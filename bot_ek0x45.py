'''
	@ Travis Drake (EklipZ) eklipz.io - tdrake0x45 at gmail)
	April 2017
	Generals.io Automated Client - https://github.com/harrischristiansen/generals-bot
	EklipZ bot - Tries to play generals lol
'''

import logging
import random
import sys
import traceback
import time
import json
import math
from base import bot_base
from base.bot_base import _create_thread
from copy import deepcopy
from collections import deque 
from queue import PriorityQueue
from pprint import pprint,pformat
from ViewInfo import ViewInfo, PathColorer
from DataModels import TreeNode, Move, PathNode
from SearchUtils import *
from dangerAnalyzer import DangerAnalyzer, ThreatType
from DataModels import get_tile_set_from_path, reverse_path, get_player_army_amount_on_path, get_tile_list_from_path
from Directives.Directives import *
from Directives.BasicPath import *
from test.test_float import INF
from Path import Path, PathMove, PathFromPathNode
from History import *
from Territory import *

GENERAL_HALF_TURN = 20000

def scale(inValue, inBottom, inTop, outBottom, outTop):
	if (inBottom > inTop):
		raise RuntimeError("inBottom > inTop")
	inValue = max(inBottom, inValue)
	inValue = min(inTop, inValue)
	numerator = (inValue - inBottom)
	divisor = (inTop - inBottom)
	if divisor == 0:
		return outTop
	valRatio = numerator / divisor
	outVal = valRatio * (outTop - outBottom) + outBottom
	return outVal

def dist(tileA, tileB):
	return abs(tileA.x - tileB.x) + abs(tileA.y - tileB.y)

def PathContains(node, x, y):
	return PathContainsCount(node, x, y) > 0


def is_gather_worthwhile(gather, parent):
	gatherWorthwhile = True
	if (parent != None):
		gatherWorthwhile = (gather.value > 0 and gather.value > parent.value / 13) or parent.fromTile == None
		#gatherWorthwhile = (gather.value > 0 and gather.value > parent.value / 20) or parent.fromTile == None
		#logging.info("{},{} <- Gather worthwhile? {} {},{}   maxGath {}  parent {}".format(parent.tile.x, parent.tile.y, gatherWorthwhile, gather.tile.x, gather.tile.y, gather.value, parent.value))
	#else:
		#logging.info("      <- No parent. True {},{}   maxGath {}".format(gather.tile.x, gather.tile.y, gather.value))
	return gatherWorthwhile


def compare_gathers(gatherA, gatherB, preferNeutrals):
	if (gatherA == None):
		return gatherB
	if (preferNeutrals and gatherA.neutrals < gatherB.neutrals):
		return gatherB
	elif (preferNeutrals and gatherA.neutrals > gatherB.neutrals):
		return gatherA
	if (gatherB.value / gatherB.gatherTurns >= gatherA.value / gatherA.gatherTurns):
		return gatherB
	return gatherA

def GetTile(Map, x, y):
	if (x < 0 or x >= Map.cols or y < 0 or y >= Map.rows):
		return None
	return Map.grid[y][x]

	
		
logging.basicConfig(format='%(message)s', level=logging.DEBUG)

######################### Move Making #########################
THREAD_COUNT = 6


class EklipZBot(object):
	def __init__(self, threadCount):
		self.general_safe_func_set = {}
		self.moveHistory = {}
		self.threadCount = threadCount
		self.threads = []
		self._bot = None
		self._map = None
		self.curPath = None
		self.curGather = None
		self.curPathPrio = -1
		self.gathers = 0
		self.attacks = 0
		self.leafMoves = []
		self.attackFailedTurn = 0
		self.countFailedQuickAttacks = 0
		self.countFailedHighDepthAttacks = 0
		self.largeTilesNearEnemyKings = {}
		self.enemyCities = []
		self.dangerAnalyzer = None
		self.lastTimingFactor = -1
		self.lastTimingTurn = 0
		self._evaluatedUndiscoveredCache = []
		self.lastTurnTime = 0

		self.allIn = False
		self.lastTargetAttackTurn = 0

		self.largeVisibleEnemyTiles = []
		self.generalApproximations = []
		self.allUndiscovered = []
		self.lastGeneralGatherTurn = -2
		self.targetPlayer = -1
		self.leafValueGrid = None
		self.failedUndiscoveredSearches = 0
		self.largePlayerTiles = []
		self.playerTargetScores = [0 for i in range(8)]
		self.ReplayId = None
		self.general = None
		self.gatherNodes = None
		self.loggingSetUp = False
		self.makingUpTileDeficit = False
		self.territories = None

		self.target_player_gather_targets = None
		self.target_player_gather_path = None

		self.viewInfo = None

		self._minAllowableArmy = -1
		self.giving_up_counter = 0
		self.all_in_counter = 0
		self.threat = None
		self.reachableTiles = set()
		self._reachableTiles = None
		self.history = History()
		self.timings = None

	def spawnWorkerThreads(self):
		return

	def detect_repetition(self, move, turns, numReps = 3):
		if move == None:
			return False
		curTurn = self._map.turn
		reps = 0
		for turn in range(int(curTurn - turns), curTurn):
			if turn in self.moveHistory:
				for oldMove in self.moveHistory[turn]:
					if oldMove != None and ((oldMove.dest == move.source and oldMove.source == move.dest) or (oldMove.source == move.source and oldMove.dest == move.dest)):
						reps += 1
						if reps == numReps:
							logging.info("  ---    YOOOOOOOOOO detected {} repetitions on {},{} -> {},{} in the last {} turns".format(reps, move.source.x, move.source.y, move.dest.x, move.dest.y, turns))
							return True
		return False

	def move_half_on_repetition(self, move, repetitionTurns, repCount = 3):
		if self.detect_repetition(move, repetitionTurns, repCount):
			move.move_half = True
		return move

	def find_move(self, allowRetry = True):
		move = self.select_move(allowRetry)
		if (self._map.turn not in self.moveHistory):
			self.moveHistory[self._map.turn] = []
		self.moveHistory[self._map.turn].append(move)
		self.viewInfo.readyToDraw = True
		return move

	def clean_up_path_before_evaluating(self):
		if self.curPath != None and self.curPath.start.next != None and not self.droppedMove(self.curPath.start.tile, self.curPath.start.next.tile):
			self.curPath.made_move()
			if self.curPath.length <= 0:
				logging.info("TERMINATING CURPATH BECAUSE <= 0 ???? Path better be over")
				self.curPath = None
			if self.curPath != None:
				if (self.curPath.start.next != None and self.curPath.start.next.next != None and self.curPath.start.next.next.next != None and self.curPath.start.tile == self.curPath.start.next.next.tile and self.curPath.start.next.tile == self.curPath.start.next.next.next.tile):
					logging.info("\n\n\n~~~~~~~~~~~\nDe-duped path\n~~~~~~~~~~~~~\n\n~~~\n")
					self.curPath.made_move()
					self.curPath.made_move()
					self.curPath.made_move()
					self.curPath.made_move()
				elif (self.curPath.start.next != None and self.curPath.start.tile.x == self.curPath.start.next.tile.x and self.curPath.start.tile.y == self.curPath.start.next.tile.y):
					logging.warning("           wtf, doubled up tiles in path?????")
					self.curPath.made_move()
					self.curPath.made_move()	
		elif self.curPath != None:
			logging.info("         --         missed move?")
		
	def droppedMove(self, fromTile = None, toTile = None, movedHalf = False):
		log = True
		lastMove = None
		if fromTile == None or toTile == None:
			if (self._map.turn - 1) in self.moveHistory:
				lastMove = self.moveHistory[self._map.turn - 1][0]
			if lastMove == None:
				if log:
					logging.info("DM: False because no last move")
				return False
			fromTile = lastMove.source
			toTile = lastMove.dest
			movedHalf = lastMove.move_half
		# easy stuff
		# if somebody else took the fromTile, then its fine.
		if fromTile.player != self.general.player:
			if log:
				logging.info("DM: False because another player captured fromTile so our move may or may not have been processed first")
			return False
		#if movedHalf:
		#	if log:
		#		logging.info("DM: False (may be wrong) because not bothering to calculate when movedHalf=True")
		#	return False
		# if army on from is what we expect
		expectedFrom = 1
		expectedToDeltaOnMiss = 0
		if self._map.turn % 50 == 0:
			expectedFrom += 1
			if toTile.player != -1:
				expectedToDeltaOnMiss += 1
		if (fromTile.isCity or fromTile.isGeneral) and self._map.turn % 2 == 0:
			expectedFrom += 1
		if ((toTile.isCity and toTile.player != -1) or toTile.isGeneral) and self._map.turn % 2 == 0:
			expectedToDeltaOnMiss += 1
		
		if (not movedHalf):
			if fromTile.army <= expectedFrom:
				if log:
					logging.info("DM: False because fromTile.army {} <= expectedFrom {}".format(fromTile.army, expectedFrom))
				return False
			else:
				if log:
					logging.info("DM: True because fromTile.army {} <= expectedFrom {}".format(fromTile.army, expectedFrom))
				return True
		else:
			if abs(toTile.delta.armyDelta) != expectedToDeltaOnMiss:
				if log:
					logging.info("DM: False because movedHalf and toTile delta {} != expectedToDeltaOnMiss {}".format(abs(toTile.delta.armyDelta), expectedToDeltaOnMiss))
				return False
			else:
				if log:
					logging.info("DM: True because movedHalf and toTile delta {} == expectedToDeltaOnMiss {}".format(abs(toTile.delta.armyDelta), expectedToDeltaOnMiss))
				return True
		
		if log:
			logging.info("DM: True because no other cases hit ???")
		return True
	
	def handle_city_found(self, tile):
		logging.info("EH: City found called! City {}".format(tile.toString()))
		self.territories.needToUpdateAroundTiles.add(tile)
		return None

	def handle_tile_captures(self, tile):
		logging.info("EH: Tile captured! Tile {}, oldOwner {} newOwner {}".format(tile.toString(), tile.delta.oldOwner, tile.delta.newOwner))
		self.territories.needToUpdateAroundTiles.add(tile)
		return None

	def handle_tile_deltas(self, tile):
		logging.info("EH: Tile delta handler! Tile {} delta {}".format(tile.toString(), tile.delta.armyDelta))
		return None

	def handle_tile_discovered(self, tile):
		logging.info("EH: Tile discovered handler! Tile {}".format(tile.toString()))
		self.territories.needToUpdateAroundTiles.add(tile)
		return None

	def handle_tile_revealed(self, tile):
		logging.info("EH: Tile revealed handler! Tile {}".format(tile.toString()))
		self.territories.needToUpdateAroundTiles.add(tile)
		return None


	def init_turn(self):
		timeSinceLastUpdate = 0
		now = time.time()
		if self.lastTurnTime != 0:
			timeSinceLastUpdate = now - self.lastTurnTime
		self.lastTurnTime = now
		logging.info("\n       ~~~\n       Turn {}   ({:.3f})\n       ~~~\n".format(self._map.turn, timeSinceLastUpdate))
		if self.general == None:
			self.general = self._map.generals[self._map.player_index]
		self._minAllowableArmy = -1
		self._gen_distances = None
		self.enemyCities = []
		if self._map.turn - 3 > self.lastTimingTurn:
			self.lastTimingFactor = -1

		if (not self.loggingSetUp and self._bot != None):
			self.dangerAnalyzer = DangerAnalyzer(self._map)
			self.viewInfo =  ViewInfo(6, self._map.cols, self._map.rows)
			self.ReplayId = self._bot._game._start_data['replay_id']
			self.loggingSetUp = True
			print("replay " + self.ReplayId)
			file = 'H:\\GeneralsLogs\\' + self.ReplayId + '.log'
			print("file: " + file)
			logging.basicConfig(format='%(levelname)s:%(message)s', filename="H:\\GeneralsLogs\\test.txt", level=logging.DEBUG)
			self._map.ekBot = self
			self._map.notify_city_found.append(self.handle_city_found)
			self._map.notify_tile_captures.append(self.handle_tile_captures)
			self._map.notify_tile_deltas.append(self.handle_tile_deltas)
			self._map.notify_tile_discovered.append(self.handle_tile_discovered)
			self._map.notify_tile_revealed.append(self.handle_tile_revealed)

		if self.territories == None:
			self.territories = TerritoryClassifier(self._map)
		if self.territories.should_recalculate(self._map.turn):
			self.territories.scan()



	def get_timings(self):
		# what size cycle to use, normally the 50 turn cycle
		cycleDuration = 50

		# at what point in the cycle to split from gather to utility moves. TODO dynamically determine this based on available utility moves?
		split = 19

		# offset so that this timing doesn't always sync up with every 100 moves, instead could sync up with 250, 350 instead of 300, 400 etc.
		# for cycle 50 this is always 0

		genPlayer = self._map.players[self.general.player]
		if self.allIn:
			cycleDuration = 100
			split = 75
		elif genPlayer.tileCount > 150:
			cycleDuration = 100
			split = 60
		elif genPlayer.tileCount > 90:
			# slightly longer split
			split = 28
		elif genPlayer.tileCount > 65:
			# slightly longer split
			split = 26
		elif genPlayer.tileCount > 45:
			# slightly longer split
			split = 23
		elif genPlayer.tileCount > 30:
			# slightly longer split
			split = 21
		offset = self._map.turn % cycleDuration
		if offset % 50 != 0:
			# When this gets set on random turns, if we don't set it to 0 it will always keep recycling on that offkilter turn.
			offset = 0
		timings = Timings(cycleDuration, split, offset)
		logging.info("Recalculated timings. Timings {}".format(timings.toString()))
		return timings


	def timing_expand(self):
		turnOffset = self._map.turn + self.timings.offsetTurns
		turnCycleOffset = turnOffset % self.timings.cycleTurns
		if (turnCycleOffset >= self.timings.splitTurns):
			return None
		return None


	def timing_gather(self, startTiles, negativeTiles = None, skipTiles = None):
		turnOffset = self._map.turn + self.timings.offsetTurns
		turnCycleOffset = turnOffset % self.timings.cycleTurns
		if (self._map.turn >= 50 and turnCycleOffset < self.timings.splitTurns and startTiles != None and len(startTiles) > 0):
			logging.info("Inside gather timing window. Timings: {}".format(self.timings.toString()))
			depth = (self.timings.splitTurns) - turnCycleOffset
			skipFunc = None
			if self._map.remainingPlayers > 2:
				# avoid gathering to undiscovered tiles when there are third parties on the map
				skipFunc = lambda tile, tilePriorityObject: not tile.discovered
			self.gatherNodes = greedy_backpack_gather(self._map, startTiles, depth, negativeTiles = negativeTiles, searchingPlayer = self.general.player, skipFunc = skipFunc, viewInfo = self.viewInfo, skipTiles = skipTiles)
			move = self.get_tree_move_default(self.gatherNodes)
			if (move != None):
				self.info("timing_gather? {}".format(move.toString()))
				return self.move_half_on_repetition(move, 6, 4)
			else:
				logging.info("NO MOVE WAS RETURNED FOR timing_gather?????????????????????")
		else:
			logging.info("No timing move because outside gather timing window. Timings: {}".format(self.timings.toString()))



	def make_first_25_move(self):
		# PLAN
		# below, count wasted moves somehow to determine how many path crossings are allowed
		# maximize empty tiles near general
		# Build longest path
		# Build second path that traverses longest path 1 or 2 moves
		# Build third path
		# build fourth path
		# build fifth path

		path = self.get_optimal_expansion(51 - self._map.turn)
		#is1v1 = self._map.remainingPlayers == 2
		#gatherNodes = self.build_mst([self.general])
		#self.gatherNodes = gatherNodes

		if (self._map.turn < 46 and self.general.army < 3 
			and self._map.players[self.general.player].standingArmy + 1 == self.general.army 
			and count(self.general.adjacents, lambda tile: tile.player == -1) > 0):
			self.info("Skipping move because general.army < 3 and all army on general and self._map.turn < 46")
			# dont send 2 army except right before the bonus, making perfect first 25 much more likely
			return None
		move = None
		if path:
			self.info("Dont make me expand. You don't want to see me when I'm expanding.")
			move = Move(path.start.tile, path.start.next.tile)
		return move


	def select_move(self, allowRetry = True):
		start = time.time()
		self.init_turn()
		if allowRetry:
			self.viewInfo.turnInc()
		if self.timings == None or self.timings.should_recalculate(self._map.turn):
			logging.info("recalculating timings...")
			self.timings = self.get_timings()

		# This is the attempt to resolve the 'dropped packets devolve into unresponsive bot making random moves
		# even though it thinks it is making sane moves' issue. If we seem to have dropped a move, clear moves on
        # the server before sending more moves to prevent moves from backing up and getting executed later.
		if (self._map.turn - 1 in self.moveHistory):
			if self.droppedMove():
				logging.info("\n\n\n^^^^^^^^^VVVVVVVVVVVVVVVVV^^^^^^^^^^^^^VVVVVVVVV^^^^^^^^^^^^^\nD R O P P E D   M O V E ? ? ? ? Sending clear_moves...\n^^^^^^^^^VVVVVVVVVVVVVVVVV^^^^^^^^^^^^^VVVVVVVVV^^^^^^^^^^^^^")
				self._bot._game.send_clear_moves()
		#if (self.turnsTillDeath > 0):
		#	self.turnsTillDeath -= 1
			#logging.info("\n\n---------TURNS TILL DEATH AT MOVE START {}\n".format(self.turnsTillDeath))
		if self._map.turn <= 1:
			# bypass divide by 0 error instead of fixing it
			return None
		self.scan_map()
		general = self.general


		
		allLeaves = self.leafMoves
		
		reevaluate = False
		if len(self._evaluatedUndiscoveredCache) > 0:
			for tile in self._evaluatedUndiscoveredCache:
				if tile.discovered:
					reevaluate = True
		
		if (self.target_player_gather_path == None 
					or reevaluate
					or self.target_player_gather_path.tail.tile.isCity
					or (self._map.turn % 50 < 2)
					or (not self.target_player_gather_path.tail.tile.isGeneral and self._map.generals[self.targetPlayer] != None
					or self.curPath == None)):
			self.target_player_gather_path = self.get_path_to_target_player(skipEnemyCities = self.allIn)
			self.target_player_gather_targets = self.target_player_gather_path.tileSet

			
		if (self._map.turn < 50):
			move = self.make_first_25_move()
			if (self._map.turn < 24):
				return None
			if move != None:
				return move
			if (self._map.turn < 46 and self.general.army < 3 
					and self._map.players[self.general.player].standingArmy + 1 == self.general.army 
					and count(self.general.adjacents, lambda tile: tile.player == -1) > 0):
				# dont send 2 army except right before the bonus, making perfect first 25 much more likely
				return None
		# Dont re-evaluate attack path except at the beginning of the army bonus round
		#if (self.target_player_gather_path == None 
		#		or (self._map.turn % 50 < 2) 
		#		or self.target_player_gather_path.tail.tile.discovered 
		#		or self.target_player_gather_path.length < 3
		#		or (not self.target_player_gather_path.tail.tile.isGeneral and self._map.generals[self.targetPlayer] != None)
		#		or self.curPath == None):
		#	self.target_player_gather_path = self.get_path_to_target_player(skipEnemyCities = self.allIn)			
		#	self.target_player_gather_targets = self.target_player_gather_path.tileSet

		targets = self.target_player_gather_targets
		if self.target_player_gather_path != None:
			alpha = 160
			minAlpha = 100
			alphaDec = 0
			self.viewInfo.paths.appendleft(PathColorer(self.target_player_gather_path, 60, 50, 00, alpha, alphaDec, minAlpha))
		


		self.clean_up_path_before_evaluating()


		if (self.curPathPrio >= 0):
			logging.info("curPathPrio: " + str(self.curPathPrio))

		self.calculate_general_danger()


		turnsTillDanger = -1 
		threat = None
		visionThreat = None
		minAllowable = self.general_min_army_allowable()
		if not self.giving_up_counter > 30:
			if (self.dangerAnalyzer.fastestVisionThreat != None):
				threat = self.dangerAnalyzer.fastestVisionThreat
				visionThreat = self.dangerAnalyzer.fastestVisionThreat
				turnsTillDanger = threat.turns

			if (self.dangerAnalyzer.fastestThreat != None):
				threat = self.dangerAnalyzer.fastestThreat
				turnsTillDanger = threat.turns

		#  # # # #   ENEMY KING KILLS
		# due to enemy_army_near_king logic, need to explicitly check for 1-tile-kills that we might win on luck
		for enemyGeneral in self._map.generals:
			if not (enemyGeneral != None and enemyGeneral.player != self.general.player):
				continue
			for adj in enemyGeneral.moveable:
				if adj.player == self.general.player and adj.army - 1 > enemyGeneral.army:
					logging.info("Adjacent kill on general lul :^) {},{}".format(enemyGeneral.x, enemyGeneral.y))
					return Move(adj, enemyGeneral)

			
		# SEARCH FOR BFS KILL ON ENEMY KING
		negativeTiles = set()
		if (len(self.largeTilesNearEnemyKings.keys()) > 0):
			for enemyGeneral in self._map.generals:
				if not (enemyGeneral != None and enemyGeneral.player != self.general.player and enemyGeneral.player not in self._map.teammates):
					continue
				targetArmy = 0
				for depth in range (1, 6):
					# TODO instead use enemies highest defense of length depth - 1
					targetArmy = self.enemy_army_near(enemyGeneral, max(depth - 2, 0))
					killPath = dest_breadth_first_target(self._map, [enemyGeneral], max(targetArmy, 1), 0.05, depth, None, self.general.player, False, 4, noLog = True)
					if (killPath != None and killPath.length > 0) and (threat == None or (turnsTillDanger > killPath.length)):
						logging.info("DEST BFS K found kill path length {} :^)".format(killPath.length))
						self.curPath = killPath
						self.curPathPrio = 5
						move = Move(killPath.start.tile, killPath.start.next.tile)
						if self.is_move_safe_valid(move):
							self.viewInfo.infoText = "Killpath against general length {}".format(killPath.length)
							return move
				# uses targetArmy from depth 6 above
				killPath = dest_breadth_first_target(self._map, [enemyGeneral], targetArmy, 0.05, len(self.target_player_gather_targets) / 2, None, self.general.player, False, 4)
				if (killPath != None and killPath.length >= 0) and (threat == None or (turnsTillDanger > killPath.length)):
					logging.info("DEST BFS K found kill path length {} :^)".format(killPath.length))
					self.curPath = killPath
					self.curPathPrio = 5
					move = Move(killPath.start.tile, killPath.start.next.tile)
					if self.is_move_safe_valid(move):
						self.viewInfo.infoText = "Killpath against general length {}".format(killPath.length)
						return move


		for king in self.largeTilesNearEnemyKings.keys():
			if king.player in self._map.teammates:
				continue
			tiles = self.largeTilesNearEnemyKings[king]
			furtherTiles = []
			if (len(tiles) > 0):	
				logging.info("Attempting to find kill path against general {} ({},{})".format(king.player, king.x, king.y))
				bestTurn = 1000
				bestPath = None
				for tile in tiles:
					if self.distance_from_general(tile) < 10:
						path = a_star_kill(self._map, [tile], king, 0.02, len(self.target_player_gather_targets) / 2, self.general_safe_func_set)
						
						if (path != None and path.length >= 0) and (threat == None or (turnsTillDanger > path.length and threat.threatPlayer == king.player)):
							logging.info("A_STAR found kill path length {} :^)".format(path.length))
							self.curPath = path
							self.curPathPrio = 5
							if (path.length < bestTurn):
								bestPath = path
								bestTurn = path.length
					else:
						furtherTiles.append(tile)
				if (bestPath != None):
					self.viewInfo.infoText = "A* Killpath {},{} length {}".format(king.x, king.y, bestPath.length)
					self.viewInfo.lastEvaluatedGrid[king.x][king.y] = 200
					return Move(bestPath.start.tile, bestPath.start.next.tile)
				#path = a_star_kill(self._map, furtherTiles, king, 0.03, 30, self.general_safe_func_set)
				#if (path != None and path.length >= 0) and (threat == None or (turnsTillDanger > path.length and threat.threatPlayer == king.player)):
				#	logging.info("Found kill path length {} :^)".format(path.length))
				#	self.curPath = path
				#	self.curPathPrio = 5
				#	return Move(path.tile, path.parent.tile)
		
				
		self.threat = threat
		if threat != None and threat.saveTile != None:
			self.viewInfo.lastEvaluatedGrid[threat.saveTile.x][threat.saveTile.y] = 200
		paths = []


		enemyNearGen = self.enemy_army_near(general)
		genArmyWeighted = general.army - enemyNearGen
		genLowArmy = self.general_min_army_allowable() / 2 > genArmyWeighted and self._map.remainingPlayers <= 3
		if (genLowArmy):
			logging.info("gen low army")

		if self.allIn:
			logging.info("~~~ ___\n   YO WE ALL IN DAWG\n~~~ ___")
		#if (genLowArmy) or (turnsTillDanger > -1 and (self.danger[3] or self.curPathPrio < 10) and (self.curPathPrio < 100 or self.turnsTillDeath != turnsTillDanger)):
		# if (genLowArmy) or (turnsTillDanger > -1 and (self.danger[3] or self.curPathPrio < 10) and (self.turnsTillDeath <= 0 or self.turnsTillDeath >= turnsTillDanger)):
		
		#if not self.allIn and (turnsTillDanger > -1 and self.dangerAnalyzer.anyThreat):
		#	armyAmount = (self.general_min_army_allowable() + enemyNearGen) * 1.1 if threat == None else threat.threatValue + general.army + 1

		if threat != None and not self.allIn and (turnsTillDanger > -1 and self.dangerAnalyzer.anyThreat):
			# DEFEND THREAT
			searchTurns = turnsTillDanger
			move = self.get_threat_killer_move(threat, searchTurns, negativeTiles)
			if move != None:
				self.viewInfo.infoText = "threat killer move! {},{} -> {},{}".format(move.source.x, move.source.y, move.dest.x, move.dest.y)
				if self.curPath != None and move.source.tile == self.curPath.start.tile:
					self.curPath.add_start(move.dest.tile)
					self.viewInfo.infoText = "threat killer move {},{} -> {},{} WITH ADDED FUN TO GET PATH BACK ON TRACK!".format(move.source.x, move.source.y, move.dest.x, move.dest.y)
				return self.move_half_on_repetition(move, 5, 4)
			armyAmount = threat.threatValue + 1
			logging.info("\n!-!-!-!-!-!  general in danger in {}, gather {} to general in {} turns  !-!-!-!-!-!".format(turnsTillDanger, armyAmount, searchTurns))

			self.viewInfo.addSearched(general)
			gatherPaths = []
			#for tile in self.largeVisibleEnemyTiles:
			#	negativeTiles.add(tile)
			if (threat != None and threat.threatType == ThreatType.Kill):

				targetTile = None
				dict = {}
				dict[general] = (0, threat.threatValue)
				negativeTilesIncludingThreat = set()
				for tile in negativeTiles:
					negativeTilesIncludingThreat.add(tile)
				for tile in threat.path.tileSet:
					negativeTilesIncludingThreat.add(tile)
				if threat.saveTile != None:
					dict[threat.saveTile] = (0, threat.threatValue)
					self.viewInfo.addSearched(threat.saveTile)
					logging.info("dict[threat.saveTile] = (0, {})  -- threat.saveTile {},{}".format(threat.saveTile.army, threat.saveTile.x, threat.saveTile.y))

				## oh god, attempt gather defense
				
				#logging.info("\n\nPREPARING GENERAL DEFENSE WITH BACKPACK")
				#threatDict = threat.path.convert_to_dist_dict()
				#offset = 0
				## if theres a saveTile then we have an extra turn to gather everywhere but our general
				#if threat.saveTile:
				#	offset = 1
				#for tile in threatDict.keys():
				#	dist = threatDict[tile] + offset
				#	threatDict[tile] = ((0, 0, 0, dist, tile.x, tile.y), 0)
				#	logging.info("tile {} set to dist {}".format(tile.toString(), dist))
				## general doesn't get to gather an extra turn
				#logging.info("GENERAL tile {} set to dist {}".format(self.general.toString(), threat.turns))
				#threatDict[self.general] = ((0, 0, 0, threat.turns, self.general.x, self.general.y), 0)

				#self.gatherNodes = greedy_backpack_gather(self._map, threatDict, threat.turns, negativeTiles = negativeTiles, searchingPlayer = self.general.player, viewInfo = self.viewInfo)
				#move = self.get_tree_move_default(self.gatherNodes)
				#if (move != None):
				#	self.info("Oh, shit, greedy-backpack-gather defense???? {},{} -> {}, {}".format(move.source.x, move.source.y, move.dest.x, move.dest.y))
				#	return self.move_half_on_repetition(move, 8, 5)
				#else:
				#	self.info("Huh, general backpack defense didn't return anything? :/")

				path = dest_breadth_first_target(self._map, dict, armyAmount, 0.1, searchTurns, negativeTilesIncludingThreat, ignoreGoalArmy=True)
				if (path != None and path.length > 0):
					logging.info("            DEST BFS TARGET to save king, \n               turn {}, value {} : {}".format(path.length, path.value, path.toString()))
					gatherPaths.append(path)
				else:
					#    old WBS defense
					#logging.info("a\naa\n  aa OH NO DEST BFS COULDN'T FIND SAVE-PATH. Trying weighted breadth at searchTurns+1")
					#gatherPaths = self.WeightedBreadthSearch([general], max(1, searchTurns + 1), 0.12, general.player, armyAmount + self.general.army, 200, negativeTilesIncludingThreat)
					## Because weighted doesn't ignore goal army like the above search does.
					#for path in gatherPaths:
					#	genIncTurns = max(path.length, threat.turns)
					#	path.value -= self.general.army + genIncTurns / 2

					
					logging.info("\n\n!-!-!-!-!-! \nIt may be too late to save general, setting their general val to 1 and also attempting backpack defense\n!-!-!-!-!-!")
					targetGen = self._map.generals[threat.threatPlayer]
					if targetGen != None and not targetGen.visible:
						targetGen.army = 1
				
					logging.info("\n\nPREPARING GENERAL DEFENSE WITH BACKPACK")
					defenseTiles = [self.general]
					if threat.saveTile:
						defenseTiles.append(threat.saveTile)

					# also include large tiles adjacent to the threat path
					# crappy hack to replace proper backpack defense
					defenseNegatives = set(threat.path.tileSet)
					#player = self._map.players[self.general.player]
					#negativeTileThresh = player.score // 20
					#for tile in threat.path.tileList:
					#	if tile != self.general and tile != threat.path.start.tile:
					#		for adjTile in tile.moveable:
					#			if adjTile not in defenseNegatives and adjTile.player == self.general.player and adjTile.army > negativeTileThresh:
					#				logging.info("adding {} with army {} > negativeTileThresh {} to gatherNegatives because next to threatPath".format(adjTile.toString(), adjTile.army, negativeTileThresh))
					#				defenseNegatives.add(adjTile)


					move = self.gather_to_target_tiles(defenseTiles, 0.2, threat.turns, None, defenseNegatives, threat.threatValue)
					if move:
						self.curPath = None
						self.info("lol backpack defense to defenseTiles only... {}".format(move.toString()))
						return move

					# TODO backpack properly to threat path
					#threatDict = threat.path.convert_to_dist_dict()
					#offset = 0
					## if theres a saveTile then we have an extra turn to gather everywhere but our general
					#if threat.saveTile:
					#	offset = 1
					#for tile in threatDict.keys():
					#	dist = threatDict[tile] + offset
					#	threatDict[tile] = ((0, 0, 0, dist, tile.x, tile.y), 0)
					#	logging.info("tile {} set to dist {}".format(tile.toString(), dist))
					## general doesn't get to gather an extra turn
					#logging.info("GENERAL tile {} set to dist {}".format(self.general.toString(), threat.turns))
					#threatDict[self.general] = ((0, 0, 0, threat.turns, self.general.x, self.general.y), 0)

					#self.gatherNodes = greedy_backpack_gather(self._map, threatDict, threat.turns, negativeTiles = negativeTiles, searchingPlayer = self.general.player, viewInfo = self.viewInfo)
					#move = self.get_tree_move_default(self.gatherNodes)
					#if (move != None):
					#	self.info("Oh, shit, greedy-backpack-gather defense???? {},{} -> {}, {}".format(move.source.x, move.source.y, move.dest.x, move.dest.y))
					#	return self.move_half_on_repetition(move, 8, 5)
					#else:
					#	self.info("Huh, general backpack defense didn't return anything? :/")
			elif visionThreat != None and not self.allIn:
				if visionThreat.turns < 2:
					logging.info("\n\n!-!-!-!-!-! \n     !!  VISION THREAT 1 !! \n!-!-!-!-!-!")
					target = visionThreat.path.start.next.tile
					if target in general.moveable and self.general_move_safe(target):
						self.viewInfo.infoText = "Vision threat general move"
						return Move(general, target)
				logging.info("\n\n!-!-!-!-!-! \n         WHEE WHOO WHEE WHOO\n       WE GATHERIN NOW, VISION THREAT\n!-!-!-!-!-!")
				threatTiles = []
				dangerPathNode = visionThreat.path.start
				i = 0
				while dangerPathNode != None:
					threatTiles.append(dangerPathNode.tile)
					#if i >= (visionThreat.turns / 2 - 1):
					#	threatTiles.append(dangerPath.move.source)
					#	logging.info("will be gathering to {},{} while trying to stop vision threat".format(dangerPath.move.source.x, dangerPath.move.source.y))
					dangerPathNode = dangerPathNode.next
				self.gatherNodes = self.build_mst(threatTiles, 1.0, visionThreat.turns / 2, None, set([general]))
				
				move = self.get_gather_move(self.gatherNodes, None, allowNonKill = True)
				if (move != None):
					self.viewInfo.infoText = "gathering to vision threat????"
					return self.move_half_on_repetition(move, visionThreat.turns, 4)
				# if self._map.turn % 3 > 0:
				# 	for tile in self.largePlayerTiles:
				# 		negativeTiles.add(tile)
				# gatherPaths = self.WeightedBreadthSearch(destinations, max(1, searchTurns + 1), 0.12, general.player, -1, 200, negativeTiles)



			queue = PriorityQueue()
			queueShortest = PriorityQueue()
			for path in gatherPaths:
				#  - path.length / 2 because of general increment

				gatherVal = (path.value)
				# i think this works including for meeting up to attack path earlier?
				lengthModifier = min(0, 1 - self.distance_from_general(path.tail.tile))
				lengthModified = path.length + lengthModifier
				if threat != None:
					# If its a real threat, sort by shortest path
					logging.info("Looking for short save paths... lengthModifier {}, searchTurns {}, threatValue {}, gatherVal {}, path {}".format(lengthModifier, searchTurns, threat.threatValue, gatherVal, path.toString()))
					if (gatherVal >= threat.threatValue):
						logging.info("gatherVal [{}] >= threat.threatValue [{}]".format(gatherVal, threat.threatValue))
						if path.length + lengthModifier < searchTurns:
							logging.info("path.length + lengthModifier [{}] < searchTurns [{}] SHORTEST ADD".format(path.length + lengthModifier, searchTurns))
							queueShortest.put((0 - (path.length + lengthModifier), 0 - path.value, path))
						else:
							logging.info("NOT path.length + lengthModifier [{}] < searchTurns [{}]".format(path.length + lengthModifier, searchTurns))
					else:
						logging.info("NOT gatherVal [{}] >= threat.threatValue [{}]".format(gatherVal, threat.threatValue))

				if (gatherVal > 0 and path.length >= 1):
					pathVal = gatherVal / 1.5 + gatherVal / lengthModified
					if lengthModified > searchTurns:
						pathVal = (pathVal / 100.0 - 1.0) / lengthModified
					queue.put((0 - pathVal, path))
			



			if (not queueShortest.empty()):
				(negTurn, negPathVal, savePath) = queueShortest.get()
				logging.info("SAFE: SHORT path to save king. Length {}, value {} : {}".format(savePath.length, savePath.value, savePath.toString()))
				paths = []
				alpha = 120
				minAlpha = 80
				alphaDec = 6
				self.viewInfo.paths.appendleft(PathColorer(savePath.clone(), 230, 220, 190, alpha, alphaDec, minAlpha))
				saveNode = savePath.start
				# mark all nodes on the savepath as negative tiles?
				if (savePath.length > searchTurns - 2):
					logging.info("SuperSafe: (savePath.length [{}] > searchTurns - 2 [{}]), Adding savepath to negative tiles.".format(savePath.length, searchTurns - 2))
					while saveNode != None:
						negativeTiles.add(saveNode.tile)
						saveNode = saveNode.next
				
			
			else:				
				while not queue.empty() and len(paths) < 5:
					node = queue.get()
					path = node[1]
					paths.append(path)
					self.info("GHETTO QUEUE path to save king, ({}) turn {}, value {} : {}".format(node[0], path.length, path.value, path.toString()))
					
			if threat != None:
				threatKill = self.kill_threat(threat)
				if threatKill:
					logging.info("Threat kill WOULD HAVE BEEN {}".format(threatKill.toString()))

			if (len(paths) > 0): 
				self.lastGeneralGatherTurn = self._map.turn
				#if (threat != None and threat.threatType == ThreatType.Kill):
				#	self.curPathPrio = 100
				#else:
				#	self.curPathPrio = 10
				savePath = paths[0]
				end = time.time()
				logging.info("GEN GATHERING.... Time calculating defensive gather to general: {}".format(end - start))
				depth = 3
				node = savePath.start
				while node != None and depth > 0:
					node = node.next
					depth -= 1
				self.info("setting curpath to save general. " + savePath.toString())
				if (savePath.start.tile.army == 1):
					self.info("set curpath to save general AND HIT INC 0.5 BUG! " + savePath.toString())
					# then hit that bug where the general was saved by 0.5 increment, lul, and he's trying to move 0 army
					savePath.made_move()
				if savePath.start.next != None:
					savePath = savePath.get_subsegment(2)
					self.curPath = savePath
					self.info("set curpath to save general (single move) {}" + savePath.toString())
					return Move(savePath.start.tile, savePath.start.next.tile)
				else:
					self.info("COULDNT SAVE GENERAL AND HIT INC 0.5 BUG I THINK!" + savePath.toString())
				
			end = time.time()
			logging.info("Time calculating defensive gather to general: {}".format(end - start))
		####    CITY RECAP
		####
		####
		
		# if ahead on economy, but not %30 ahead on army we should play defensively
		defendEconomy = False
		if self._map.turn >= 100:
			econRatio = -0.15
			armyRatio = -0.3
			winningEcon = self.winning_on_economy(econRatio, 20)
			winningArmy = self.winning_on_army(armyRatio)
			defendEconomy = winningEcon and not winningArmy
			if defendEconomy:
				logging.info("\n\nDEFENDING ECONOMY! self.winning_on_economy({}) {}, self.winning_on_army({}) {}".format(econRatio, winningEcon, armyRatio, winningArmy))
			else:
				logging.info("\n\nNOT DEFENDING ECONOMY? self.winning_on_economy({}) {}, self.winning_on_army({}) {}".format(econRatio, winningEcon, armyRatio, winningArmy))


		dangerTiles = self.get_danger_tiles()
		if (len(dangerTiles) > 0 and not self.allIn):
			logging.info("trying to kill danger tiles")
			for tile in dangerTiles:
				self.viewInfo.addSearched(tile)
				armyToSearch = self.get_target_army_inc_adjacent_enemy(tile)
				killPath = dest_breadth_first_target(self._map, [tile], armyToSearch, 0.1, 10, None, dontEvacCities=False)
				if (killPath != None):
					self.info("found depth {} dest bfs kill on danger tile {},{} \n{}".format(killPath.length, tile.x, tile.y, killPath.toString()))
					self.curPath = killPath
				#else:
				#	self.gatherNodes = self.build_mst(dangerTiles, 1.0, 10, None, set([general]))
				#	move = self.get_gather_move(self.gatherNodes, None)
				#	if (move != None):
				#		self.info("gathering to danger tile??? {},{}".format(tile.x, tile.y))
				#		return self.move_half_on_repetition(move, 4, 2)


		#if not (len(paths) > 0) and (not (self.danger != None and self.danger[3]) and (self.curPath == None or self.curPath.start.next == None or self.curPathPrio <= 0)):
		# if len(paths) == 0 and (self.curPath == None or self.curPath.start.next == None) and not self._map.turn % 20 == 1: 


		gatherTargets = self.target_player_gather_path.tileList
		if not self.allIn and (len(paths) == 0):
			# TODO REDUCE CITYDEPTHSEARCH NOW THAT WE HAVE CITY FIGHTING BASIC IMPL
			cityDepthSearch = int(self._map.players[self.general.player].tileCount**0.5 / 2)
			#if (len(self.enemyCities) > 5):
			#	cityDepthSearch = 5
			for enemyCity in self.enemyCities:
				logging.info("searching for depth {} dest bfs kill on city {},{}".format(cityDepthSearch, enemyCity.x, enemyCity.y))
				self.viewInfo.addSearched(enemyCity)
				armyToSearch = self.get_target_army_inc_adjacent_enemy(enemyCity)
				killPath = dest_breadth_first_target(self._map, [enemyCity], armyToSearch, 0.1, cityDepthSearch, negativeTiles, dontEvacCities=True)
				if (killPath != None):
					self.info("found depth {} dest bfs kill on city {},{} \n{}".format(killPath.length, enemyCity.x, enemyCity.y, killPath.toString()))
					if (killPath.start.tile.isCity):
						killPath.move_half = True
					paths.append(killPath)
			(cityPath, gatherMove) = self.capture_cities(targets, negativeTiles)
			if cityPath != None:
				logging.info("returning capture_cities cityPath {}".format(cityPath.toString()))
				paths.append(cityPath)
			elif gatherMove != None:
				logging.info("returning capture_cities gatherMove {}".format(gatherMove.toString()))
				return gatherMove
			
		undiscNeg = negativeTiles.copy()				
		for city in self._map.players[self.general.player].cities:
			undiscNeg.add(city)
		halfTargetPath = self.target_player_gather_path.get_subsegment(self.target_player_gather_path.length / 2)
		undiscNeg.add(self.general)
		for tile in halfTargetPath.tileList:
			undiscNeg.add(tile)
		path = self.explore_target_player_undiscovered(undiscNeg, 20)	
		if (path != None):
			pruned = self.get_value_per_turn_subsegment(path, 0.9)
			self.info("LARGE: found depth {} dest bfs kill on target undisc (pruned to {})\n{}".format(path.length, pruned.length, path.toString()))
			paths.append(pruned)
			

				
		if len(paths) == 0 and (self.curPath == None or self.curPath.start.next == None) and self._map.turn >= 50:
			path = self.get_value_per_turn_subsegment(self.target_player_gather_path)
			# reduce the length of the path to allow for other use of the army
			path = path.get_subsegment(path.length * 6 / 7 + 1)
			path.calculate_value(self.general.player)
			logging.info("value subsegment = {}".format(path.toString()))
			timingTurn = (self._map.turn + self.timings.offsetTurns) % self.timings.cycleTurns
			if timingTurn >= self.timings.splitTurns:
				expStartTime = time.time()
				inAttackWindow = timingTurn < self.timings.splitTurns + path.length
				self.info("Inside +split if. path.value {}, timingTurn {} < self.timings.splitTurns + path.length {}: {}".format(path.value, timingTurn, self.timings.splitTurns + path.length, inAttackWindow))
				if path != None and path.value > 5 and inAttackWindow:
					# Then it is worth launching the attack?
					paths.append(path)
					logging.info("attacking because NEW worth_attacking_target(), {}".format(path.toString()))
					self.lastTargetAttackTurn = self._map.turn
					#return self.move_half_on_repetition(Move(path[1].tile, path[1].parent.tile, path[1].move_half), 7, 3)
					self.curPath = path
				elif path != None:
					logging.info("Did NOT attack because NOT new worth_attacking_target()??? {}".format(path.toString()))

				#if len(paths) == 0 and (self.curPath == None or self.curPath.start.next == None) and self.worth_attacking_target():
				#	logging.info("Inside worth_attacking_target if")
				#	path = self.get_value_per_turn_subsegment(self.target_player_gather_path)

				#	notTooLate = (self._map.turn + self.timings.offsetTurns) % self.timings.cycleTurns + (path.length) < self.timings.cycleTurns
				#	logging.info("Worth attacking but is timing too late for attacking target? {}".format(not notTooLate))
				#	logging.info("(self._map.turn {} + self.timings.offsetTurns {}) % self.timings.cycleTurns {} + (path.length {}) < self.timings.cycleTurns {}".format(self._map.turn, self.timings.offsetTurns, self.timings.cycleTurns, path.length, self.timings.cycleTurns))
				#	if notTooLate:
				#		logging.info("\n\nOOOOOOOOOOOOMG launching attack\n\n")
				#		#paths.append(path)
				#		if path != None:
				#			paths.append(path)
				#			self.info("attacking because self.worth_attacking_target(), {}".format(path.toString()))
				#			self.lastTargetAttackTurn = self._map.turn
				#			#return self.move_half_on_repetition(Move(path[1].tile, path[1].parent.tile, path[1].move_half), 7, 3)
				#			self.curPath = path
				#		else:
				#			logging.info("WTF PATH WAS NONEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEE")
				#	else:
				#		logging.info("Skipped launching attack because not enough time to fully utilize the army")
				#else:
				#	logging.info("Not worth attacking target")
				if len(paths) == 0:
					undiscNeg = negativeTiles.copy()				
					for city in self._map.players[self.general.player].cities:
						undiscNeg.add(city)
					undiscNeg.add(self.general)
					path = self.explore_target_player_undiscovered(undiscNeg)	
					if (path != None):
						self.info("found depth {} dest bfs kill on target undisc\n{}".format(path.length, path.toString()))
						paths.append(path)
			
				if len(paths) == 0 and not self.all_in_counter > 50 and not defendEconomy:
					# no timing gather move, optimal expand?
					path = self.get_optimal_expansion(1 + self.timings.cycleTurns - (self._map.turn + self.timings.offsetTurns) % self.timings.cycleTurns, negativeTiles)
					if path:
						move = Move(path.start.tile, path.start.next.tile)
						self.info("oh shit, we're using new expansion? {} Duration {:.3f}".format(move.toString(), time.time() - expStartTime))
						return move
					else:
						logging.info("No path found for optimal expansion??? Duration {:.3f}".format(time.time() - expStartTime))
				else:
					logging.info("skipping optimal expansion because len(paths) {} or self.all_in_counter {} or defendEconomy {}".format(len(paths), self.all_in_counter, defendEconomy))
			else:
				logging.info("skipped optimal expand and worth_attacking_target because not outside +split window")
			largestEnemyAdj = None
			sumAdj = 0
			armyToGather = self.get_target_army_inc_adjacent_enemy(self.general)
			enemyGenAdj = []
			for generalAdj in self.general.adjacents:
				if (generalAdj.player != self._map.player_index and generalAdj.player != -1):
					self.viewInfo.addSearched(generalAdj)
					enemyGenAdj.append(generalAdj)
			if not self.allIn and len(enemyGenAdj) > 0:
				logging.info("KILLING GENERAL VISION TILES searching for dest bfs kill")
				largest = max(enemyGenAdj, key=lambda tile: tile.army)
				killPath = dest_breadth_first_target(self._map, [largest], armyToGather, 0.2, 11)
				if (killPath != None):
					self.info("found depth {} dest bfs kill on general vision tile: {}".format(killPath.length, killPath.toString()))
					paths.append(killPath)

				#Gather to threat
				#if (self.threat != None and threat.threatPlayer == self.targetPlayer and self.curPath == None):
				#	threatNextTile = self.threat.path.start.next.tile
				#	move = self.gather_to_target_tile(threatNextTile, 0.1, self.threat.turns)
				#	if (self.is_move_safe_valid(move)):
				#		logging.info("////////// Gathering to threat {},{}: {},{} -> {},{}".format(threatNextTile.x, threatNextTile.y, move.source.x, move.source.y, move.dest.x, move.dest.y))
				#		return move
			if not self.allIn and (len(paths) == 0):
				for city in self._map.players[self.general.player].cities:
					if (city.player == -1):
						continue
					largestEnemyAdj = None
					sumAdj = 0
					enemyAdjCount = 0
					friendlyAdjCount = 0
					for cityAdj in city.adjacents:
						if (cityAdj.player == self._map.player_index):
							friendlyAdjCount += 1

						elif (cityAdj.player != self._map.player_index and cityAdj.player != -1):
							sumAdj += cityAdj.army
							enemyAdjCount += 1
							if (largestEnemyAdj == None or largestEnemyAdj.army < cityAdj.army):
								largestEnemyAdj = cityAdj
							
					if (largestEnemyAdj != None and friendlyAdjCount > 0 and friendlyAdjCount >= enemyAdjCount and (self._map.players[self.general.player].standingArmy < 1000 or self._map.turn % 150 < 25)):
						logging.info("KILLING CITY VISION TILES searching for dest bfs kill on tile {},{}".format(largestEnemyAdj.x, largestEnemyAdj.y))
						self.viewInfo.addSearched(largestEnemyAdj)
						killPath = dest_breadth_first_target(self._map, [largestEnemyAdj], sumAdj - largestEnemyAdj.army + 3, 0.2, 6, negativeTiles)
						if (killPath != None):
							self.info("found depth {} dest bfs kill on CITY vision tile {},{}\n{}".format(killPath.length, largestEnemyAdj.x, largestEnemyAdj.y, killPath.toString()))
							paths.append(killPath)
				# if largestEnemyAdj != None:
				# 	logging.info("KILLING GENERAL VISION TILES searching for dest bfs kill on tile {},{}".format(largestEnemyAdj.x, largestEnemyAdj.y))
				# 	self.viewInfo.addSearched(largestEnemyAdj)
				# 	(killStart, killPath) = self.dest_breadth_first_kill(largestEnemyAdj, sumAdj - largestEnemyAdj.army + 5, 0.2, 11, negativeTiles)
				# 	if (killPath != None):
				# 		logging.info("found depth {} dest bfs kill on general vision tile {},{}\n{}".format(killPath.turn, largestEnemyAdj.x, largestEnemyAdj.y, killPath.toString()))
				# 		paths.append(killPath)


			paths = sorted(paths, key=lambda x: (x.length, 0 - x.value))

		if len(paths) == 0 and (self.curPath == None or self.curPath.start.next == None):
			tryGather = True
			player = self._map.players[self.general.player]
			modVal = 0
			enemyGather = False
			if not self.winning_on_economy(byExtraRatio = 0, cityValue = 0) and self.winning_on_army(-0.05):
				enemyGather = True
			neutralGather = len(targets) <= 2
			turn = self._map.turn
			tiles = player.tileCount
			#if tiles < 50:
			#	if turn % 50 < 20:
			#		tryGather = True
			#	if turn % 50 > 40 and turn % 50 < 46:
			#		enemyGather = True
			#elif tiles < 75:
			#	if turn % 50 < 24:
			#		tryGather = True
			#	if turn % 50 > 40 and turn % 50 < 46:
			#		enemyGather = True
			#elif tiles < 90:
			#	if turn % 50 < 30:
			#		tryGather = True
			#	if turn % 50 > 38 and turn % 50 < 45:
			#		enemyGather = True
			#elif tiles < 110:
			#	if turn % 100 < 50:
			#		tryGather = True
			#	if turn % 100 > 80 and turn % 100 < 92:
			#		enemyGather = True
			#elif tiles < 150:
			#	if turn % 100 < 60:
			#		tryGather = True
			#	if turn % 100 > 80 and turn % 100 < 92:
			#		enemyGather = True
			#elif tiles < 200:
			#	if turn % 200 < 120:
			#		tryGather = True
			#	if turn % 100 > 80 and turn % 100 < 92:
			#		enemyGather = True
			#elif tiles < 250:
			#	if turn % 200 < 130:
			#		tryGather = True
			#	if turn % 100 > 80 and turn % 100 < 92:
			#		enemyGather = True
			#else:
			#	if turn % 200 < 140:
			#		tryGather = True
			#	if turn % 100 > 80 and turn % 100 < 92:
			#		enemyGather = True
			
			
			tileDeficitThreshold = self._map.players[self.targetPlayer].tileCount * 1.05
			if (self.makingUpTileDeficit):
				tileDeficitThreshold = self._map.players[self.targetPlayer].tileCount * 1.15 + 8
			
			if not defendEconomy and len(targets) > 2 and player.tileCount < tileDeficitThreshold and not (self.allIn or self.all_in_counter > 50):
				logging.info("ayyyyyyyyyyyyyyyyyyyyyyyyy set enemyGather to True because we're behind on tiles")
				enemyGather = True
				skipFFANeutralGather = (self._map.turn > 50 and self._map.remainingPlayers > 2)
				if not skipFFANeutralGather and (self._map.turn < 120 or len(self.target_player_gather_targets) < 3):
					neutralGather = True
				self.makingUpTileDeficit = True
			else:
				self.makingUpTileDeficit = False
				
			if defendEconomy:
				logging.info("we're playing defensively, neutralGather and enemyGather set to false...")
				neutralGather = False
				enemyGather = False
			# TODO maybe replace with optimal expand? But shouldn't be before gather anymore.
			#if (self.makingUpTileDeficit):
			#	leafMove = self.find_leaf_move(allLeaves)
			#	if (None != leafMove):
			#		self.info("doing tileDeficit leafMove stuff mannn")
			#		return leafMove

			if tryGather:
				gathStartTime = time.time()
				gatherTargets = targets.copy()
				gatherNegatives = negativeTiles.copy()
				negSet = set()
				#for tile in self.largePlayerTiles:
				#	gatherNegatives.add(tile)
				if (self.curPath != None):
					negSet.add(self.curPath.start.tile)

								
				if (enemyGather or neutralGather) and not self.allIn:
					# ENEMY TILE GATHER
					leafGatherTargets = []
					leafPruneStartTime = time.time()
					#for leaf in filter(lambda move: move.dest.army > 0 and (move.source.player == move.dest.player or move.source.army - 1 > move.dest.army), self.leafMoves):
					for leaf in filter(lambda move: move.dest.player == self.targetPlayer or (neutralGather and move.dest.player == -1), self.leafMoves):
						if not (leaf.dest.isCity and leaf.dest.player == -1) and not leaf.dest in self.target_player_gather_targets:
							if leaf.dest.player != self.targetPlayer:
								continue
							useTile = leaf.source
							if leaf.dest.player == self.targetPlayer:
								useTile = leaf.dest
							# determine whether leaf is worth expanding to
							counter = Counter(0)
							def counterFunc(tile):
								if (tile.player == self.targetPlayer or tile.player == -1) and not ((not tile.discovered and tile.isobstacle()) or tile.mountain):
									counter.add(1)
							def skipFunc(tile): 
								return tile.player == self.general.player or tile.mountain or (not tile.discovered and tile.isobstacle())
							breadth_first_foreach(self._map, [useTile], 6, counterFunc, None, skipFunc, None, self.general.player, noLog = True)
							if counter.value > 5:
								logging.info("leaf {} explorability {}:".format(useTile.toString(), counter.value))
								leafGatherTargets.append(useTile)
							else:
								logging.info("pruned leaf {} from gather due to explorability {}:".format(useTile.toString(), counter.value))
					logging.info("pruning leaves and stuff took {:.3f}".format(time.time() - leafPruneStartTime))


					# removed as this doesn't actually help due to low gather distance
					for node in gatherTargets:
						leafGatherTargets.append(node)
					#for city in player.cities:
					#	gatherNegatives.add(city)
					negSet.add(general)
					leafGatherDepth = player.tileCount**0.2 + 4
					move = self.timing_gather(leafGatherTargets, gatherNegatives, skipTiles = None)
					if (move != None):
						self.curPath = None
						self.info("NEW GATHER TO LEAVES AND PATH! Gather move: {} Duration {:.3f}".format(move.toString(), time.time() - gathStartTime))
						return self.move_half_on_repetition(move, 6, 4)
					#logging.info("    ****   leafGatherDepth: {}".format(leafGatherDepth))
					#leafTreeNodes = self.build_mst(leafGatherTargets, 1.0, leafGatherDepth, gatherNegatives, negSet)
					#leafMove = self.get_gather_move(leafTreeNodes, None, minGatherAmount = 1, preferNeutral = True, allowNonKill = True)
					#if (leafMove != None):
					#	self.info("LEAF MST GATHER MOVE! {},{} -> {},{}  leafGatherDepth: {}".format(leafMove.source.x, leafMove.source.y, leafMove.dest.x, leafMove.dest.y, leafGatherDepth))
					#	self.gatherNodes = leafTreeNodes
					#	self.curGather = None
					#	#self.curPath = None
					#	#self.curPathPrio = -1
					#	return self.move_half_on_repetition(leafMove, 6)

				move = self.timing_gather(gatherTargets, gatherNegatives, skipTiles = None)
				if (move != None):
					self.curPath = None
					self.info("NEW GATHER TO GATHER PATH! Gather move: {} Duration {:.3f}".format(move.toString(), time.time() - gathStartTime))
					return self.move_half_on_repetition(move, 6, 4)
				## TARGET PATH GATEHR
				#self.gatherNodes = self.build_mst(gatherTargets, 1.0, 40, gatherNegatives, negSet)
				
				#move = self.get_gather_move(self.gatherNodes, None, allowNonKill = True)
				#if (move != None):
				#	self.info("TARGET-PATH GATHER MOVE! {},{} -> {},{}".format(move.source.x, move.source.y, move.dest.x, move.dest.y))
				#	self.curGather = self.gatherNodes
				#	#self.curPath = None
				#	#self.curPathPrio = -1
				#	return self.move_half_on_repetition(move, 6)
			elif self.curGather != None and self.targetPlayer >= 0:
				move = self.get_gather_move(self.gatherNodes, None, allowNonKill = True)
				if (move != None):
					self.info("POST-GATHER-COMPLETE GATHER MOVE! {},{} -> {},{}".format(move.source.x, move.source.y, move.dest.x, move.dest.y))
					#self.curPath = None
					#self.curPathPrio = -1
					return self.move_half_on_repetition(move, 6)
				else:
					logging.info(".\n ..\n  ...\n   ....\n    .....self.curGather MOVE WAS NULL REEEEEEEEEEEEEEEEEEEEE")
					self.curGather = None
			leafMove = self.find_leaf_move(allLeaves)
			if (None != leafMove):
				return leafMove
			

		if (self.curPath == None or self.curPath.start.next == None):
					
			if (general != None):					
				highPriAttack = False
				attackable = []
				if (self.attackFailedTurn <= self._map.turn - 100 and random.choice(range(3)) == 0):
					for gen in self._map.generals:
						if (gen != None and gen.player != self._map.player_index):
							if (self.cost_effective_to_attack(gen)):
								logging.info("Cost effective to attack general {}.".format(gen.player))
								attackable.append(gen)
								#killPath = self.a_star_kill(player, gen, 0.02, 25)
								highPriAttack = True
							else:
								logging.info("Skipped attack of general {}".format(gen.player))
				#attack undiscovered tiles and cities
				if (self._map.turn > 250 and len(attackable) == 0 and random.choice(range(2)) == 0):
					logging.info("\n------------\nGathering to attack undiscovered or cities:\n------------\n")
					prio = PriorityQueue()					
					#for tile in self.get_enemy_undiscovered():
					if self._map.generals[self.targetPlayer] == None:
						if (self.generalApproximations[self.targetPlayer][2] > 0):
							for tile in random.sample(self.allUndiscovered, max(int(len(self.allUndiscovered) / 3), min(2, len(self.allUndiscovered)))):
								prio.put((self.euclidDist(tile.x, tile.y, self.generalApproximations[self.targetPlayer][0], self.generalApproximations[self.targetPlayer][1]), tile))
					iter = 0
					while not prio.empty() and iter < 3:
						iter += 1
						attackable.append(prio.get()[1])

					if not self.allIn and (len(attackable) == 0 or random.choice(range(4)) == 0) and self._map.players[self.general.player].standingArmy > 100:
						logging.info("including cities")
						for city in self.enemyCities:
							attackable.append(city)
						# if (self._map.turn % 10 == 0):
						# 	logging.info("including large enemy tiles")
						# 	for enemyTile in self.largeVisibleEnemyTiles:
						# 		attackable.append(enemyTile)
					if (len(attackable) == 0 and self.targetPlayer == -1):
						#TODO prioritize better spots wtf not random
						attackable = self.allUndiscovered


									
				if (len(paths) > 0):
					self.curPath = paths[0]
					self.gathers += 1
				else:
					self.curPathPrio = -1
		if (self.curPath != None):
			inc = 0
			while ((self.curPath.start.tile.army <= 1 or self.curPath.start.tile.player != self._map.player_index) and self.curPath.start.next != None):
				inc += 1
				if (self.curPath.start.tile.army <= 1):
					logging.info("!!!!\nMove was from square with 1 or 0 army\n!!!!! {},{} -> {},{}".format(self.curPath.start.tile.x, self.curPath.start.tile.y, self.curPath.start.next.tile.x, self.curPath.start.next.tile.y))
				elif (self.curPath.start.tile.player != self._map.player_index):
					logging.info("!!!!\nMove was from square OWNED BY THE ENEMY\n!!!!! [{}] {},{} -> {},{}".format(self.curPath.start.tile.player, self.curPath.start.tile.x, self.curPath.start.tile.y, self.curPath.start.next.tile.x, self.curPath.start.next.tile.y))
				logging.info("{}: doing made move thing? Path: {}".format(inc, self.curPath.toString()))
				self.curPath.made_move()
				if inc > 20:
					raise ArithmeticError("bitch, what you doin?")
				
			if (self.curPath.start.next != None):
				dest = self.curPath.start.next.tile
				source = self.curPath.start.tile
				if (dest.isCity or dest.isGeneral) and dest.player != self._map.player_index:
					if (source.army - 2 < dest.army):
						gatherDist = len(self.target_player_gather_targets) / 2
						logging.info("Tried to take a city / general with less than enough army.")
						if (dest.isGeneral and self._map.players[self.general.player].tileCount < self._map.players[self.targetPlayer].tileCount):
							gatherDist = len(self.target_player_gather_targets) / 4
							logging.info("Losing economically and target was general, searching a shorter additional killpath.")
											
						armyAmount = -1
						if (dest.isGeneral or (dest.isCity and dest.player >= 0)):
							armyAmount = dest.army / 2
						paths = self.WeightedBreadthSearch([dest], gatherDist, 0.12, -2, armyAmount, 10, negativeTiles)
						if (len(paths) > 0):
							self.curPath = paths[0]
							logging.info("Found path to cap the city: {}".format(self.curPath.toString()))
						elif dest.isGeneral:
							self.attackFailedTurn = self._map.turn
							self.curPath = None	
							self.curPathPrio = -1
						else:							
							self.curPath = None	
							self.curPathPrio = -1


				if (self.curPath != None and self.curPath.start.next != None and self.curPath.start.tile.isGeneral and not self.general_move_safe(self.curPath.start.next.tile)):
					#self.curPath = None	
					#self.curPathPrio = -1
					#logging.info("General move in path would have violated general min army allowable. Repathing.")					
					if (self.general_move_safe(self.curPath.start.next.tile, move_half=True)):
						logging.info("General move in path would have violated general min army allowable. Moving half.")
						move = Move(self.curPath.start.tile, self.curPath.start.next.tile, True)
						return move
					else:
						self.curPath = None	
						self.curPathPrio = -1
						logging.info("General move in path would have violated general min army allowable. Repathing.")					

				else:
					cleanPath = False
					while self.curPath != None and not cleanPath:
						if (self.curPath.start.tile in negativeTiles and self.curPath.start.tile.army > 5):
							tile = self.curPath.start.tile
							# self.curPathPrio = -1
							logging.info("\n\n\n~~~~~~~~~~~\nSKIPPED: Move was from a negative tile {},{}\n~~~~~~~~~~~~~\n\n~~~\n".format(tile.x, tile.y))
							self.curPath = None
							self.curPathPrio = -1
							if threat != None:
								killThreatPath = self.kill_threat(self.threat)
								if killThreatPath != None:
									self.info("Final path to kill threat! {}".format(killThreatPath.toString()))
									self.curPath = killThreatPath
									return Move(killThreatPath.start.tile, killThreatPath.start.next.tile)
							else:
								logging.warn("Negative tiles prevented a move but there was no threat???")

						elif (self.curPath.start.next != None and self.curPath.start.next.next != None and self.curPath.start.tile == self.curPath.start.next.next.tile and self.curPath.start.next.tile.player == self.curPath.start.tile.player):
							logging.info("\n\n\n~~~~~~~~~~~\nCleaned double-back from path\n~~~~~~~~~~~~~\n\n~~~\n")
							self.curPath.made_move()
						elif (self.curPath.start.tile.player != self._map.player_index or self.curPath.start.tile.army < 2):
							logging.info("\n\n\n~~~~~~~~~~~\nCleaned useless move from path\n~~~~~~~~~~~~~\n\n~~~\n")
							self.curPath.made_move()
						else:
							cleanPath = True
					if (self.curPath != None and self.curPath.start.next != None):
						if self.curPath.start.tile == self.general and not self.general_move_safe(self.curPath.start.next.tile, self.curPath.start.move_half):
							self.curPath = None
							self.curPathPrio = -1
						else:
							move = Move(self.curPath.start.tile, self.curPath.start.next.tile, self.curPath.start.move_half)
							end = time.time()
							logging.info("Path Move Duration: {:.2f}".format(end - start))
							#self.info("MAKING MOVE FROM NEW PATH CLASS! Path {}".format(self.curPath.toString()))
							return self.move_half_on_repetition(move, 6, 3)
				

			self.curPath = None
		self.curPathPrio = -1
		end = time.time()
		self.info("!!!!\nFOUND NO MOVES, GONNA GATHER {}\n!!!!!".format(end - start))
		logging.info("\n\n!-!-!-!-!-! \n         WHEE WHOO WHEE WHOO NO MOVES \n       WE GATHERIN NOW CUZ NO MOVES \n!-!-!-!-!-!")
		
		gathers = self.build_mst(self.target_player_gather_targets, 1.0, 50,  None)
		self.gatherNodes = gathers
		move = self.get_gather_move(gathers, None, 1, 0, preferNeutral = True)
		if move == None:
			self.info("Found-no-moves-gather found no move ?????")
		elif (self.is_move_safe_valid(move)):
			return move
		elif move != None:
			self.info("Found-no-moves-gather move {},{} -> {},{} was not safe or valid!".format(move.source.x, move.source.y, move.dest.x, move.dest.y))

		if (allowRetry):
			logging.info("Retrying.")
			return self.select_move(False)
		return None
	
	def kill_threat(self, threat):
		threatPath = threat.path
		threatPathSet = set(threatPath.tileSet)
		threatPathSet.remove(threatPath.start.tile)
		# doesn't make any sense to have the general defend against his own threat, does it? Maybe it does actually hm
		negativeTiles = set()
		negativeTiles.add(self.general)
		gatherToThreatPath = dest_breadth_first_target(self._map, threatPathSet, threatPath.start.tile.army, 0.1, threatPath.length, searchingPlayer = self.general.player, negativeTiles = negativeTiles)
		if gatherToThreatPath != None:
			logging.info("whoo, found kill on threatpath with path {}".format(gatherToThreatPath.toString()))
			alpha = 140
			minAlpha = 100
			alphaDec = 2
			self.viewInfo.paths.appendleft(PathColorer(gatherToThreatPath.clone(), 150, 150, 255, alpha, alphaDec, minAlpha))
			tail = gatherToThreatPath.tail.tile

			goalFunc = lambda tile, prioObject: tile == threatPath.start.tile

			def threatPathSortFunc(nextTile, prioObject):
				(dist, negNumThreatTiles, negArmy) = prioObject
				if nextTile in threatPathSet:
					negNumThreatTiles -= 1
				if nextTile.player == self.general.player:
					negArmy -= nextTile.army
				else:
					negArmy += nextTile.army
				dist += 1
				return (dist, negNumThreatTiles, negArmy)
			inputTiles = {}
			inputTiles[tail] = ((0, 0, 0), 0)

			threatPathToThreat = breadth_first_dynamic(self._map, inputTiles, goalFunc, noNeutralCities=True, priorityFunc=threatPathSortFunc)
			if threatPathToThreat != None:
				logging.info("whoo, finished off the threatpath kill {}\nCombining paths...".format(threatPathToThreat.toString()))
				node = threatPathToThreat.start.next
				while node != None:
					gatherToThreatPath.add_next(node.tile)
					node = node.next
				gatherToThreatPath.calculate_value(self.general.player)
		return gatherToThreatPath

	def gather_to_target(self, target, maxTime, maxDepth, gatherNegatives = None, negativeSet = None, targetArmy = None):
		if targetArmy == None:
			targetArmy = target.army + 1
		targets = self.get_path_to_target(target, maxTime, maxDepth, True, preferNeutral = True).tileSet
		TreeNodes = self.build_mst(targets, maxTime, maxDepth, gatherNegatives, negativeSet)
		move = self.get_gather_move(TreeNodes, None, targetArmy)
		if (move != None):
			self.gatherNodes = TreeNodes
			#self.curPath = None
			#self.curPathPrio = -1
			return self.move_half_on_repetition(move, 5)
		return None


	def gather_to_target_tile(self, target, maxTime, maxDepth, gatherNegatives = None, negativeSet = None, targetArmy = None):
		targets = [target]
		if targetArmy == None:
			targetArmy = target.army + 1
		return self.gather_to_target_tiles(targets, maxTime, maxDepth, gatherNegatives, negativeSet, targetArmy)

	def gather_to_target_tiles(self, targets, maxTime, maxDepth, gatherNegatives = None, negativeSet = None, targetArmy = None):
		if targetArmy == None:
			targetArmy = targets[0].army + 1
		#gatherNodes = self.build_mst(targets, maxTime, maxDepth, gatherNegatives, negativeSet)
		#move = self.get_gather_move(gatherNodes, None, targetArmy, None)
		gatherNodes = greedy_backpack_gather(self._map, targets, maxDepth, targetArmy, negativeTiles = negativeSet, searchingPlayer = self.general.player, viewInfo = self.viewInfo)
		move = self.get_tree_move_default(gatherNodes)
		if (move != None):
			self.gatherNodes = gatherNodes
			#self.curPath = None
			#self.curPathPrio = -1
			return self.move_half_on_repetition(move, 4)
		return None


	def get_enemy_undiscovered(self):
		enemyUndiscovered = []
		for tile in self.allUndiscovered:			
			for siblingTile in tile.moveable: #new spots to try
				if (siblingTile.player != -1):
					enemyUndiscovered.append(tile)
		return enemyUndiscovered
	
	def shortestPath(self, start, goal):
		return a_star_search(start, goal, _shortestPathHeur, _shortestPathCost)


	def _shortestPathCost(self, a, b):
		return 1

	def euclidDist(self, x, y, x2, y2):
		return pow(pow(abs(x - x2), 2) + pow(abs(y - y2), 2), 0.5)

	#def minimax_defense(self, startTiles, goal, maxTime = 0.1, maxDepth = 20):

	#	frontier = deque()
	#	visited = [[{} for x in range(self._map.rows)] for y in range(self._map.cols)]
	#	for start in startTiles:
	#		frontier.appendleft((start, 0, start.army))
	#		visited[start.x][start.y][0] = (start.army, None)
	#	start = time.time()
	#	iter = 0
	#	foundGoal = False
	#	foundArmy = -1
	#	foundDist = -1
	#	depthEvaluated = 0
	#	while not len(frontier) == 0:
	#		iter += 1
	#		if (iter % 100 == 0 and time.time() - start > maxTime):
	#			break
			
	#		(current, dist, army) = frontier.pop()


	#		x = current.x
	#		y = current.y				
			
	#		if current == goal:
	#			if army > 0 and army > foundArmy:
	#				foundGoal = True
	#				foundDist = dist
	#				foundArmy = army
	#			else: # skip paths that go through king, that wouldn't make sense
	#				continue
	#		if dist > depthEvaluated:
	#			depthEvaluated = dist
	#		if (dist <= maxDepth and not foundGoal):
	#			for i in [[x - 1,y],[x + 1,y],[x,y - 1],[x,y + 1]]: #new spots to try
	#				if (i[0] < 0 or i[1] < 0 or i[0] >= self._map.cols or i[1] >= self._map.rows):
	#					continue
	#				next = self._map.grid[i[1]][i[0]]
	#				inc = 0 if not (next.isCity or next.isGeneral) else dist / 2
	#				self.viewInfo.evaluatedGrid[next.x][next.y] += 1
	#				if (next.mountain or (not next.discovered and next.isobstacle())):
	#					continue
	#				#new_cost = cost_so_far[current] + graph.cost(current, next)
	#				nextArmy = army - 1
	#				if (startTiles[0].player == next.player):
	#					nextArmy += next.army + inc
	#				else:
	#					nextArmy -= (next.army + inc)
	#					if (nextArmy <= 0):
	#						continue
	#				newDist = dist + 1
	
	#				if newDist not in visited[next.x][next.y] or visited[next.x][next.y][newDist][0] < nextArmy:
	#					visited[next.x][next.y][newDist] = (nextArmy, current)
	#				frontier.appendleft((next, newDist, nextArmy))

	#	logging.info("BFS SEARCH ITERATIONS {}, DURATION: {}, DEPTH: {}".format(iter, time.time() - start, depthEvaluated))
	#	if foundDist < 0:
	#		return None
		
	#	pathStart = PathNode(goal, None, foundArmy, foundDist, -1, None)
	#	path = pathStart
	#	node = goal
	#	dist = foundDist
	#	while (node != None):
	#		army, node = visited[node.x][node.y][dist]
	#		dist -= 1
	#		path = PathNode(node, path, army, dist, -1, None) 

	#	logging.info("BFS FOUND KILLPATH OF LENGTH {} VALUE {}".format(pathStart.turn, pathStart.value))
	#	return pathStart
	
	def cost_effective_to_attack(self, enemyGen):
		player = self._map.players[self.general.player]
		enemyPlayer = self._map.players[enemyGen.player]

		armyBase = player.standingArmy - self.general_min_army_allowable()

		if (enemyPlayer.tileCount == 1 and enemyGen.army > 30 and self._map.remainingPlayers > 2):
			return False

		if (armyBase * 0.7 < enemyGen.army + 15):
			return False
		return True

	def enemy_army_near(self, tile, distance = 2):		
		enemyNear = Counter(0)
		counterLambda = lambda tile: enemyNear.add(tile.army - 1)
		negativeLambda = lambda tile: tile.player == self.general.player or tile.player == -1
		skipFunc = lambda tile: tile.isCity == True and tile.player == -1
		breadth_first_foreach(self._map, [tile], distance, counterLambda, negativeLambda, skipFunc, noLog = True)
		value = enemyNear.value
		if tile.player != -1 and tile.player != self.general.player:
			# don't include the tiles army itself...
			value = value - (tile.army - 1)
		#logging.info("enemy_army_near for tile {},{} returned {}".format(tile.x, tile.y, value))
		return value
		

	def player_army_near(self, tile, distance = 2, player = None):
		if (player == None):
			player = self._map.player_index
		armyNear = Counter(0)
		counterLambda = lambda tile: armyNear.add(tile.army - 1)
		negativeLambda = lambda tile: tile.player != player or (tile.isCity and tile.player == -1)
		breadth_first_foreach(self._map, [tile], distance, counterLambda, negativeLambda)
		value = armyNear.value
		if tile.player == player:
			# don't include the tiles army itself...
			value = value - (tile.army - 1)
		logging.info("player_army_near for tile {},{} player {} returned {}".format(tile.x, tile.y, player, value))
		return value

	
	def explore_target_player_undiscovered(self, negativeTiles, targetArmy = 1):
		if self._map.turn < 100 or self.targetPlayer == -1 or self._map.generals[self.targetPlayer] != None:
			return None
		genPlayer = self._map.players[self.general.player]
		enemyUndiscBordered = []
		if self.targetPlayer != -1:
			for tile in self.allUndiscovered:
				for move in tile.moveable:
					if move.player == self.targetPlayer:
						enemyUndiscBordered.append(move)
		path = dest_breadth_first_target(self._map, enemyUndiscBordered, targetArmy, 0.03, 2, negativeTiles, self._map.player_index, False, 1, True)
		if not path:
			path = dest_breadth_first_target(self._map, enemyUndiscBordered, max(targetArmy, max(8, (genPlayer.standingArmy ** 0.5) / 4)), 0.03, 5, negativeTiles, self._map.player_index, False, 1, True)
		return path
			

	def get_median_tile_value(self, percentagePoint = 50):
		tiles = [tile for tile in self._map.players[self.general.player].tiles]
		tiles = sorted(tiles, key = lambda tile: tile.army)
		tileIdx = max(0, len(tiles)*percentagePoint//100 - 1)
		if len(tiles) > tileIdx:
			return tiles[tileIdx].army
		else:
			logging.info("whoah, dude cmon,Z ZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzzZZzz")
			logging.info("hit that weird tileIdx bug.")
			return 0


	def build_mst(self, startTiles, maxTime = 0.1, maxDepth = 30, negativeTiles = None, avoidTiles = None, priorityFunc = None):
		LOG_TIME = False
		origStartTiles = startTiles
		startTiles = set(startTiles)
		self.leafValueGrid = [[None for x in range(self._map.rows)] for y in range(self._map.cols)]
		searchingPlayer = self._map.player_index
		frontier = PriorityQueue()
		visitedBack = [[None for x in range(self._map.rows)] for y in range(self._map.cols)]

		if isinstance(startTiles, dict):
			for tile in startTiles.keys():
				(startPriorityObject, distance) = startTiles[tile]
				startVal = startPriorityObject
				frontier.put((startVal, distance, tile, tile))
		else:
			if priorityFunc != None:
				raise AssertionError("You MUST use a dict of starttiles if not using the default priorityFunc")
			for tile in startTiles:
				negEnemyCount = 0
				if tile.player == self.targetPlayer:
					negEnemyCount = -1
				frontier.put((0, (0, negEnemyCount, tile.x, tile.y), tile, tile))

		if not priorityFunc:
			def default_priority_func(nextTile, currentPriorityObject):			
				(negArmy, negEnemyCount, xSum, ySum) = currentPriorityObject
				army = 0 - negArmy					
				nextArmy = army - 1
				if (negativeTiles == None or nextTile not in negativeTiles):
					if (searchingPlayer == nextTile.player):
						nextArmy += nextTile.army
					else:
						nextArmy -= nextTile.army
				newEnemyCount = negEnemyCount
				if (nextTile.player == self.targetPlayer):
					newEnemyCount -= 1
				return (0-nextArmy, newEnemyCount, xSum + nextTile.x, ySum + nextTile.y)
			priorityFunc = default_priority_func
				# if newDist not in visited[next.x][next.y] or visited[next.x][next.y][newDist][0] < nextArmy:
				# 	visited[next.x][next.y][newDist] = (nextArmy, current)
		
	

		# sort on distance, then army, then x and y (to stop the paths from shuffling randomly and looking annoying)
		start = time.time()
			#frontier.put((0, startArmy, tile.x, tile.y, tile, None, 0))
		depthEvaluated = 0
		while not frontier.empty():			
			(dist, curPriorityVal, current, cameFrom) = frontier.get()
			x = current.x
			y = current.y
			if (visitedBack[x][y] != None):
				continue
			if avoidTiles != None and current in avoidTiles:
				continue
			if (current.mountain or (not current.discovered and current.isobstacle())):
				continue
			if (current.isCity and current.player != searchingPlayer and not current in startTiles):
				continue
			visitedBack[x][y] = cameFrom

			if dist > depthEvaluated:
				depthEvaluated = dist
			if (dist <= maxDepth):
				dist += 1
				for next in current.moveable: #new spots to try
					nextPriorityVal = priorityFunc(next, curPriorityVal)
					frontier.put((dist, nextPriorityVal, next, current))
		if (LOG_TIME):
			logging.info("BUILD-MST DURATION: {:.2f}, DEPTH: {}".format(time.time() - start, depthEvaluated))

		result = self.build_mst_rebuild(startTiles, visitedBack, self._map.player_index)
		
		# hopefully this starts showing stuff?
		dictStart = {}
		if isinstance(startTiles, dict):
			for tile in startTiles.keys():
				dist = 0
				startVal = (0, 0, 0, tile.x, tile.y)
				dictStart[tile] = (startVal, dist)
		else:		
			for tile in startTiles:
				dist = 0
				startVal = (0, 0, 0, tile.x, tile.y)
				dictStart[tile] = (startVal, dist)
		
		return result

	def build_mst_rebuild(self, startTiles, fromMap, searchingPlayer):
		results = []
		for tile in startTiles:
			gather = self.get_gather(tile, None, fromMap, 0, searchingPlayer)
			if (gather.tile.player == searchingPlayer):
				gather.value -= gather.tile.army
			else:
				gather.value += gather.tile.army
				
			results.append(gather)
		return results

	def get_gather(self, tile, fromTile, fromMap, turn, searchingPlayer):
		gatherTotal = tile.army
		turnTotal = 1
		if (tile.player != searchingPlayer):
			gatherTotal = 0 - tile.army
		gatherTotal -= 1
		thisNode = TreeNode(tile, fromTile, turn)
		if (tile.player == -1):
			thisNode.neutrals = 1
		for move in tile.moveable:
			# logging.info("evaluating {},{}".format(move.x, move.y))
			if (move == fromTile):
				# logging.info("move == fromTile  |  {},{}".format(move.x, move.y))
				continue
			if (fromMap[move.x][move.y] != tile):
				# logging.info("fromMap[move.x][move.y] != tile  |  {},{}".format(move.x, move.y))
				continue
			gather = self.get_gather(move, tile, fromMap, turn + 1, searchingPlayer)
			if (gather.value > 0):
				gatherTotal += gather.value
				turnTotal += gather.gatherTurns
				thisNode.children.append(gather)
				thisNode.neutrals += gather.neutrals
				
		thisNode.value = gatherTotal
		thisNode.gatherTurns = turnTotal
		# only de-prioritize cities when they are the leaf
		if thisNode.tile.isCity and 0 == len(thisNode.children):
			thisNode.value -= 10
		# logging.info("{},{} ({}  {})".format(thisNode.tile.x, thisNode.tile.y, thisNode.value, thisNode.gatherTurns))
		return thisNode
	
	def get_tree_move_default(self, gathers, priorityFunc = None, valueFunc = None):
		logging.info("G E T T R E E M O V E D E F A U L T ! ! !")
		if priorityFunc == None:
			# default priority func, gathers based on cityCount then distance from general
			def default_priority_func(nextTile, currentPriorityObject):
				cityCount = distToGen = negArmy = 0
				if currentPriorityObject != None:
					(cityCount, distToGen, negArmy) = currentPriorityObject
					negArmy += 1
				if nextTile.player == self.general.player and (nextTile.isGeneral or nextTile.isCity):
					cityCount += 1
				distToGen = 0 - self.distance_from_general(nextTile)
				if (nextTile.player == self.general.player):
					negArmy -= nextTile.army
				else:
					negArmy += nextTile.army
				return (cityCount, distToGen, negArmy)
			priorityFunc = default_priority_func

		if valueFunc == None:
			# default value func, gathers based on cityCount then distance from general
			def default_value_func(currentTile, currentPriorityObject):
				cityCount = distToGen = negArmy = 0
				if currentPriorityObject != None:
					(cityCount, distToGen, negArmy) = currentPriorityObject
				# because these are all negated in the priorityFunc we need to negate them here for making them 'positive' weights for value
				return (0 - cityCount, 0 - distToGen - negArmy)
				#return (0 - cityCount, 0 - distToGen, 0 - negArmy)
			valueFunc = default_value_func

		return get_tree_move(gathers, priorityFunc, valueFunc)
	
	def get_gather_move(self, gathers, parent, minGatherAmount = 0, pruneThreshold = None, preferNeutral = True, allowNonKill = False):
		#logging.info("G A T H E R I N G :  minGatherAmount {}, pruneThreshold {}, preferNeutral {}, allowNonKill {}".format(minGatherAmount, pruneThreshold, preferNeutral, allowNonKill))
		if pruneThreshold == None:
			player = self._map.players[self.general.player]
			pruneThreshPercent = 45
			pruneThreshold = self.get_median_tile_value(pruneThreshPercent) - 1
			logging.info("~!~!~!~!~!~!~ MEDIAN {}: {}".format(20, self.get_median_tile_value(20)))
			logging.info("~!~!~!~!~!~!~ MEDIAN {}: {}".format(35, self.get_median_tile_value(35)))
			logging.info("~!~!~!~!~!~!~ MEDIAN {}: {}".format(50, self.get_median_tile_value(50)))
			#logging.info("~!~!~!~!~!~!~ MEDIAN {}: {}".format(65, self.get_median_tile_value(65)))
			logging.info("~!~!~!~!~!~!~ MEDIAN {}: {}".format(75, self.get_median_tile_value(75)))
			logging.info("~!~!~!~!~!~!~ pruneThreshold {}: {}".format(pruneThreshPercent, pruneThreshold))
		
			pruneThreshold = math.floor((player.standingArmy - self.general.army) / player.tileCount)
			logging.info("~!~!~!~!~!~!~ pruneThreshold via average {}%: {}".format(pruneThreshPercent, pruneThreshold))
		logging.info("G A T H E R I N G :  minGatherAmount {}, pruneThreshold {}, preferNeutral {}, allowNonKill {}".format(minGatherAmount, pruneThreshold, preferNeutral, allowNonKill))
		start = time.time()
		logging.info("Gathering :)")
		move = self._get_gather_move_int_v2(gathers, parent, minGatherAmount, pruneThreshold, preferNeutral, allowNonKill = allowNonKill)
		if move == None and pruneThreshold > 0:
			newThreshold = max(0, self.get_median_tile_value(25) - 2)
			logging.info("\nEEEEEEEEEEEEEEEEEEEEEEEE\nEEEEEEEEE\nEE\nNo move found for pruneThreshold {}, retrying with {}".format(pruneThreshold, newThreshold))
			move = self._get_gather_move_int_v2(gathers, parent, minGatherAmount, newThreshold, preferNeutral, allowNonKill = allowNonKill)
		if move == None:
			logging.info("\nNo move found......... :(")
			newThreshold = 0
			logging.info("\nEEEEEEEEEEEEEEEEEEEEEEEE\nEEEEEEEEE\nEE\nNo move found for pruneThreshold {}, retrying with {}".format(pruneThreshold, newThreshold))
			move = self._get_gather_move_int_v2(gathers, parent, minGatherAmount, newThreshold, preferNeutral, allowNonKill = allowNonKill)
		if move == None:
			logging.info("\nNo move found......... :(")
		logging.info("GATHER MOVE DURATION: {:.2f}".format(time.time() - start))
		return move
	

	def _get_gather_move_int_v2(self, gathers, parent, minGatherAmount = 0, pruneThreshold = 0, preferNeutral = False, allowNonKill = False):
		LOG_STUFF = False
		pX = "  "
		pY = "  "
		minGatherAmount = 0
		if parent != None:
			pX = parent.tile.x
			pY = parent.tile.y
		move = None
		maxGather = None
		for gather in gathers:
			curMove = None
			gatherWorthwhile = is_gather_worthwhile(gather, parent)			
			if parent == None or gatherWorthwhile:
				curMove = self._get_gather_move_int_v2(gather.children, gather, minGatherAmount, pruneThreshold, preferNeutral, allowNonKill)
				#update this gathers value with its changed childrens values
				newVal = 0
				newTurns = 1
				if parent != None:
					newVal = gather.tile.army - 1
					if gather.tile.player != self.general.player:
						newVal = -1 - gather.tile.army
				for child in gather.children:
					newVal += child.value
					newTurns += child.gatherTurns
				if LOG_STUFF:
					logging.info("{},{} <- [update] Gather {},{} updated value {}->{} and turns {}->{}".format(pX, pY, gather.tile.x, gather.tile.y, gather.value, newVal, gather.gatherTurns, newTurns))
				gather.value = newVal
				gather.gatherTurns = newTurns
			if (gather.value > 0):
				self.leafValueGrid[gather.tile.x][gather.tile.y] = gather.value
			else:
				if LOG_STUFF:
					logging.info("{},{} <- [!worth] Gather {},{} val-turns {}-{} was new maxGather".format(pX, pY, gather.tile.x, gather.tile.y, gather.value, gather.gatherTurns))
			#if maxGather == None or (gather.value - gather.tile.army) / gather.gatherTurns > (maxGather.value - maxGather.tile.army) / maxGather.gatherTurns:
			if (gather.value / gather.gatherTurns > pruneThreshold and gather.value >= minGatherAmount):
				if (gather == compare_gathers(maxGather, gather, preferNeutral)):
					if LOG_STUFF:
						logging.info("{},{} <- [max!] Gather {},{} val-turns {}-{} was new maxGather".format(pX, pY, gather.tile.x, gather.tile.y, gather.value, gather.gatherTurns))					
					maxGather = gather
					if self.is_move_safe_valid(curMove, allowNonKill = allowNonKill):
						if LOG_STUFF:
							logging.info("{},{} <- [max!] Gather {},{} val-turns {}-{} was new maxGather".format(pX, pY, gather.tile.x, gather.tile.y, gather.value, gather.gatherTurns))
						move = curMove
					elif curMove != None:
						if LOG_STUFF:
							logging.info("{},{} <- [inval] Gather MOVE {},{} <- {},{} returned by gather {},{} wasn't safe or wasn't valid".format(pX, pY, curMove.dest.x, curMove.dest.y, curMove.source.x, curMove.source.y, gather.tile.x, gather.tile.y))
					else:
						if LOG_STUFF and False:
							logging.info("{},{} <- [     ] Gather {},{} didn't return any child moves".format(pX, pY, gather.tile.x, gather.tile.y))
				else:
					if LOG_STUFF:
						logging.info("{},{} <- [worse] Gather {},{} val-turns {}-{} was worse than maxGather {},{} val-turns {}-{}".format(pX, pY, gather.tile.x, gather.tile.y, gather.value, gather.gatherTurns, maxGather.tile.x, maxGather.tile.y, maxGather.value, maxGather.gatherTurns))
			else:
				if LOG_STUFF:
					logging.info("{},{} <- [prune] Gather {},{} val-turns {}-{} did not meet the prune threshold or min gather amount.".format(pX, pY, gather.tile.x, gather.tile.y, gather.value, gather.gatherTurns))

		
		if move != None:
			return move
		if maxGather != None:
			if LOG_STUFF:
				logging.info("{},{} <- maxGather was {},{} but no move. We should be considering making this as a move.".format(pX, pY, maxGather.tile.x, maxGather.tile.y))
			if parent != None:
				if maxGather.tile.army <= 1 or maxGather.tile.player != self._map.player_index:
					if LOG_STUFF:
						logging.info("{},{} <- WTF tried to move {},{} with 1 or less army :v".format(pX, pY, maxGather.tile.x, maxGather.tile.y))
				elif maxGather.value > 0:
					if LOG_STUFF:
						logging.info("{},{} <- Returning {},{} -> {},{}".format(pX, pY, maxGather.tile.x, maxGather.tile.y, pX, pY))
					#parent.children.remove(maxGather)
					maxGather.children = []
					maxGather.value = maxGather.tile.army - 1
					maxGather.gatherTurns = 1
					self.leafValueGrid[maxGather.tile.x][maxGather.tile.y] = maxGather.value
					return Move(maxGather.tile, parent.tile)
		if LOG_STUFF:
			logging.info("{},{} <- FUCK! NO POSITIVE GATHER MOVE FOUND".format(pX, pY))
		return None

	def _get_gather_move_int(self, gathers, parent, minGatherAmount = 0, pruneThreshold = 0, preferNeutral = False, allowNonKill = False):
		move = None
		maxGather = None
		for gather in gathers:
			if (gather.value <= 0):
				logging.info("gather {},{} worthless".format(gather.tile.x, gather.tile.y))
				# then just prune it and don't log it?
				continue
			#if maxGather == None or (gather.value - gather.tile.army) / gather.gatherTurns > (maxGather.value - maxGather.tile.army) / maxGather.gatherTurns:
			if (gather.value / gather.gatherTurns > pruneThreshold):
				if (gather.value >= minGatherAmount):
					if (gather == compare_gathers(maxGather, gather, preferNeutral)):
						maxGather = gather
					else:
						logging.info("[non] gather {},{} was worse than maxGather in compare_gathers, value/gather.gatherTurns {}/{} ({})".format(gather.tile.x, gather.tile.y, gather.value, gather.gatherTurns, (gather.value/gather.gatherTurns)))
				else:
					logging.info("[low] gather {},{} value {} was less than minGatherAmount {}".format(gather.tile.x, gather.tile.y, gather.value, minGatherAmount))
			else:
				logging.info("[prn] gather {},{} value/gather.gatherTurns {}/{} ({}) was less than pruneThreshold {}".format(gather.tile.x, gather.tile.y, gather.value, gather.gatherTurns, (gather.value/gather.gatherTurns), pruneThreshold))
		
		# if maxGather != None and (parent == None or maxGather.value / maxGather.gatherTurns > parent.value / parent.gatherTurns):
		if maxGather != None:
			logging.info("}}max{{ gather {},{} was maxGather! value/gather.gatherTurns {}/{} ({}) pruneThreshold {}".format(maxGather.tile.x, maxGather.tile.y, maxGather.value, maxGather.gatherTurns, (maxGather.value/maxGather.gatherTurns), pruneThreshold))
			gatherWorthwhile = is_gather_worthwhile(maxGather, parent)
			if parent == None or gatherWorthwhile:
				# minGatherAmount = 1 is a hack because until the full gather is planned out in advance, 
				# we don't know what will be pruned and can't keep this number evaluated correctly recursively.
				# So we only use it to pick an initial gather branch, and then don't prune any further than the trunk with it for now.
				minGatherAmount = 1
				move = self._get_gather_move_int(maxGather.children, maxGather, minGatherAmount, pruneThreshold, preferNeutral, allowNonKill)
				if self.is_move_safe_valid(move, allowNonKill = allowNonKill):
					logging.info("Returning child move {},{} -> {},{}".format(move.source.x, move.source.y, move.dest.x, move.dest.y))
					return move
			else:
				logging.info("Cut {},{} because not gatherWorthwhile or no parent".format(maxGather.tile.x, maxGather.tile.y))
			if parent != None:
				if maxGather.tile.army <= 1 or maxGather.tile.player != self._map.player_index:
					logging.info("WTF tried to move {},{} with 1 or less army :v".format(maxGather.tile.x, maxGather.tile.y))
				elif maxGather.value > 0:
					logging.info("Returning {},{} -> {},{}".format(maxGather.tile.x, maxGather.tile.y, parent.tile.x, parent.tile.y))
					parent.children.remove(maxGather)
					return Move(maxGather.tile, parent.tile)
			logging.info("FUCK! NO POSITIVE, LEGAL, SAFE GATHER MOVE FOUND at gather {},{} value {} gatherTurns {}".format(maxGather.tile.x, maxGather.tile.y, maxGather.value, maxGather.gatherTurns))
		else:
			logging.info("FUCK! NO POSITIVE GATHER MOVE FOUND, no maxGather")
			
		return None

	def get_threat_killer_move(self, threat, searchTurns, negativeTiles):
		killTiles = [threat.path.start.next.tile, threat.path.start.tile]
		armyAmount = threat.threatValue + 1
		skipTiles = set()
		if threat.path.start.next != None:
			skipTiles.add(threat.path.start.next.tile)
			if threat.path.start.next.next != None:
				skipTiles.add(threat.path.start.next.next.tile)
		saveTile = None
		largestTile = None
		source = None
		for threatSource in killTiles:
			for tile in threatSource.moveable:
				if tile.player == self._map.player_index and tile not in skipTiles:
					if largestTile == None or tile.army > largestTile.army:
						largestTile = tile
						source = threatSource
		if largestTile != None:
			if threat.threatValue - largestTile.army + 1 < 0:
				logging.info("reeeeeeeeeeeeeeeee\nFUCK YES KILLING THREAT TILE {},{}".format(largestTile.x, largestTile.y))
				saveTile = largestTile
			else:
				# else see if we can save after killing threat tile
				negativeTilesIncludingThreat = set()
				negativeTilesIncludingThreat.add(largestTile)
				dict = {}
				for tile in negativeTiles:
					negativeTilesIncludingThreat.add(tile)
				for tile in threat.path.tileSet:
					negativeTilesIncludingThreat.add(tile)
				if threat.saveTile != None:
					dict[threat.saveTile] = (0, threat.threatValue)
					self.viewInfo.addSearched(threat.saveTile)
					logging.info("(killthreat) dict[threat.saveTile] = (0, {})  -- threat.saveTile {},{}".format(threat.saveTile.army, threat.saveTile.x, threat.saveTile.y))
				savePathSearchModifier = 1
				if largestTile in threat.path.start.tile.moveable:
					logging.info("largestTile was adjacent to the real threat tile, so savepath needs to be 1 turn shorter for this to be safe")
					# then we have to be prepared for this move to fail the first turn. Look for savePath - 1
					savePathSearchModifier = 2
				bestPath = dest_breadth_first_target(self._map, dict, armyAmount + 1 - largestTile.army, 0.1, searchTurns - savePathSearchModifier, negativeTilesIncludingThreat, ignoreGoalArmy=True)
				if bestPath != None:
					self.viewInfo.paths.appendleft(PathColorer(bestPath, 250,250, 250, 200, 12, 100))
					if (largestTile.army > 5 or threat.threatValue < largestTile.army):
						logging.info("reeeeeeeeeeeeeeeee\nkilling threat tile with {},{}, we still have time for defense after with path {}:".format(largestTile.x, largestTile.y, bestPath.toString())) 
						saveTile = largestTile
					else:
						logging.info("threatKill {},{} -> {},{} not worthwhile?".format(largestTile.x, largestTile.y, source.x, source.y))


		if saveTile != None:
			return Move(saveTile, source)
		return None

	def get_cities_bordered_by_enemy(self, enemyTileCount = 1):
		player = self._map.players[self.general.player]
		cities = where(player.cities, lambda x: x.player == player.index and count(x.adjacents, lambda y: y.player >= 0 and y.player != player.index) >= enemyTileCount)
		return cities



	def a_star_search(self, start, goal, heurFunc, costFunc, goalFunc):
		frontier = PriorityQueue()
		frontier.put(start, 0)
		came_from = {}
		cost_so_far = {}
		came_from[start] = None
		cost_so_far[start] = 0
	
		while not frontier.empty():
			current = frontier.get()
			x = current.x
			y = current.y
			if current == goal:
				break
			for i in [[x - 1,y],[x + 1,y],[x,y - 1],[x,y + 1]]: #new spots to try
				if (i[0] < 0 or i[1] < 0 or i[0] >= self._map.cols or i[1] >= self._map.rows):
					continue
				next = self._map.grid[i[1]][i[0]]
				if (next.mountain or (not next.discovered and next.isobstacle())):
					continue
				#new_cost = cost_so_far[current] + graph.cost(current, next)
				new_cost = cost_so_far[current] + costFunc(self, current, next)
				if next not in cost_so_far or new_cost < cost_so_far[next]:
					cost_so_far[next] = new_cost
					priority = new_cost + heurFunc(self, goal, next)
					frontier.put(priority, next)
					came_from[next] = current
	
		return came_from, cost_so_far

	def should_proactively_take_cities(self):
		# never take cities proactively in FFA when we're engaging a player
		if self.targetPlayer != -1 and self._map.remainingPlayers > 2:
			return False

		cityLeadWeight = 0
		if self.targetPlayer != -1:
			opp = self._map.players[self.targetPlayer]
			me = self._map.players[self.general.player]
			# don't keep taking cities unless our lead is really huge
			# need 100 army lead for each additional city we want to take
			cityLeadWeight = (me.cityCount - opp.cityCount) * 80

		knowsWhereEnemyGenIs = self.targetPlayer != -1 and self._map.generals[self.targetPlayer] != None
		if knowsWhereEnemyGenIs and self.distance_from_general(self._map.generals[self.targetPlayer]) > 25:
			logging.info("Not proactively taking neutral cities because we know enemy general location and map distance isn't incredibly short")
			return False
		player = self._map.players[self.general.player]
		targetPlayer = self._map.players[self.targetPlayer]
		safeOnStandingArmy = player.standingArmy > targetPlayer.standingArmy * 0.9
		if safeOnStandingArmy and (player.standingArmy > 80 + cityLeadWeight and (self.target_player_gather_path == None or self.target_player_gather_path.length > 25)
					or player.standingArmy > 100 + cityLeadWeight and (self.target_player_gather_path == None or self.target_player_gather_path.length > 22)
					or player.standingArmy > 140 + cityLeadWeight and (self.target_player_gather_path == None or self.target_player_gather_path.length > 19)
					or player.standingArmy > 200 + cityLeadWeight and (self.target_player_gather_path == None or self.target_player_gather_path.length > 17)
					or player.standingArmy > 250 + cityLeadWeight and (self.target_player_gather_path == None or self.target_player_gather_path.length > 15)
					or player.standingArmy > 350 + cityLeadWeight):
			return True
		return False


	def capture_cities(self, targets, negativeTiles):
		maxDist = max(6, len(targets) * 0.4)
		isNeutCity = False
		path = self.find_enemy_city_path(targets, negativeTiles)
		player = self._map.players[self.general.player]
		largestTile = self.general
		for tile in player.tiles:
			if tile.army > largestTile.army:
				largestTile = tile
		targetPlayer = None
		if self.targetPlayer != -1:
			targetPlayer = self._map.players[self.targetPlayer]
		neutDepth = -1
		# we now take cities proactively?
		proactivelyTakeCity = self.should_proactively_take_cities()
		if proactivelyTakeCity:
			if self.threat != None:
				logging.info("Will not proactively take cities due to the existing threat....")
				proactivelyTakeCity = False
			else:
				neutDepth = len(targets) / 3
		if self.targetPlayer == -1 or self._map.remainingPlayers == 2:
			if targetPlayer == None or player.cityCount < targetPlayer.cityCount or proactivelyTakeCity:
				# ? move this logic into proactivelytakecities?
				sqrtFactor = 7
				if targetPlayer == None or player.cityCount < targetPlayer.cityCount or math.sqrt(player.standingArmy) * sqrtFactor < largestTile.army:
					logging.info("..........NO ENEMY CITY PATH FOUND, searching neutral city target.........")
					neutPath = self.find_neutral_city_path(targets, negativeTiles, neutDepth, force = True)
					if neutPath and (path == None or neutPath.length < path.length / 2):
						logging.info("Targeting neutral city.")
						path = neutPath
						isNeutCity = True
				else:
					logging.info("We shouldn't be taking more neutral cities, we're too defenseless	right now. math.sqrt(player.standingArmy) * {}: {} << largestTile.army: {}".format(sqrtFactor, math.sqrt(player.standingArmy) * sqrtFactor, largestTile.army))

		if path != None:
			target = path.tail.tile
			if player.standingArmy <= target.army:
				return (None, None)
			targetArmyGather = 1 + self.enemy_army_near(target, 3) * 3
			targetArmy = 1 + self.enemy_army_near(target, 3) * 2
			searchDist = maxDist
			self.viewInfo.lastEvaluatedGrid[target.x][target.y] = 140
			# gather to the 2 tiles in front of the city
			logging.info("xxxxxxxxx\n  xxxxx\n    SEARCHED AND FOUND NEAREST NEUTRAL / ENEMY CITY {},{} dist {}. Searching {} army dist {}\n  xxxxx\nxxxxxxxx".format(target.x, target.y, path.length, targetArmy, searchDist))
			if path.length > 1:
				# strip the city off
				path = path.get_subsegment(path.length)
			if path.length > 2:
				# strip all but 2 end tiles off
				path = path.get_subsegment(2, end=True)
			if not isNeutCity:
				#targetArmy = max(5, target.army / 5 + self.enemy_army_near(target) * 1.2)
				#if (target.army < 4 and self.enemy_army_near(target) < 10):
				#	targetArmy = self.enemy_army_near(target)
				#searchDist = maxDist // 3 + 1
				targetArmyGather = max(3, target.army / 3 + self.enemy_army_near(target, 4) * 1.2)
				targetArmy = max(2, self.enemy_army_near(target, 2) * 1.1)
				searchDist = maxDist // 2 + 1
			killPath = dest_breadth_first_target(self._map, [target], targetArmy, 0.1, searchDist, negativeTiles, dontEvacCities=True)
			if (killPath != None):
				logging.info("found depth {} dest bfs kill on Neutral or Enemy city {},{} \n{}".format(killPath.length, target.x, target.y, killPath.toString()))
				self.info("City killpath {},{}  setting TreeNodes to None".format(target.x, target.y))
				self.viewInfo.lastEvaluatedGrid[target.x][target.y] = 300
				self.curGather = None
				self.gatherNodes = None
				return (killPath, None)
			else:
				gatherDuration = 25
				if player.tileCount > 125:
					gatherDuration = 50

				gatherDist = 1 + (gatherDuration - self._map.turn % gatherDuration)
				negativeTiles = negativeTiles.copy()
				#negativeTiles.add(self.general)
				logging.info("self.gather_to_target_tile gatherDist {} - targetArmyGather {}".format(gatherDist, targetArmyGather))
				move = self.gather_to_target_tiles(path.tileList, 0.1, gatherDist, targetArmy=targetArmyGather)
				if move != None:
					self.info("Gathering to target city {},{}, proactivelyTakeCity {}, move {}".format(target.x, target.y, proactivelyTakeCity, move.toString()))
					self.viewInfo.lastEvaluatedGrid[target.x][target.y] = 300
					return (None, move)
				
				logging.info("xxxxxxxxx\n  xxxxx\n    GATHERING TO CITY FAILED :( {},{} \n  xxxxx\nxxxxxxxx".format(target.x, target.y))
		else:
			logging.info("xxxxxxxxx\n  xxxxx\n    NO ENEMY CITY FOUND / Neutral city prioritized??? \n  xxxxx\nxxxxxxxx")
		return (None, None)

	def mark_tile(self, tile, alpha = 100):
		self.viewInfo.lastEvaluatedGrid[tile.x][tile.y] = alpha

	def find_neutral_city_path(self, targets, negativeTiles, maxDist = -1, force = False):
		playerArmy = self._map.players[self.general.player].standingArmy
		if maxDist == -1:
			maxDist = 0
			if playerArmy > 1000: # our general has greater than 1000 standing army, capture neutrals up to 0.6* the dist to enemy general
				maxDist = len(targets) * 0.68
			elif playerArmy > 700: # our general has greater than 700 standing army, capture neutrals
				maxDist = len(targets) * 0.6
			elif playerArmy > 600:
				maxDist = len(targets) * 0.5
			elif playerArmy > 500:
				maxDist = len(targets) * 0.47
			else:
				maxDist = len(targets) * 0.45
			maxDist = max(maxDist, 5)
		
		searchLambda = (lambda tile, prioObject: tile.isCity 
						and tile.player == -1 
						and count(tile.adjacents, lambda adjTile: adjTile.player != self.general.player and adjTile.player != -1) == 0
						and count(tile.adjacents, lambda adjTile: not adjTile.discovered) == 0)
		targetPath = self.target_player_gather_path
		if self.target_player_gather_path.length > 10:
			targetPath = self.target_player_gather_path.get_subsegment(self.target_player_gather_path.length / 5)

		path = breadth_first_dynamic(self._map, targetPath.tileSet, searchLambda, 0.1, maxDist, preferNeutral = True)


		if path == None and force:
			enemyPos = self.target_player_gather_path.tail.tile
			myPos = self.general

			idealCity = None
			idealCityClosenessRating = [-15]

			def citySearcher(tile):
				if tile.isCity and tile.player == -1:
					distances = build_distance_map(self._map, [tile])
					distanceRating = distances[enemyPos.x][enemyPos.y] - distances[myPos.x][myPos.y]
					logging.info("evaluating city {} distance comparison (enemy {}, gen {}) - distanceRating {} > idealCityClosenessRating[0] {}: {}".format(tile.toString(), distances[enemyPos.x][enemyPos.y], distances[myPos.x][myPos.y], distanceRating, idealCityClosenessRating[0], distanceRating > idealCityClosenessRating[0]))
					if distanceRating > idealCityClosenessRating[0]:
						idealCityClosenessRating[0] = distanceRating
						idealCity = tile
			breadth_first_foreach(self._map, [myPos], 45, citySearcher, None, lambda tile: not tile.visible, None, self.general.player, noLog = True)
			if idealCity != None:
				logging.info("Forcing a neutral city path, closest to me and furthest from enemy. Chose city {} with rating ".format(idealCity.toString(), idealCityClosenessRating[0]))
				path = self.get_path_to_target(idealCity).get_reversed()
			else:
				logging.info("Forcing a neutral city path but couldn't find one??? :(")
		elif path != None:
			logging.info("Neutral city {} path obtained by normal subsegment distance search.".format(path.tail.tile.toString()))
		return path


	def find_enemy_city_path(self, targets, negativeTiles):
		maxDist = 0
		playerArmy = self._map.players[self.general.player].standingArmy
		ignoreCityArmyThreshold = playerArmy / 3 + 50
		# our general has less than 500 standing army, only target cities owned by our target player
		searchLambda = lambda tile, prioObject: tile.isCity and tile.player == self.targetPlayer and tile.army < ignoreCityArmyThreshold

		if playerArmy > 1000: # our general has greater than 1000 standing army, capture neutrals up to 0.8* the dist to enemy general
			maxDist = len(targets) * 0.4
		elif playerArmy > 700: # our general has greater than 700 standing army, capture neutrals
			maxDist = len(targets) * 0.38
		elif playerArmy > 500:
			maxDist = len(targets) * 0.35
		elif playerArmy > 400:
			maxDist = len(targets) * 0.33
		else:
			maxDist = len(targets) * 0.3
		maxDist = max(maxDist, 5)
		targetPath = self.target_player_gather_path
		if self.target_player_gather_path.length > 6:
			targetPath = self.target_player_gather_path.get_subsegment(self.target_player_gather_path.length / 3)

		path = breadth_first_dynamic(self._map, targetPath.tileSet, searchLambda, 0.1, maxDist, preferNeutral = True)
		if (path != None):
			return path

		if playerArmy > 1000: # our general has greater than 1000 standing army, capture neutrals up to 0.8* the dist to enemy general
			maxDist = len(targets) * 0.6
		elif playerArmy > 700: # our general has greater than 700 standing army, capture neutrals
			maxDist = len(targets) * 0.5
		elif playerArmy > 500:
			maxDist = len(targets) * 0.45
		elif playerArmy > 300:
			maxDist = len(targets) * 0.42
		else:
			maxDist = len(targets) * 0.35
		return breadth_first_dynamic(self._map, targetPath.tileSet, searchLambda, 0.1, maxDist, preferNeutral = True)




	def get_value_per_turn_subsegment(self, path, minFactor = 0.7, minLengthFactor = 0.25):
		pathMoveList = get_tile_list_from_path(path)
		totalCount = len(pathMoveList)
		fullValue = 0
		for tile in pathMoveList:
			if tile.player == self.general.player:
				fullValue += tile.army - 1
		i = 1
		curSum = 0
		maxValuePerTurn = 0
				
		lastValueTile = None
		reversedPath = list(reversed(pathMoveList))
		logging.info("get_value_per_turn_subsegment: len(pathMoveList) == {}".format(len(pathMoveList)))
		logging.info("get_value_per_turn_subsegment input path: {}".format(path.toString()))
		for tile in reversedPath:
			if tile.player == self.general.player:
				curSum += tile.army - 1
			valuePerTurn = curSum / i
			logging.info("  [{}]  {},{}  value per turn was {}".format(i, tile.x, tile.y, "%.1f" % valuePerTurn))
			if valuePerTurn >= maxValuePerTurn and i <= totalCount and i > totalCount * minLengthFactor:
				logging.info(" ![{}]  {},{}  new max!    {} > {}".format(i, tile.x, tile.y, "%.1f" % valuePerTurn, "%.1f" % maxValuePerTurn))
				maxValuePerTurn = valuePerTurn
				lastValueTile = tile
			i += 1

		i = 1
		lastValueIndex = 0
		curSum = 0
		#logging.info("len(reversedPath) {}".format(len(reversedPath)))
		for tile in reversedPath:
			if tile.player == self.general.player:
				curSum += tile.army - 1
			valuePerTurn = curSum / i
			logging.info("  [{}]  {},{}   2nd pass {}".format(i, tile.x, tile.y, "%.1f" % valuePerTurn))
			if valuePerTurn >= maxValuePerTurn * minFactor:
				lastValueIndex = i
				lastValueTile = tile
				logging.info("!![{}]  {},{}    minFactor max   {} >= {}".format(i, tile.x, tile.y, "%.1f" % valuePerTurn, "%.1f" % maxValuePerTurn))
			i += 1
		if lastValueTile:
			logging.info("       -----   ---- lastValueIndex was {} tile {}".format(lastValueIndex, lastValueTile.toString()))
		else:
			logging.warn("No lastValueTile found??? lastValueIndex was {}".format(lastValueIndex))
		newPath = path.get_subsegment(lastValueIndex, end=True)
		newPath.calculate_value(self.general.player)
		return newPath

	#def get_path_list_subsegment(self, pathList, count, end=False):
		

	#def get_path_subsegment(self, path, count, end=False):
	#	pathMoveList = get_tile_list_from_path(path)
		

	#def get_path_subsegment_ratio(self, path, fraction, end=False):
	#	count = 0
	#	node = path
	#	while node != None:
	#		count += 1
	#		node = node.parent
		

	def WeightedBreadthSearch(self, tiles, maxLength=50, maxTime = 0.2, playerSearching = -2, armyAmount = -1, returnAmount = 10, negativeTilesSet = None): 
		loggingOn = False
		frontier = PriorityQueue()
		tileArr = tiles
		tiles = set()
		for tile in tileArr:
			tiles.add(tile)
		Map = self._map
		#logging.info("searching, len tiles {}".format(len(tiles)))
		if (playerSearching == -2):
			playerSearching = Map.player_index
		general = Map.generals[playerSearching]
		generalPlayer = Map.players[playerSearching]
		cityRatio = self.get_city_ratio(playerSearching)


		for tile in tiles:
			if (tile.player == playerSearching):
				if (armyAmount != -1):
					logging.info("\n\n------\nSearching nonstandard army amount {} to {},{}\n--------".format(armyAmount, tile.x, tile.y))
				frontier.put((-10000, PathNode(tile, None, tile.army, 1, 1 if tile.isCity or tile.isGeneral else 0, {(tile.x, tile.y) : 1}), armyAmount, False, 0))
			else:
				isIncrementing = (tile.isCity and tile.player != -1) or tile.isGeneral
				if (isIncrementing):
					logging.info("City or General is in this searches targets: {},{}".format(tile.x, tile.y))
				frontier.put((-10000 * (1 if not tile.isCity else cityRatio), PathNode(tile, None, 0 - tile.army, 1, 1 if tile.isCity or tile.isGeneral else 0, {(tile.x, tile.y) : 1}), 2, isIncrementing, 1))
		leafNodes = PriorityQueue()
		start = time.time()
	

		iter = 1
		undiscoveredTileSearchCount = 0
		score = Map.scores[playerSearching]
		skippedTargetCount = 0
		isHalfTurn = Map.turn > GENERAL_HALF_TURN
		while not frontier.empty(): #make sure there are nodes to check left
		
			if (iter & 32 == 0 and time.time() - start > maxTime):
				break
			
			prioNode = frontier.get() #grab the first nodep
			prioValue = prioNode[0]
			node = prioNode[1]
			enemyTileCount = prioNode[4]
			x = node.tile.x
			y = node.tile.y
			turn = node.turn
			curTile = node.tile

			#Map[x][y]="explored" #make this spot explored so we don't try again
		
			if (turn <= maxLength):
				value = node.value
				# cityCount = node.cityCount
				pathDict = node.pathDict
				#if (loggingOn):
				#	logging.info("{} evaluating {},{}: turn {} army {}".format(prioNode[0], x, y, turn, value))

				targetArmy = prioNode[2]
				isIncrementing = prioNode[3]
		
				neededArmy = targetArmy + 2
				if (isIncrementing):
					neededArmy += (turn / 2)
		
				for candTile in curTile.moveable: #new spots to try
					containsCount = pathDict.get((candTile.x, candTile.y), 0)
					if (containsCount <= 2):						 
						if (candTile.isobstacle() or candTile.mountain or (candTile.isCity and candTile.player == -1)):
							continue

						if (candTile in tiles):
							continue
						self.viewInfo.evaluatedGrid[candTile.x][candTile.y] += 1
						candTileArmyVal = 0
						
						# if we've already visited this tile
						if (containsCount > 0):
							candTileArmyVal = value
					
						# if this tile is recommended not to be moved
						elif (negativeTilesSet != None and candTile in negativeTilesSet):
							#if (loggingOn):
							#logging.info("Tile {},{} value calculated as 0 because it is in negativeTileSet".format(candTile.x, candTile.y))
							candTileArmyVal = value
					
						# if this tile is owned by the current player
						elif candTile.player == playerSearching:
							candTileArmyVal = value + (candTile.army - 1)
							if (candTile.isGeneral and isHalfTurn):
								if playerSearching == Map.player_index:
									if (not self.general_move_safe(candTile)):
										#logging.info("Bot is in danger. Refusing to use general tile altogether.")
										continue
									candTileArmyVal -= candTile.army / 2
										
						
						# if this is an undiscovered neutral tile
						elif not candTile.discovered: 
							if (candTile.isobstacle()):
								candTileArmyVal = value - 100
							else:
								candTileArmyVal = value - (candTile.army + 1)
							undiscoveredTileSearchCount += 1
						else: 
							candTileArmyVal = value - (candTile.army + 1)
						weightedCandTileArmyVal = candTileArmyVal
						if (targetArmy > 0 and candTileArmyVal > neededArmy):
							#weightedCandTileArmyVal = 2 * (candTileArmyVal - neededArmy) / 3 + neededArmy
							weightedCandTileArmyVal = pow(candTileArmyVal - neededArmy, 0.9) + neededArmy
						#paths starting through enemy territory carry a zero weight until troops are found, causing this to degenerate into breadth first search until we start collecting army (due to subtracting turn)
						#weight paths closer to king
						if (weightedCandTileArmyVal <= -5 and general != None):
							distToGen = self.distance_from_general(candTile)
							weightedCandTileArmyVal = weightedCandTileArmyVal - (distToGen / 5.0)
							#if (loggingOn):
							#	logging.info("{},{} weightedCandTileArmyVal <= 0, weighted: {}".format(candTile.x, candTile.y, weightedCandTileArmyVal))
						#elif(loggingOn):
						#	logging.info("{},{} weightedCandTileArmyVal > 0, weighted: {}".format(candTile.x, candTile.y, weightedCandTileArmyVal))
														
						
						# candTileCityCount = cityCount if containsCount > 0 or not (candTile.isCity and candTile.player != -1) else cityCount + 1
						candPathDict = pathDict.copy()
						candPathDict[(candTile.x, candTile.y)] = containsCount + 1
						candTileEnemyTileCount = enemyTileCount	
						if containsCount == 0 and ((candTile.player != self._map.player_index and candTile.player != -1)):
							candTileEnemyTileCount += 1
							if (candTile.isCity and containsCount == 0):
								candTileEnemyTileCount += (3 * cityRatio)
						tileWeight = 0
						#if (maximizeTurns):
						#	weightedCandTileArmyVal - turn - score['total'] / 750.0 * pow(turn, 1.5)
						#else:
						# tileWeight = candTileEnemyTileCount + (candTileEnemyTileCount / 4.0 + candTileCityCount * 2) * weightedCandTileArmyVal + 14 * weightedCandTileArmyVal / turn - turn - (score['total'] / 900.0) * pow(turn, 1.33)
						tileWeight = candTileEnemyTileCount + 14 * weightedCandTileArmyVal / turn - 2 * turn - (score['total'] / 900.0) * pow(turn, 1.1)
							#tileWeight = (candTileCityCount + 2) * weightedCandTileArmyVal + 13 * weightedCandTileArmyVal / turn - turn - score['total'] / 750.0 * pow(turn, 1.5)
						#if (loggingOn): logging.info("{},{} fullWeight: {}".format(candTile.x, candTile.y, tileWeight))
						frontier.put((0 - tileWeight, PathNode(candTile, node, candTileArmyVal, turn + 1, 0, candPathDict), targetArmy, isIncrementing, candTileEnemyTileCount))#create the new spot, with node as the parent
					#elif(loggingOn):
					#	logging.info("{},{} already showed up twice".format(x, y))
			if (curTile.player == playerSearching and curTile.army > 1 and targetArmy < value and turn > 1):
				leafNodes.put(prioNode)
			iter += 1
		best = []
		for i in range(returnAmount):
			if (leafNodes.empty()):
				break
			node = leafNodes.get()
			best.append(node)
		
		if (len(best) > 0):
			logging.info("best: " + str(best[0][0]))
		end = time.time()
		logging.info("SEARCH ITERATIONS {}, TARGET SKIPPED {}, DURATION: {:.2f}".format(iter, skippedTargetCount, end - start))
		#if (undiscoveredTileSearchCount > 0):
		#	logging.info("~~evaluated undiscovered tiles during search: " + str(undiscoveredTileSearchCount))
		newBest = []
		for i, oldpath in enumerate(best):
			oldPathNode = oldpath[1]
			newPath = Path(oldPathNode.value)
			while oldPathNode != None:
				newPath.add_next(oldPathNode.tile)
				oldPathNode = oldPathNode.parent
			newBest.append(newPath)			
			logging.info("newBest {}:  {}\n{}".format(i, newPath.value, newPath.toString()))

		return newBest



	def get_city_ratio(self, player_index):
		enemyCityMax = 0
		generalPlayer = self._map.players[player_index]
		for player in self._map.players:
			if player.index != player_index and not player.dead:
				enemyCityMax = max(player.cityCount, enemyCityMax)
		cityRatio = max(1.0, 1.0 * enemyCityMax / generalPlayer.cityCount)


		otherPlayerIncomeMax = 0
		playerIncome = generalPlayer.tileCount + 25 * generalPlayer.cityCount
		for player in self._map.players:
			if player.index != player_index and not player.dead:
				otherPlayerIncomeMax = max(player.tileCount + 25 * player.cityCount, otherPlayerIncomeMax)
		incomeRatio = max(1.0, 1.0 * otherPlayerIncomeMax / playerIncome)
		tileCount = max(generalPlayer.tileCount, 1)
		theMax = max(cityRatio, incomeRatio)
		theMax = theMax * (self._map.remainingPlayers / 2.0)
		theMax = min(1.0 * generalPlayer.score / tileCount, theMax)
		logging.info("city ratio: {}".format(theMax))
		return theMax


	def calculate_general_danger(self):
		depth = len(self.target_player_gather_targets) - 3
		if (depth < 7):
			depth = 10
		self.dangerAnalyzer.analyze(self.general, depth)


	def general_min_army_allowable(self):
		if (self._minAllowableArmy != -1):
			return self._minAllowableArmy
		general = self._map.generals[self._map.player_index]
		if (general == None):
			return -1
		maxPlayerPotentialArmy = 0
		generalScore = self._map.scores[self._map.player_index]
		generalPlayer = self._map.players[self.general.player]
		
		realDanger = False
		dangerousPath = None
		dangerValue = -1
		self.allIn = False
		for player in self._map.players:
			if player == generalPlayer or player == None or player.dead:
				continue
			#give up if we're massively losing
			if self._map.remainingPlayers == 2:
				if self._map.turn > 150 and player.tileCount + 35 * player.cityCount > generalPlayer.tileCount * 1.35 + 5 + 35 * generalPlayer.cityCount and player.standingArmy > generalPlayer.standingArmy * 1.25 + 5:
					self.allIn = True
					self.all_in_counter = 200
				elif self._map.turn > 50 and player.tileCount + 35 * player.cityCount > generalPlayer.tileCount * 1.1 + (37 * generalPlayer.cityCount):
					self.all_in_counter += 1
				else:
					self.all_in_counter = 0
				if (self.all_in_counter > generalPlayer.tileCount):
					self.allIn = True
				if player.tileCount + 35 * player.cityCount > generalPlayer.tileCount * 1.6 + 5 + 35 * generalPlayer.cityCount and player.score > generalPlayer.score * 1.7 + 5:
					self.giving_up_counter += 1
					logging.info("~ ~ ~ ~ ~ ~ ~ giving_up_counter: {}. Player {} with {} tiles and {} army.".format(self.giving_up_counter, player.index, player.tileCount, player.score))
					if self.giving_up_counter > generalPlayer.tileCount + 10:
						logging.info("~ ~ ~ ~ ~ ~ ~ giving up due to player {} with {} tiles and {} army.".format(player.index, player.tileCount, player.score))
						time.sleep(2)
						self._map.result = False
						self._map.complete = True
				else:
					self.giving_up_counter = 0
			
		self._minAllowableArmy = 1
		return 1
		
	def is_move_safe_valid(self, move, allowNonKill = False):
		if (move == None):
			return False
		if (move.source == self.general):
			return self.general_move_safe(move.dest)
		if (move.source.player != move.dest.player and move.source.army - 2 < move.dest.army and not allowNonKill):
			logging.info("{},{} -> {},{} was not a move that killed the dest tile".format(move.source.x, move.source.y, move.dest.x, move.dest.y))
			return False
		return True
	

	def general_move_safe(self, target, move_half=False):
		if (self._map.turn - self.lastGeneralGatherTurn < 4):
			# logging.info("not moving general tile because he just gathered")
			return False
		dangerTiles = self.get_danger_tiles(move_half)
		
		general = self._map.generals[self._map.player_index]
		minArmy = self.general_min_army_allowable()

		genArmyAfterMove = general.army / 2 
		if not move_half and (self._map.turn <= GENERAL_HALF_TURN):
			genArmyAfterMove = 1

		safeSoFar = True
		if (len(dangerTiles) > 1):
			safeSoFar = False
		elif (len(dangerTiles) == 0 and genArmyAfterMove < minArmy and self._map.remainingPlayers == 2):
			return False

		for dangerTile in dangerTiles:
			if not (target.x  == dangerTile.x and target.y == dangerTile.y):
				safeSoFar = False
				logging.info("Enemy tile at {},{} with value {} is preventing king moves.".format(dangerTile.x, dangerTile.y, dangerTile.army))
			else:
				logging.info("\n~~~Allowed otherwise-illegal king move to attack the dangerous tile at {},{} with value {}.".format(dangerTile.x, dangerTile.y, dangerTile.army))
		return safeSoFar
			
	def get_danger_tiles(self, move_half=False):
		general = self._map.generals[self._map.player_index]
		genArmyAfterMove = general.army / 2 
		if not move_half and (self._map.turn <= GENERAL_HALF_TURN):
			genArmyAfterMove = 1
		dangerTiles = set()
		toCheck = []
		if (general.left != None and general.left.left != None):
			toCheck.append(general.left.left)
		if (general.bottom != None and general.bottom.bottom != None):
			toCheck.append(general.bottom.bottom)
		if (general.top != None and general.top.top != None):
			toCheck.append(general.top.top)
		if (general.right != None and general.right.right != None):
			toCheck.append(general.right.right)

		for tile in toCheck:
			if (tile != None and tile.player != general.player and tile.player != -1 and tile.army - 4 > genArmyAfterMove):					
				dangerTiles.add(tile)


		toCheck = []
		for tile in general.adjacents:
			toCheck.append(tile)

		for tile in toCheck:
			if (tile != None and tile.player != general.player and tile.player != -1 and tile.army - 1 > genArmyAfterMove):
				dangerTiles.add(tile)
		return dangerTiles
		


	def find_target_gather_leaves(self, allLeaves=None):
		self.leafValueGrid = [[None for x in range(self._map.rows)] for y in range(self._map.cols)]
		general = self._map.generals[self._map.player_index]
		mapMid = (self._map.cols / 2, self._map.rows / 2)
		maxMoves = PriorityQueue()
		player = self._map.players[self.general.player]
		cityRatio = self.get_city_ratio(self._map.player_index)
		logging.info("CityRatio: {}".format(cityRatio))
		genArmy = self.general.army
		if (self.general.army // 2 > self.general_min_army_allowable()):
			genArmy = self.general.army // 2
		standingArmyWeighted = (self._map.players[self.general.player].standingArmy - genArmy) * 0.85
		for leaf in allLeaves:
			#if (len(maxMoves) == 0 or leaf.source.army - leaf.dest.army >= maxMoves[0].source.army - maxMoves[0].dest.army):
			leafValue = 10 + leaf.dest.army

			midWeight = pow(pow(abs(leaf.dest.x - mapMid[0]), 2) + pow(abs(leaf.dest.y - mapMid[1]), 2), 0.5) - (self._map.cols + self._map.rows) / 6
			if (midWeight < 0):
				midWeight = 0
			
			if (self._map.remainingPlayers > 3):
				leafValue += midWeight 
			else:
				leafValue -= midWeight


			if (leaf.dest.isCity and leaf.dest.player == -1):
			#if (leaf.dest.isCity and leaf.dest.player == -1 and ((self._map.turn < 150 and self._map.remainingPlayers <= 3) or self._map.turn < 100 or 50 > standingArmyWeighted)):
				#logging.info("skipped cities")
				curVal = self.leafValueGrid[leaf.dest.x][leaf.dest.y]
				if (curVal == None):
					self.leafValueGrid[leaf.dest.x][leaf.dest.y] = -1000000
				continue

			distToGen = max(self.distance_from_general(leaf.dest), 3)
			leafValue = leafValue + 600 / distToGen
			if (leaf.dest.isCity and leaf.dest.player == -1):
				leafValue = leafValue + (350 - distToGen * 15) * cityRatio
			
			#if (leaf.dest.player != -1 or leaf.dest.isCity):
			if (leaf.dest.player != -1 and leaf.dest.player != self.targetPlayer and self.distance_from_general(leaf.dest) > len(self.target_player_gather_targets) // 3):
				# skip non-close tiles owned by enemies who are not the current target.
				# TODO support agrod enemies who are actively attacking us despite not being the current target. Also improve reprioritization for players aggroing us.
				self.viewInfo.lastEvaluatedGrid[leaf.dest.x][leaf.dest.y] = 200
				self.leafValueGrid[leaf.dest.x][leaf.dest.y] = -1000000
				continue
			elif (leaf.dest.player == self.targetPlayer and self._map.turn < 50):
				leafValue *= 0.3
			elif (leaf.dest.player == self.targetPlayer and self._map.turn < 100):
				leafValue *= 5.0 / min(self._map.remainingPlayers, 3)
			elif (leaf.dest.player == self.targetPlayer and self._map.turn >= 100):
				leafValue *= 8.0 / min(self._map.remainingPlayers, 4)
			elif (leaf.dest.player != -1):
				leafValue = leafValue * 2.0 / min(4, max(self._map.remainingPlayers, 2))
			if (leaf.dest.isCity):
				cityRatActive = cityRatio
				if (leaf.dest.player == -1):
					inEnemyTerr = False
					for adj in leaf.dest.adjacents:
						if (adj.player != -1 and adj.player != self._map.player_index):
							inEnemyTerr = True
					if inEnemyTerr:
						cityRatActive = cityRatActive * 0.7
				distToGen = self.distance_from_general(leaf.dest)
				distToEnemy = self.getDistToEnemy(leaf.dest)
				leafValue *= 3
				if (distToEnemy > 0):
					distWeight = max(1.0, pow(distToGen * 2, 1.1) - pow((2 + distToEnemy) * 2.2, 1.4) / 4.0)
					logging.info("distWeight {},{}: {} ({}, {})".format(leaf.dest.x, leaf.dest.y, distWeight, distToGen, distToEnemy))
					leafValue = ((leafValue) / distWeight) * cityRatActive
				else:
					leafValue = ((leafValue) / pow(distToGen / 2, 1.4)) * cityRatActive 
				#leafValue *= 1.0

			curVal = self.leafValueGrid[leaf.dest.x][leaf.dest.y]
			if (curVal == None or curVal < leafValue):
				self.leafValueGrid[leaf.dest.x][leaf.dest.y] = leafValue
			leafValue = 0 - leafValue
			maxMoves.put((leafValue, leaf))
			
		moves = []
		addedSet = set()
		if (not maxMoves.empty()):
			moveNode = maxMoves.get()
			maxMove = moveNode[0]
			leeway = maxMove * 0.90
			#always return at least 1 potential targets
			# less than because the heuristic value goes negative for good values
			while moveNode[0] < leeway or len(moves) < 1:
				moveTuple = (moveNode[1].dest.x, moveNode[1].dest.y)
				if not moveTuple in addedSet:
					tile = moveNode[1].dest
					tileInfo = "{}, player {}".format(tile.army, tile.player)
					if (tile.isCity):
						tileInfo += ", city"
					if (tile.isGeneral):
						tileInfo += ", general"

					logging.info("TargetGather including {},{} [{}] ({})".format(tile.x, tile.y, moveNode[0], tileInfo))
					addedSet.add(moveTuple)
					moves.append(moveNode[1])
				if (maxMoves.empty()):
					break
				moveNode = maxMoves.get()
		return moves
	

	def winning_on_economy(self, byExtraRatio = 0, cityValue = 30):
		if self.targetPlayer == -1:
			return True
		targetPlayer = self._map.players[self.targetPlayer]
		generalPlayer = self._map.players[self.general.player]

		playerEconValue = generalPlayer.tileCount * (1 + byExtraRatio) + generalPlayer.cityCount * cityValue
		oppEconValue = targetPlayer.tileCount + targetPlayer.cityCount * cityValue
		return playerEconValue >= oppEconValue


	def winning_on_army(self, byExtraRatio = 0, useFullArmy = False):
		if self.targetPlayer == -1:
			return True
		targetPlayer = self._map.players[self.targetPlayer]
		generalPlayer = self._map.players[self.general.player]

		targetArmy = targetPlayer.standingArmy
		playerArmy = generalPlayer.standingArmy
		if useFullArmy:
			targetArmy = targetPlayer.score
			playerArmy = generalPlayer.score
		winningOnArmy = playerArmy * (1 + byExtraRatio) >= targetArmy
		logging.info("winning_on_army: playerArmy {} (weighted {:.1f}) >= targetArmy {} ?  {}".format(playerArmy, playerArmy * (1 + byExtraRatio), targetArmy, winningOnArmy))
		return winningOnArmy


	def worth_attacking_target(self):
		timingFactor = 1.0
		if self._map.turn < 50:
			logging.info("Not worth attacking, turn < 50")
			return False

		
		knowsWhereEnemyGeneralIs = self.targetPlayer != -1 and self._map.generals[self.targetPlayer] != None

		player = self._map.players[self.general.player]
		targetPlayer = self._map.players[self.targetPlayer]
		
		# if 20% ahead on economy and not 10% ahead on standing army, just gather, dont attack....
		wPStanding = player.standingArmy * 0.9
		oppStanding = targetPlayer.standingArmy
		wPIncome = player.tileCount + player.cityCount * 30
		wOppIncome = targetPlayer.tileCount * 1.2 + targetPlayer.cityCount * 35 + 5
		if self._map.turn >= 100 and wPStanding < oppStanding and wPIncome > wOppIncome:
			logging.info("NOT WORTH ATTACKING TARGET BECAUSE wPStanding < oppStanding and wPIncome > wOppIncome")
			logging.info("NOT WORTH ATTACKING TARGET BECAUSE {}     <  {}        and   {} >   {}".format(wPStanding, oppStanding, wPIncome, wOppIncome))
			return False

		#factor in some time for exploring after the attack, + 1 * 1.1
		if self.target_player_gather_path == None:
			logging.info("ELIM due to no path")
			return False
		value = get_player_army_amount_on_path(self.target_player_gather_path, self._map.player_index, 0, self.target_player_gather_path.length)
		logging.info("Player army amount on path: {}   TARGET PLAYER PATH IS REVERSED ? {}".format(value, self.target_player_gather_path.toString()))
		subsegment = self.get_value_per_turn_subsegment(self.target_player_gather_path)
		logging.info("value per turn subsegment = {}".format(subsegment.toString()))
		subsegmentTargets = get_tile_set_from_path(subsegment)

		lengthRatio = len(self.target_player_gather_targets) / max(1, len(subsegmentTargets))

		sqrtVal = 0
		if (value > 0):
			sqrtVal = value ** 0.5
			logging.info("value ** 0.5 -> sqrtVal {}".format(sqrtVal))
		if player.tileCount < 60:
			sqrtVal = value / 2.0
			logging.info("value / 2.3  -> sqrtVal {}".format(sqrtVal))
		sqrtVal = min(20, sqrtVal)
		
		dist = int((len(subsegmentTargets)) + sqrtVal)
		factorTurns = 50
		if dist > 25 or player.tileCount > 110:
			factorTurns = 100
		turnOffset = self._map.turn + dist
		factorScale = turnOffset % factorTurns
		if (factorScale < factorTurns / 2):
			logging.info("factorScale < factorTurns / 2")
			timingFactor = scale(factorScale, 0, factorTurns / 2, 0, 0.40)
		else:
			logging.info("factorScale >>>>>>>>> factorTurns / 2")
			timingFactor = scale(factorScale, factorTurns / 2, factorTurns, 0.30, 0)

		if self.lastTimingFactor != -1 and self.lastTimingFactor < timingFactor:
			logging.info("  ~~~  ---  ~~~  lastTimingFactor {} <<<< timingFactor {}".format("%.3f" % self.lastTimingFactor, "%.3f" % timingFactor))
			factor = self.lastTimingFactor
			self.lastTimingFactor = timingFactor
			timingFactor = factor
		self.lastTimingTurn = self._map.turn

		if player.tileCount > 200:
			#timing no longer matters after a certain point?
			timingFactor = 0.1

		# if we are already attacking, keep attacking
		alreadyAttacking = False
		if (self._map.turn - 3 < self.lastTargetAttackTurn):
			timingFactor *= 0.3 # 0.3
			alreadyAttacking = True
			logging.info("already attacking :)")

		if player.standingArmy < 5 and timingFactor > 0.1:
			return False
		logging.info("OoOoOoOoOoOoOoOoOoOoOoOoOoOoOoOoOoOoO\n   {}  oOo  timingFactor {},  factorTurns {},  turnOffset {},  factorScale {},  sqrtVal {},  dist {}".format(self._map.turn, "%.3f" % timingFactor, factorTurns, turnOffset, factorScale, "%.1f" % sqrtVal, dist))
		
		playerEffectiveStandingArmy = player.standingArmy - 9 * (player.cityCount - 1)
		if self.target_player_gather_path.length < 2:
			logging.info("ELIM due to path length {}".format(self.target_player_gather_path.length))
			return False

		targetPlayerArmyThreshold = self._map.players[self.targetPlayer].standingArmy + dist / 2
		if (player.standingArmy < 70):
			timingFactor *= 2
			timingFactor = timingFactor ** 2
			if (knowsWhereEnemyGeneralIs):
				timingFactor += 0.05
			rawNeeded = playerEffectiveStandingArmy * 0.62 + playerEffectiveStandingArmy * timingFactor
			rawNeededScaled = rawNeeded * lengthRatio
			neededVal = min(targetPlayerArmyThreshold, rawNeededScaled)
			if alreadyAttacking:
				neededVal *= 0.75
			logging.info("    --   playerEffectiveStandingArmy: {},  NEEDEDVAL: {},            VALUE: {}".format(playerEffectiveStandingArmy, "%.1f" % neededVal, value))
			logging.info("    --                                     rawNeeded: {},  rawNeededScaled: {},  lengthRatio: {}, targetPlayerArmyThreshold: {}".format("%.1f" % rawNeeded, "%.1f" % rawNeededScaled, "%.1f" % lengthRatio, "%.1f" % targetPlayerArmyThreshold))
			return value > neededVal
		else:
			if (knowsWhereEnemyGeneralIs):
				timingFactor *= 1.5
				timingFactor += 0.03
			expBase = playerEffectiveStandingArmy * 0.15
			exp = 0.68 + timingFactor
			expValue = playerEffectiveStandingArmy ** exp
			rawNeeded = expBase + expValue
			rawNeededScaled = rawNeeded * lengthRatio
			neededVal = min(targetPlayerArmyThreshold, rawNeededScaled)
			if alreadyAttacking:
				neededVal *= 0.75
			logging.info("    --    playerEffectiveStandingArmy: {},  NEEDEDVAL: {},            VALUE: {},      expBase: {},   exp: {},       expValue: {}".format(playerEffectiveStandingArmy, "%.1f" % neededVal, value, "%.2f" % expBase, "%.2f" % exp, "%.2f" % expValue))
			logging.info("    --                                      rawNeeded: {},  rawNeededScaled: {},  lengthRatio: {}, targetPlayerArmyThreshold: {}".format("%.1f" % rawNeeded, "%.1f" % rawNeededScaled, "%.1f" % lengthRatio, "%.1f" % targetPlayerArmyThreshold))
			return value >= neededVal


	def get_target_army_inc_adjacent_enemy(self, tile):
		sumAdj = 0
		for adj in tile.adjacents:
			if (adj.player != self._map.player_index and adj.player != -1):
				sumAdj += adj.army
		armyToSearch = sumAdj
		if (tile.army > 5 and tile.player != self._map.player_index):
			armyToSearch += tile.army / 2
		return armyToSearch


	def find_leaf_move(self, allLeaves):
		leafMoves = self.find_greatest_expansion_leaves(allLeaves)
		if (len(leafMoves) > 0):
			#self.curPath = None
			#self.curPathPrio = -1
			move = leafMoves[0]
			i = 0
			valid = True
			while move.source.isGeneral and not self.general_move_safe(move.dest):
				if (self.general_move_safe(move.dest, True)):
					move.move_half = True
					break
				else:	
					move = random.choice(leafMoves)
					i += 1
					if i > 10:
						valid = False
						break

			if valid:
				self.curPath = None
				self.curPathPrio = -1
				return move
		return None
		
	def find_greatest_expansion_leaves(self, allLeaves=None):

		general = self._map.generals[self._map.player_index]
		mapMid = (self._map.cols / 2, self._map.rows / 2)
		maxMoves = []
		moveHalfMin = 8
		moveHalfMax = self._map.players[general.player].tileCount / 3

		includeNeutralTiles = True
		botPlayer = self._map.players[self.general.player]
		if self.targetPlayer >= 0 and botPlayer.tileCount > 1.25 * self._map.players[self.targetPlayer].tileCount + 4:
			includeNeutralTiles = False
			logging.info("SKIPPING NEUTRAL TILES ON SINGLE MOVE EXPANSION LEAVES!")

		for leaf in allLeaves:
			#if (len(maxMoves) == 0 or leaf.source.army - leaf.dest.army >= maxMoves[0].source.army - maxMoves[0].dest.army):
			if (leaf.source.army - leaf.dest.army <= 1):
				continue
			leafValue = leaf.source.army - leaf.dest.army - 1
			moveHalf = False
			armyAmount = leaf.source.army
			exploratory = False


			if (leaf.source.army > moveHalfMin and leaf.source.army <= moveHalfMax):
				possibleExpansions = 0
				nearbyFriendlyCities = 0
				for adj in leaf.source.adjacents:
					if (adj.isCity and adj.player == general.player):
						nearbyFriendlyCities += 1
				for adj in leaf.source.moveable:
					if (adj.player != general.player and adj.player != -1 and adj.army * 2 < leaf.source.army - 1):
						possibleExpansions += 1

				numNotVisible = 0
				for destAdj in leaf.dest.moveable:
					if (not destAdj.discovered):
						exploratory = True
					if (not destAdj.visible):
						numNotVisible += 1

				if (not exploratory) and possibleExpansions > 1 and numNotVisible == 0:
					moveHalf = True
					armyAmount = int(leaf.source.army / 2)
					leafValue = (leafValue / 2) - 1
				if (nearbyFriendlyCities > 0):
					moveHalf = True
					armyAmount = int(leaf.source.army / 2)
					leafValue = (leafValue / 2) - 3

			if (leaf.dest.player != -1):
				if (self.distance_from_general(leaf.dest) < 11):
					# logging.info("Close to our general, attack larger tiles")
					leafValue = armyAmount + leaf.dest.army

			midWeight = pow(pow(abs(leaf.dest.x - mapMid[0]), 2) + pow(abs(leaf.dest.y - mapMid[1]), 2), 0.5) - (self._map.cols + self._map.rows) / 6
			if (midWeight < 0):
				midWeight = 0
			
			if (self._map.remainingPlayers > 4 and leaf.dest.player == -1):
				leafValue += midWeight * self._map.remainingPlayers / 3
			elif (self._map.remainingPlayers < 3):
				leafValue -= midWeight / 2

			if self._map.remainingPlayers <= 3:
				for tile in leaf.dest.adjacents:
					if not tile.discovered:
						if not tile.isobstacle():
							leafValue += 5
							armyAmount = leaf.source.army
						else:
							leafValue += 0.1

					elif not tile.mountain and not tile.player == general.player:
						leafValue -= 0.5
					elif tile.isCity:
						leafValue += 2
						leafValue *= 4

					if self._map.remainingPlayers <= 3 and not tile.isvisible() and not tile.mountain and not tile.isobstacle():
						leafValue += 1

			#midWeight = pow(pow(abs(leaf.dest.x - mapMid[0]), 2) + pow(abs(leaf.dest.y - mapMid[1]), 2), 0.5) - (self._map.cols + self._map.rows) / 6
			#if (midWeight < 0):
			#	midWeight = 0
			if (leaf.dest.player != -1 and leaf.dest.player != self.targetPlayer and self.distance_from_general(leaf.dest) > len(self.target_player_gather_targets) // 3):
				# skip non-close tiles owned by enemies who are not the current target.
				# TODO support agro'd enemies who are actively attacking us despite not being the current target. Also improve reprioritization for players aggroing us.
				self.viewInfo.lastEvaluatedGrid[leaf.dest.x][leaf.dest.y] = 200
				self.leafValueGrid[leaf.dest.x][leaf.dest.y] = -1000000
				continue
			if leaf.dest.player != self.targetPlayer and (not includeNeutralTiles and leaf.dest.player == -1):
				continue
			if (leaf.source.isCity and not leaf.dest.isCity):
				if armyAmount < leaf.dest.army + 1:
					continue
				nearbyEnemyTiles = 0
				nearbyLargeEnemyTiles = 0
				maxNearbyTile = 0
				for adj in leaf.source.adjacents:
					if (adj.player != self._map.player_index and adj.player != -1 and adj != leaf.dest):
						nearbyEnemyTiles += 1
						if (adj.army > 5):
							nearbyLargeEnemyTiles += 1
							maxNearbyTile = max(maxNearbyTile, adj.army)

				if (nearbyEnemyTiles > 3):
					continue
				if (nearbyEnemyTiles > 1):
					moveHalf = True
					armyAmount = int(leaf.source.army / 2)
				if nearbyLargeEnemyTiles > 0 and maxNearbyTile < leaf.source.army < 2:
					moveHalf = True
					armyAmount = int(leaf.source.army / 2)	
			if (leaf.source.isGeneral and not self.general_move_safe(leaf.dest)):
				continue
			if (self.dangerAnalyzer.anyThreat and leaf.dest.player == -1):
				continue
			# if (leaf.dest.isCity and leaf.dest.player == -1):
			# 	continue
			if (leaf.dest.player != -1):
				leafValue = leafValue * 4 
				if not leaf.dest.player == self.targetPlayer and not leaf.dest.isCity:
					leafValue = leafValue / self._map.remainingPlayers
				if (leaf.dest.isGeneral):
					leafValue = 1000000000
			if (leaf.dest.isCity and 1.0 * leaf.source.army / max(1, leaf.dest.army) > 2.5): 
				moveHalf = False
				armyAmount = leaf.source.army
				if (leaf.dest.player == -1):
					notInEnemyTerr = True
					for adj in leaf.dest.adjacents:
						if (not adj.discovered and not adj.isobstacle()) or (adj.player != -1 and adj.player != self._map.player_index):
							notInEnemyTerr = False
					if (notInEnemyTerr):
						leafValue += 200
				else:
					leafValue += 10000
				#if (self._map.turn > 100):
				#	leafValue += (abs(leaf.dest.x - general.x) + abs(leaf.dest.y - general.y)) / 5
			if self._map.turn < 50 and leaf.source.isGeneral:
				leafValue = leafValue / 30
			leaf.move_half = moveHalf
			if (len(maxMoves) > 0 and maxMoves[0][0] < leafValue):
				maxMoves = []
			if (len(maxMoves) == 0 or maxMoves[0][0] == leafValue):
				maxMoves.append((leafValue, leaf))
		moves = []
		for moveTuple in maxMoves:
			moves.append(moveTuple[1])
		return moves

	def getDistToEnemy(self, tile):
		dist = 1000
		for i in range(len(self._map.generals)):
			gen = self._map.generals[i]
			genDist = 0
			if (gen != None):
				genDist = self.euclidDist(gen.x, gen.y, tile.x, tile.y)
			elif self.generalApproximations[i][2] > 0:
				genDist = self.euclidDist(self.generalApproximations[i][0], self.generalApproximations[i][1], tile.x, tile.y)
			
			if (genDist < dist):
				dist = genDist
		return dist


	# attempt to get this to a* able?
	'''
	f(n) = node priority in queue
	g(n) = cost so far
	h(n) = estimated cost after choosing next node
	priority (f(n)) = g(n) + h(n)
	what is our cost?
	goal is no remaining moves with this army
		h(n) estimated cost to reach goal: amount of army remaining on tile
			- targets high army enemy tiles first?
		g(n) moves used so far
	add value function which simply evaluates the paths for best path


	what about estimated cost is distance to 

	'''



	def get_optimal_expansion(self, turns, negativeTiles = None):
		logging.info("\n\nAttempting Optimal Expansion (tm):\n")
		startTime = time.time()
		generalPlayer = self._map.players[self.general.player]
		searchingPlayer = self.general.player
		if negativeTiles == None:
			negativeTiles = set()
		else:
			negativeTiles = negativeTiles.copy()
		for tile in negativeTiles:
			logging.info("negativeTile: {}".format(tile.toString()))


		distSource = [self.general]
		if self.target_player_gather_path != None:
			distSource = self.target_player_gather_path.tileList
		distMap = build_distance_map(self._map, distSource)
		
		
		#skipFunc(next, nextVal). Not sure why this is 0 instead of 1, but 1 breaks it. I guess the 1 is already subtracted
		def skip_after_out_of_army(nextTile, nextVal):
			wastedMoves, pathPriorityDivided, armyRemaining, enemyTiles, neutralTiles, pathPriority, distSoFar, tileSetSoFar, adjacentSetSoFar = nextVal
			# we can't take enemy tiles at 0 army, need 1 army
			offset = 0
			if nextTile.player != -1:
				offset = 1
			if armyRemaining <= offset:
				return True
			return False


		def value_priority_army_dist(currentTile, priorityObject):
			wastedMoves, pathPriorityDivided, armyRemaining, enemyTiles, neutralTiles, pathPriority, distSoFar, tileSetSoFar, adjacentSetSoFar = priorityObject
			# negative these back to positive
			posPathPrio = 0-pathPriorityDivided
			#return (posPathPrio, 0-armyRemaining, distSoFar)
			return (0-(enemyTiles*2 + neutralTiles) / (max(1, distSoFar)), 0-enemyTiles / (max(1, distSoFar)), posPathPrio, distSoFar)


		def a_starey_value_priority_army_dist(currentTile, priorityObject):
			wastedMoves, pathPriorityDivided, armyRemaining, enemyTiles, neutralTiles, pathPriority, distSoFar, tileSetSoFar, adjacentSetSoFar = priorityObject
			# negative these back to positive
			posPathPrio = 0-pathPriorityDivided
			#return (posPathPrio, 0-armyRemaining, distSoFar)
			return (0-(enemyTiles*2 + neutralTiles) / (max(1, distSoFar)), 0-enemyTiles / (max(1, distSoFar)), posPathPrio, distSoFar)


		
		def default_priority_func(nextTile, currentPriorityObject):
			wastedMoves, pathPriorityDivided, armyRemaining, enemyTiles, neutralTiles, pathPriority, distSoFar, tileSetSoFar, adjacentSetSoFar = currentPriorityObject
			nextTileSet = tileSetSoFar.copy()
			distSoFar += 1
			addedPriority = -7 - max(3, distMap[nextTile.x][nextTile.y] / 4)
			if nextTile not in nextTileSet:
				armyRemaining -= 1
				releventAdjacents = where(nextTile.adjacents, lambda adjTile: adjTile not in adjacentSetSoFar and adjTile not in tileSetSoFar)
				if negativeTiles == None or (nextTile not in negativeTiles):
					if (searchingPlayer == nextTile.player):
						armyRemaining += nextTile.army
					else:
						armyRemaining -= nextTile.army
				nextTileSet.add(nextTile)
				# enemytiles or enemyterritory undiscovered tiles
				if nextTile.player == self.targetPlayer or (not nextTile.visible and self.territories.territoryMap[nextTile.x][nextTile.y] == self.targetPlayer):
					enemyTiles -= 1
					# points for capping target tiles
					addedPriority += 6
					# points for locking all nearby enemy tiles down
					numEnemyNear = count(nextTile.adjacents, lambda adjTile: adjTile.player == self.targetPlayer)
					numEnemyLocked = count(releventAdjacents, lambda adjTile: adjTile.player == self.targetPlayer)
					#    for every other nearby enemy tile on the path that we've already included in the path, add some priority
					addedPriority += (numEnemyNear - numEnemyLocked) * 8
				elif nextTile.player == -1:
					neutralTiles -= 1
					# points for capping tiles in general
					addedPriority += 2
					# points for taking neutrals next to enemy tiles
					numEnemyNear = count(nextTile.moveable, lambda adjTile: adjTile not in adjacentSetSoFar and adjTile.player == self.targetPlayer)
					if numEnemyNear > 0:
						addedPriority += 2
				else: # our tiles and non-target enemy tiles get negatively weighted
					addedPriority -= 2
					wastedMoves += 0.7
				# points for discovering new tiles
				addedPriority += count(releventAdjacents, lambda adjTile: not adjTile.discovered) / 2
				## points for revealing tiles in the fog
				#addedPriority += count(releventAdjacents, lambda adjTile: not adjTile.visible)
			else:
				wastedMoves += 1
			nextAdjacentSet = adjacentSetSoFar.copy()
			for adj in nextTile.adjacents:
				nextAdjacentSet.add(adj)
			newPathPriority = pathPriority - addedPriority
			#if generalPlayer.tileCount < 46:
			#	logging.info("nextTile {}, newPathPriority / distSoFar {:.2f}, armyRemaining {}, newPathPriority {}, distSoFar {}, len(nextTileSet) {}".format(nextTile.toString(), newPathPriority / distSoFar, armyRemaining, newPathPriority, distSoFar, len(nextTileSet)))
			return (wastedMoves, newPathPriority / distSoFar, armyRemaining, enemyTiles, neutralTiles, newPathPriority, distSoFar, nextTileSet, nextAdjacentSet)
		priorityFunc = default_priority_func
		
		#logging.info("Using default priorityFunc")
		def a_starey_priority_func(nextTile, currentPriorityObject):
			wastedMoves, pathPriorityDivided, armyRemaining, enemyTiles, neutralTiles, pathPriority, distSoFar, tileSetSoFar, adjacentSetSoFar = currentPriorityObject
			nextTileSet = tileSetSoFar.copy()
			distSoFar += 1
			addedPriority = -7 - max(3, distMap[nextTile.x][nextTile.y] / 4)
			if nextTile not in nextTileSet:
				armyRemaining -= 1
				releventAdjacents = where(nextTile.adjacents, lambda adjTile: adjTile not in adjacentSetSoFar and adjTile not in tileSetSoFar)
				if negativeTiles == None or (nextTile not in negativeTiles):
					if (searchingPlayer == nextTile.player):
						armyRemaining += nextTile.army
					else:
						armyRemaining -= nextTile.army
				nextTileSet.add(nextTile)
				if nextTile.player == self.targetPlayer:
					enemyTiles -= 1
					# points for capping target tiles
					addedPriority += 6
					# points for locking all nearby enemy tiles down
					numEnemyNear = count(nextTile.adjacents, lambda adjTile: adjTile.player == self.targetPlayer)
					numEnemyLocked = count(releventAdjacents, lambda adjTile: adjTile.player == self.targetPlayer)
					#    for every other nearby enemy tile on the path that we've already included in the path, add some priority
					addedPriority += (numEnemyNear - numEnemyLocked) * 8
				elif nextTile.player == -1:
					neutralTiles -= 1
					# points for capping tiles in general
					addedPriority += 2
					# points for taking neutrals next to enemy tiles
					numEnemyNear = count(nextTile.moveable, lambda adjTile: adjTile not in adjacentSetSoFar and adjTile.player == self.targetPlayer)
					if numEnemyNear > 0:
						addedPriority += 2
				else: # our tiles and non-target enemy tiles get negatively weighted
					addedPriority -= 2
					wastedMoves += 0.7
				# points for discovering new tiles
				addedPriority += count(releventAdjacents, lambda adjTile: not adjTile.discovered) / 2
				## points for revealing tiles in the fog
				#addedPriority += count(releventAdjacents, lambda adjTile: not adjTile.visible)
			else:
				wastedMoves += 1
			nextAdjacentSet = adjacentSetSoFar.copy()
			for adj in nextTile.adjacents:
				nextAdjacentSet.add(adj)
			newPathPriority = pathPriority - addedPriority
			#if generalPlayer.tileCount < 46:
			#	logging.info("nextTile {}, newPathPriority / distSoFar {:.2f}, armyRemaining {}, newPathPriority {}, distSoFar {}, len(nextTileSet) {}".format(nextTile.toString(), newPathPriority / distSoFar, armyRemaining, newPathPriority, distSoFar, len(nextTileSet)))
			return (wastedMoves, newPathPriority / distSoFar, armyRemaining, enemyTiles, neutralTiles, newPathPriority, distSoFar, nextTileSet, nextAdjacentSet)
		#priorityFunc = a_starey_priority_func
		
		if turns < 0:
			turns = 50
		remainingTurns = turns
		sortedTiles = sorted(list(where(generalPlayer.tiles, lambda tile: tile.army > 1)), key = lambda tile: 0 - tile.army)
		paths = []
		fullCutoff = 15
		cutoffFactor = 1

		# BACKPACK THIS EXPANSION! Don't stop at remainingTurns 0... just keep finding paths until out of time, then knapsack them

		while remainingTurns > 0 and cutoffFactor <= fullCutoff:
			timeUsed = time.time() - startTime
			# Stages:
			# first 0.1s, use large tiles and shift smaller. (do nothing)
			# second 0.1s, use all tiles (to make sure our small tiles are included)
			if timeUsed > 0.1:
				logging.info("timeUsed > 0.1... Switching to using all tiles, cutoffFactor = fullCutoff...")
				cutoffFactor = fullCutoff
			# third 0.1s - knapsack optimal stuff outside this loop i guess?
			if timeUsed > 0.2:
				logging.info("timeUsed > 0.2... Breaking loop and knapsacking...")
				break

			startIdx = max(0, ((cutoffFactor - 1) * len(sortedTiles))//fullCutoff)
			startIdx = 0
			endIdx = min(len(sortedTiles), (cutoffFactor * len(sortedTiles))//fullCutoff + 1)
			logging.info("startIdx {} endIdx {}".format(startIdx, endIdx))
			tilePercentile = sortedTiles[startIdx:endIdx]
			# filter out the bottom value of tiles (will filter out 1's in the early game, or the remaining 2's, etc)
			tilesLargerThanAverage = where(tilePercentile, lambda tile: tile.army > tilePercentile[-1].army)
			tilesLargerThanAverage = tilePercentile
			logging.info("cutoffFactor {}/{}, largestTile {}: {} army, smallestTile {}: {} army".format(cutoffFactor, fullCutoff, tilePercentile[0].toString(), tilePercentile[0].army, tilePercentile[-1].toString(), tilePercentile[-1].army))
			# hack,  see what happens TODO
			#tilesLargerThanAverage = where(generalPlayer.tiles, lambda tile: tile.army > 1)
			#logging.info("Filtered for tilesLargerThanAverage with army > {}, found {} of them".format(tilePercentile[-1].army, len(tilesLargerThanAverage)))
			startDict = {}
			for i, tile in enumerate(tilesLargerThanAverage):
				# skip tiles we've already used or intentionally ignored
				if tile in negativeTiles:
					continue
				#self.mark_tile(tile, 10)
				startingSet = set()
				startingSet.add(tile)
				startingAdjSet = set()
				for adj in tile.adjacents:
					startingAdjSet.add(adj)
				#wastedMoves, pathPriorityDivided, armyRemaining, pathPriority, distSoFar, tileSetSoFar 
				# 10 because it puts the tile above any other first move tile, so it gets explored at least 1 deep...
				startDict[tile] = ((0, 10, tile.army, 0, 0, 0, 0, startingSet, startingAdjSet), 0)
			logging.info("Seeing if theres a super duper cool optimized expansion pathy thing?")
			path = breadth_first_dynamic_max(self._map, startDict, value_priority_army_dist, 0.2, remainingTurns, True, negativeTiles, 
									searchingPlayer = self.general.player, 
									priorityFunc = priorityFunc, 
									useGlobalVisitedSet = True, 
									skipFunc = skip_after_out_of_army)

			
			if path:
				logging.info("Path found for maximizing army usage? Duration {:.3f} path {}".format(time.time() - startTime, path.toString()))	
				alpha = 50
				minAlpha = 30
				alphaDec = 2
				self.viewInfo.paths.appendleft(PathColorer(path, 255, 51, 204, alpha, alphaDec, minAlpha))
				node = path.start
				# BYPASSED THIS BECAUSE KNAPSACK...
				# remainingTurns -= path.length
				tilesGrabbed = 0
				visited = set()
				friendlyCityCount = 0
				while node != None:
					if node.tile in startDict:
						del startDict[node.tile]
					if node.tile not in negativeTiles and node.tile not in visited:
						if node.tile.player == -1:
							tilesGrabbed += 1
						if node.tile.player == self.targetPlayer:
							tilesGrabbed += 2
						visited.add(node.tile)
					if node.tile.player == self.general.player and (node.tile.isCity or node.tile.isGeneral):
						friendlyCityCount += 1
					# this tile is now worth nothing because we already intend to use it ?
					negativeTiles.add(node.tile)
					node = node.next
				paths.append((friendlyCityCount, tilesGrabbed, path))
			else:
				cutoffFactor += 1
				logging.info("Didn't find a super duper cool optimized expansion pathy thing for remainingTurns {}, cutoffFactor {} :(".format(remainingTurns, cutoffFactor))
				
		#expansionGather = greedy_backpack_gather(self._map, tilesLargerThanAverage, turns, None, valueFunc, baseCaseFunc, negativeTiles, None, self.general.player, priorityFunc, skipFunc = None)
		for leafMove in self.leafMoves:
			if (not leafMove.source in negativeTiles 
					and not leafMove.dest in negativeTiles 
					and (leafMove.dest.player == -1 or leafMove.dest.player == self.targetPlayer)
					and leafMove.source.army > leafMove.dest.army + 1):
				if leafMove.source.army < 5:
					logging.info("adding leafMove {} to knapsack input".format(leafMove.toString()))
					path = Path(leafMove.source.army - leafMove.dest.army - 1)
					path.add_next(leafMove.source)
					path.add_next(leafMove.dest)
					value = 1
					if leafMove.dest.player != -1:
						value = 2
					paths.append((0, value, path))
					negativeTiles.add(leafMove.source)
					negativeTiles.add(leafMove.dest)
				else:
					logging.info("Did NOT add leafMove {} to knapsack input because its value was high. Why wasn't it already input if it is a good move?".format(leafMove.toString()))


		# build knapsack weights and values
		weights = [pathTuple[2].length for pathTuple in paths]
		values = [pathTuple[1] for pathTuple in paths]
		logging.info("Feeding the following paths into knapsackSolver at turns {}...".format(turns))
		for i, pathTuple in enumerate(paths):
			friendlyCityCount, tilesCaptured, curPath = pathTuple
			logging.info("{}:  cap {} length {} path {}".format(i, tilesCaptured, curPath.length, curPath.toString()))

		maxKnapsackedPaths = solve_knapsack(paths, turns, weights, values)
		logging.info("maxKnapsackedPaths length {} Duration {:.3f},".format(len(maxKnapsackedPaths), time.time() - startTime))

		path = None
		if len(maxKnapsackedPaths) > 0:
			maxVal = (-100, -1)
			for pathTuple in maxKnapsackedPaths:
				friendlyCityCount, tilesCaptured, curPath = pathTuple

				# the +1 lightly de-favors 1-move expansions by moving them to 2 moves per tile captured to weight longer paths a bit higher
				thisVal = (0-friendlyCityCount, tilesCaptured / (curPath.length + 1))
				if thisVal > maxVal:
					maxVal = thisVal
					path = curPath
					logging.info("no way this works, evaluation {:.1f}, path {}".format(maxVal[1], path.toString()))					
					
				#draw other paths darker
				alpha = 150
				minAlpha = 70
				alphaDec = 10
				self.viewInfo.paths.appendleft(PathColorer(curPath, 200, 51, 204, alpha, alphaDec, minAlpha))
			logging.info("EXPANSION PLANNED HOLY SHIT? Duration {:.3f}, path {}".format(time.time() - startTime, path.toString()))
			#draw maximal path darker
			alpha = 255
			minAlpha = 100
			alphaDec = 15
			self.viewInfo.paths = deque(where(self.viewInfo.paths, lambda pathCol: pathCol.path != path))
			self.viewInfo.paths.appendleft(PathColorer(path, 255, 100, 200, alpha, alphaDec, minAlpha))
		else:
			logging.info("No expansion plan.... :( Duration {:.3f},".format(time.time() - startTime))

		return path
		
	

	def get_path_to_target_player(self, skipEnemyCities = False):
		undiscoveredCounterDepth = 5
		maxTile = self.general
		maxAmount = 0
		startTime = time.time()
		self._evaluatedUndiscoveredCache = []
		if (self.targetPlayer != -1):
			if self._map.generals[self.targetPlayer] != None:
				return self.get_path_to_target(self._map.generals[self.targetPlayer], skipEnemyCities = skipEnemyCities)

			undiscoveredCounterDepth = 5
			for tile in self.reachableTiles:
				if not tile.discovered and not (tile.mountain or tile.isobstacle()):
					if self._map.remainingPlayers > 2 and count(tile.adjacents, lambda adjTile: adjTile.player == self.targetPlayer) == 0:
						# in FFA, don't evaluate tiles other than those directly next to enemy tiles (to avoid overshooting into 3rd party territory)
						continue
					enemyCounter = Counter(0)
					undiscCounter = Counter(0)
					# the lambda for counting stuff! Lower weight for undiscovereds, we prefer enemy tiles.
					def undiscoveredEnemyCounter(tile):
						if (not (tile.isobstacle() or tile.mountain)) and not (tile.discovered and (tile.player == -1 or tile.player == self.general.player)):
							if (not tile.discovered):
								undiscCounter.add(0.1)
							if tile.player == self.targetPlayer:
								enemyCounter.add(1)
					def skipPlayerAndDiscoveredFunc(tile):
						if tile.player == self.general.player or tile.discoveredAsNeutral:
							return True
						return False
					breadth_first_foreach(self._map, [tile], undiscoveredCounterDepth, undiscoveredEnemyCounter, noLog = True, skipFunc = skipPlayerAndDiscoveredFunc)
					foundValue = enemyCounter.value + undiscCounter.value
					if enemyCounter.value > 0 and foundValue > maxAmount:
						maxTile = tile
						maxAmount = foundValue
			if maxTile == self.general:
				# retry without forcing discoveredAsNeutral. TODO refactor into method call. WTF dont copy paste, who does that?
				for tile in self.reachableTiles:
					if not tile.discovered and not (tile.mountain or tile.isobstacle()):
						enemyCounter = Counter(0)
						undiscCounter = Counter(0)
						# the lambda for counting stuff! Lower weight for undiscovereds, we prefer enemy tiles.
						def undiscoveredEnemyCounter(tile):
							if (not (tile.isobstacle() or tile.mountain)) and not (tile.discovered and (tile.player == -1 or tile.player == self.general.player)):
								if (not tile.discovered):
									undiscCounter.add(1)
								if tile.player == self.targetPlayer:
									enemyCounter.add(1)
						def skipPlayerAndDiscoveredFunc(tile):
							if tile.player == self.general.player or (tile.discovered and tile.player == -1):
								return True
							return False
						breadth_first_foreach(self._map, [tile], undiscoveredCounterDepth, undiscoveredEnemyCounter, noLog = True, skipFunc = skipPlayerAndDiscoveredFunc)
						foundValue = min(enemyCounter.value, undiscCounter.value) + 0.01 * max(enemyCounter.value, undiscCounter.value)
						if enemyCounter.value > 0 and undiscCounter.value > 0 and foundValue > maxAmount:
							maxTile = tile
							maxAmount = foundValue
			def undiscoveredMarker(tile):
				if (not (tile.isobstacle() or tile.mountain)) and not (tile.discoveredAsNeutral or tile.player == self.general.player):
					if (not tile.discovered):
						self._evaluatedUndiscoveredCache.append(tile)
						self.viewInfo.evaluatedGrid[tile.x][tile.y] = 1
					if tile.player == self.targetPlayer:
						self.viewInfo.evaluatedGrid[tile.x][tile.y] = 1
			breadth_first_foreach(self._map, [maxTile], undiscoveredCounterDepth, undiscoveredMarker, noLog = True, skipFunc = skipPlayerAndDiscoveredFunc)
		else:
			# TODO look into the void and see it staring back at yourself
			# find mirror spot in the void? Or just discover the most tiles possible.
			# Kind of done. Except really, shouldn't be BFSing with so much CPU for this lol.

			for tile in self.reachableTiles:
				if not tile.discovered and not (tile.mountain or tile.isobstacle()):
					counter = Counter(0)
					# the lambda for counting stuff!
					def undiscoveredCounter(tile):
						if (not tile.discovered) and not (tile.isobstacle() or tile.mountain):
							counter.add(1)
					breadth_first_foreach(self._map, [tile], undiscoveredCounterDepth, undiscoveredCounter, noLog = True)
					if counter.value > maxAmount:
						maxTile = tile
						maxAmount = counter.value
			def undiscoveredMarker(tile):
				if (not tile.discovered) and not (tile.isobstacle() or tile.mountain):
					self._evaluatedUndiscoveredCache.append(tile)
					self.viewInfo.evaluatedGrid[tile.x][tile.y] = 1
			breadth_first_foreach(self._map, [maxTile], undiscoveredCounterDepth, undiscoveredMarker, noLog = True)

		path = self.get_path_to_target(maxTile, skipEnemyCities = skipEnemyCities, preferNeutral = self._map.remainingPlayers < 3)
		logging.info("Highest density undiscovered tile {},{} with value {} found in {}, \npath {}".format(maxTile.x, maxTile.y, maxAmount, time.time() - startTime, path.toString()))
		if self.targetPlayer == -1 and self._map.remainingPlayers > 2:
			# To avoid launching out into the middle of the FFA, just return the general tile and the next tile in the path as the path. 
			# this sort of triggers camping-city-taking behavior at the moment.
			fakeGenPath = path.get_subsegment(2)
			logging.info("FakeGenPath because FFA: {}".format(fakeGenPath.toString()))
			return fakeGenPath
		return path
		
	def info(self, text):
		self.viewInfo.infoText = text
		logging.info(text)

	def get_path_to_target(self, target, maxTime = 0.1, maxDepth = 85, skipNeutralCities = True, skipEnemyCities = False, preferNeutral = True):
		negativeTiles = None
		if skipEnemyCities:
			negativeTiles = set()
			for enemyCity in self.enemyCities:
				negativeTiles.add(enemyCity)
		skipFunc = None
		if skipEnemyCities:
			skipFunc = lambda tile, prioObject: tile.player != self.general.player and tile.isCity
		path = breadth_first_dynamic(self._map, [self.general], lambda tile, prioObj: tile == target, maxTime, maxDepth, skipNeutralCities, negativeTiles = negativeTiles, preferNeutral = preferNeutral, skipFunc = skipFunc)
		if path == None:
			path = Path(0)
			path.add_next(self.general)
		return path

	
	def distance_from_general(self, sourceTile):
		if sourceTile == self.general:
			return 0
		if self._gen_distances == None:
			self._gen_distances = build_distance_map(self._map, [self.general])

		val = self._gen_distances[sourceTile.x][sourceTile.y]
		return val
		
		

	def scan_map(self):
		self.general_safe_func_set[self.general] = self.general_move_safe
		self.numPlayers = self._map.remainingPlayers
		self.leafMoves = []
		self.largeTilesNearEnemyKings = {}
		self.allUndiscovered = []
		self.largePlayerTiles = []
		player = self._map.players[self.general.player]
		largePlayerTileThreshold = player.standingArmy / player.tileCount * 5
		general = self._map.generals[self._map.player_index]
		generalApproximations = [[0, 0, 0, None] for i in range(len(self._map.generals))]
		for x in range(general.x - 1, general.x + 2):
			for y in range(general.y - 1, general.y + 2):
				if x == general.x and y == general.y:
					continue
				tile = GetTile(self._map, x, y)
				if tile != None and tile.player != general.player and tile.player != -1:
					self._map.players[tile.player].knowsKingLocation = True
					

		for enemyGen in self._map.generals:
			if (enemyGen != None and enemyGen.player != self._map.player_index):
				self.largeTilesNearEnemyKings[enemyGen] = []
		for x in range(self._map.cols):
			for y in range(self._map.rows):
				tile = _map.grid[y][x]
				if tile.discovered and tile.player == -1:
					tile.discoveredAsNeutral = True
				if (not tile.discovered and not tile.isobstacle()):
					self.allUndiscovered.append(tile)

				if (tile.player != self._map.player_index and tile.player >= 0 and self._map.generals[tile.player] == None):
					for nextTile in tile.moveable:
						if (not nextTile.discovered and not nextTile.isobstacle()):
							approx = generalApproximations[tile.player]
							approx[0] += nextTile.x
							approx[1] += nextTile.y
							approx[2] += 1

				if (tile.player == self._map.player_index):
					for nextTile in tile.moveable:
						if nextTile.player != _map.player_index and not nextTile.mountain:
							self.leafMoves.append(Move(tile, nextTile))
					if (tile.army > largePlayerTileThreshold):
						self.largePlayerTiles.append(tile)

				elif(tile.player != -1):
					if(tile.isCity):
						self.enemyCities.append(tile)	
				if (not tile.isvisible() and not ((tile.isCity or tile.isGeneral) and self._map.turn > 250) and (self._map.turn - tile.lastSeen >= 100 or (self._map.turn - tile.lastSeen > 25 and tile.army > 25))):
					player = self._map.players[tile.player]
					if player.tileCount > 0:
						tile.army = int((player.standingArmy / player.tileCount) / (player.cityCount / 2 + 1))
				if (not tile.isvisible() and tile.isCity and tile.player != -1 and self._map.turn - tile.lastSeen > 25):
					player = self._map.players[tile.player]
					if player.cityCount > 0:
						tile.army = int((player.standingArmy / player.cityCount) / 8)
				if tile.player == self._map.player_index and tile.army > 4:
					for enemyGen in self.largeTilesNearEnemyKings.keys():
						if tile.army > enemyGen.army and self.euclidDist(tile.x, tile.y, enemyGen.x, enemyGen.y) < 12:
							self.largeTilesNearEnemyKings[enemyGen].append(tile)
						

	
		reachableTiles = set()		
		def find_reachable(tile):
			reachableTiles.add(tile)

		fakePath = breadth_first_foreach(self._map, [self.general], 100, find_reachable, skipFunc = lambda tile: tile.isCity and tile.player == -1)
		self.reachableTiles = reachableTiles
		self._map.reachableTiles = reachableTiles

		for i in range(len(self._map.generals)):
			if self._map.generals[i] != None:
				gen = self._map.generals[i]
				generalApproximations[i][0] = gen.x
				generalApproximations[i][1] = gen.y
				generalApproximations[i][3] = gen
			elif (generalApproximations[i][2] > 0):
				
				generalApproximations[i][0] = generalApproximations[i][0] / generalApproximations[i][2]
				generalApproximations[i][1] = generalApproximations[i][1] / generalApproximations[i][2]

				#calculate vector				
				delta = ((generalApproximations[i][0] - general.x) * 1.1, (generalApproximations[i][1] - general.y) * 1.1)
				generalApproximations[i][0] = general.x + delta[0]
				generalApproximations[i][1] = general.y + delta[1]
		for i in range(len(self._map.generals)):
			gen = self._map.generals[i]
			genDist = 1000
			
			if gen == None and generalApproximations[i][2] > 0:
				for tile in self.reachableTiles:
					if not tile.discovered and not tile.isobstacle():
						tileDist = self.euclidDist(generalApproximations[i][0], generalApproximations[i][1], tile.x, tile.y)
						if (tileDist < genDist and self.distance_from_general(tile) < 1000):
							generalApproximations[i][3] = tile
							genDist = tileDist

		self.generalApproximations = generalApproximations	

		targetPlayer = -1
		playerScore = -100000
		minStars = 10000
		starSum = 0
		for player in self._map.players:
			minStars = min(minStars, player.stars)
			starSum += player.stars
		starAvg = starSum * 1.0 / len(self._map.players)
		minStars = max(minStars, starAvg - 20)
		self.playerTargetScores = [0 for i in range(len(self._map.players))]
		generalPlayer = self._map.players[self.general.player]
		for player in self._map.players:
			seenPlayer = self.generalApproximations[player.index][2] > 0 or self._map.generals[player.index] != None
			if not player.dead and player.index != self._map.player_index and seenPlayer:
				curScore = 300

				alreadyTargetingBonus = 80
				if player.index == self.targetPlayer:
					curScore += alreadyTargetingBonus

				knowsWhereEnemyGeneralIsBonus = 100
				if self._map.generals[player.index] != None:
					curScore += knowsWhereEnemyGeneralIsBonus

				# target players with better economies first
				curScore = curScore + player.tileCount + player.cityCount * 30 - player.standingArmy ** 0.8

				weAreWinningBonus = 80
				if generalPlayer.standingArmy > player.standingArmy * 0.9:
					curScore += weAreWinningBonus

				if (player.knowsKingLocation):
					curScore += 150
					curScore *= 2

				if generalApproximations[player.index][3] != None:
					genDist = self.distance_from_general(generalApproximations[player.index][3])
				else:
					logging.info("           wot {} didn't have a gen approx tile???".format(self._map.usernames[targetPlayer]))
					genDist = self.euclidDist(generalApproximations[player.index][0], generalApproximations[player.index][1], self.general.x, self.general.y)
				curScore = curScore + 2 * curScore / (max(10, genDist) - 2)

				if (player.tileCount < 4 and player.general == None) or (player.general != None and player.general.army > player.standingArmy * 0.8):
					curScore = -100
				if (curScore > playerScore and player.index not in self._map.teammates):
					playerScore = curScore
					targetPlayer = player.index
				self.playerTargetScores[player.index] = curScore

		self.targetPlayer = targetPlayer
		if (targetPlayer != -1):
			logging.info("target player: {} ({})".format(self._map.usernames[targetPlayer], int(playerScore)))



			

	

_eklipzBot = EklipZBot(THREAD_COUNT)

def make_move(currentBot, currentMap):
	global _bot, _map
	_bot = currentBot
	_map = currentMap
	_eklipzBot._bot = _bot
	_eklipzBot._map = _map
	
	command = currentBot.getLastCommand()	
	#if (command == "-s"):
	#	return
	startTime = time.time()
	move = _eklipzBot.find_move()
	duration = time.time() - startTime
	_eklipzBot.viewInfo.lastMoveDuration = duration
	if (move != None):
		if not place_move(move.source, move.dest, move.move_half):
			logging.info("!!!!!!!!! {},{} -> {},{} was an illegal / bad move!!!!".format(move.source.x, move.source.y, move.dest.x, move.dest.y))
	return


def place_move(source, dest, moveHalf = False):
	if _map.turn > GENERAL_HALF_TURN:
		if source.isGeneral:
			moveHalf = True
		elif source.isCity and _map.turn - source.turn_captured < 50:
			moveHalf = True
	
	logging.info("Placing move: {},{} to {},{}".format(source.x, source.y, dest.x, dest.y))
	return _bot.place_move(source, dest, move_half=moveHalf)

def make_primary_move():
	if not move_toward():
		move_outward()

######################### Move Outward #########################
def move_outward():
	for x in bot_base._shuffle(range(_map.cols)): # Check Each Square
		for y in bot_base._shuffle(range(_map.rows)):
			source = _map.grid[y][x]

			if (source.tile == _map.player_index and source.army >= 2 and source not in _path): # Find One With Armies
				for dy, dx in _bot.toward_dest_moves(source):
					if (_bot.validPosition(x + dx,y + dy)):
						dest = _map.grid[y + dy][x + dx]
						if (dest.tile != _map.player_index and source.army > (dest.army + 1)) or (dest in _path): # Capture Somewhere New
							place_move(source, dest)
							return True
	return False

######################### Move Toward #########################
_path = []
def move_toward():
	# Find path from largest tile to closest target
	source = _bot.find_largest_tile(includeGeneral=True)
	target = _bot.find_closest_target(source)
	path = _bot.find_path(source=source, dest=target)

	army_total = 0
	for tile in path: # Verify can obtain every tile in path
		if (tile.tile == _map.player_index):
			army_total += (tile.army - 1)
		elif (tile.army + 1 > army_total): # Cannot obtain tile, draw path from largest city to largest tile
			source = _bot.find_city(includeGeneral=True)
			target = _bot.find_largest_tile(notInPath=[source])
			if (source and target and source != target):
				path = _bot.find_path(source=source, dest=target)
			break

	# Place Move
	_path = path
	_bot._path = path
	(move_from, move_to) = _bot.path_forward_moves(path)
	if (move_from != None):
		place_move(move_from, move_to)
		return True

	return False

######################### Main #########################

# Start Game
import startup
if __name__ == '__main__':
	startup.startup(make_move, "EklipZTest2")