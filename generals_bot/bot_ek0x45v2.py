"""
	@ Travis Drake (EklipZ) eklipz.io - tdrake0x45 at gmail)
	April 2017
	Generals.io Automated Client - https://github.com/harrischristiansen/generals-bot
	EklipZ bot - Tries to play generals lol
"""

import logging
import random
import sys
import traceback
import time
import json
from .base import bot_base
from .base.bot_base import _create_thread
from copy import deepcopy
from collections import deque
from queue import PriorityQueue
from pprint import pprint, pformat
from .ViewInfo import ViewInfo
from .DataModels import GatherNode, PathNode, stringPath, Move
from .SearchUtils import (
    dest_breadth_first_target,
    a_star_kill,
    breadth_first_find,
    breadth_first_find_queue,
)
from .dangerAnalyzer import DangerAnalyzer, ThreatType
from .DataModels import (
    get_tile_set_from_path,
    get_tile_set_from_path_tuple,
    reverse_path,
    reverse_path_tuple,
    get_player_army_amount_on_path,
    get_tile_list_from_path,
    get_tile_list_from_path_tuple,
)
import math
INF = math.inf


"""
PSEUDOCODE

First 50 turns: 
	plan optimal expansion

Next 50 turns:




















GENERAL_HALF_TURN = 20000

def where(list, filter):
	results = set()
	for item in list:
		if filter(item):
			results.add(item)
	return results

def any(list, filter):
	for item in list:
		if filter(item):
			return True
	return False

def count(list, filter):
	count = 0
	for item in list:
		if filter(item):
			count += 1
	return count

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
			
def is_gather_worthwhile(gather, parent):
	gatherWorthwhile = False
	if (parent != None):
		gatherWorthwhile = (gather.value > 0 and gather.value > parent.value / 20) or parent.fromTile == None
		#gatherWorthwhile = maxGather.value > 0 and maxGather.value > parent.value / 9
		logging.info("Gather worthwhile? {} {},{}   maxGath {}  parent {}".format(gatherWorthwhile, gather.tile.x, gather.tile.y, gather.value, parent.value))
	else:
		logging.info("No parent. {},{}   maxGath {}".format(gather.tile.x, gather.tile.y, gather.value))
	return gatherWorthwhile


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

		self.target_player_gather_targets = None
		self.target_player_gather_path = None

		self.viewInfo = None

		self._minAllowableArmy = -1
		self.giving_up_counter = 0
		self.all_in_counter = 0
		self.threat = None

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
		move = self.dummyMover(allowRetry)
		if (self._map.turn not in self.moveHistory):
			self.moveHistory[self._map.turn] = []
		self.moveHistory[self._map.turn].append(move)
		return move
		
	def dummyMover(self, allowRetry = True):
		start = time.time()
		logging.info("\n       ~~~\n       Turn {}\n       ~~~\n".format(self._map.turn))
		if self.general == None:
			self.general = self._map.generals[self._map.player_index]
		self._minAllowableArmy = -1
		self._gen_distances = None
		self.target_player_gather_path = None
		self.target_player_gather_targets = None
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
			logging.basicConfig(format='%(levelname)s:%(message)s', filename="test.txt", level=logging.DEBUG)
		#logging.info('thingy')
		self._map.ekBot = self
		self.viewInfo.turnInc()
		
		
		if (self._map.turn < 50):
			if (self._map.turn < 24):
				return None
			if (self._map.turn < 47 and self.general.army < 3 and self._map.players[self.general.player].standingArmy + 1 == self.general.army):
				# dont send 2 army except right before the bonus, making perfect first 25 much more likely
				return None
		#if (self.turnsTillDeath > 0):
		#	self.turnsTillDeath -= 1
			#logging.info("\n\n---------TURNS TILL DEATH AT MOVE START {}\n".format(self.turnsTillDeath))
		self.scan_map()
		general = self.general
		
		allLeaves = self.leafMoves

		if self.target_player_gather_path == None or (not self._map.turn - self.lastTargetAttackTurn > 2):
			self.target_player_gather_path = self.get_path_to_target_player()
			targets = get_tile_set_from_path_tuple(self.target_player_gather_path)
			self.target_player_gather_targets = targets

		if (self.curPath != None and (self.curPath.tile.delta.armyDelta != 0 or self.curPath.tile.player != self._map.player_index or self.curPath.tile.isGeneral)):
			if (self.curPath.parent != None and self.curPath.parent.parent != None and self.curPath.parent.parent.parent != None and self.curPath.tile == self.curPath.parent.parent.tile and self.curPath.parent.tile == self.curPath.parent.parent.parent.tile):
				logging.info("\n\n\n~~~~~~~~~~~\nDe-duped path\n~~~~~~~~~~~~~\n\n~~~\n")
				self.curPath = self.curPath.parent.parent.parent.parent
			elif (self.curPath.parent != None and self.curPath.tile.x == self.curPath.parent.tile.x and self.curPath.tile.y == self.curPath.parent.tile.y):
				logging.warning("           wtf, doubled up tiles in path?????")
				self.curPath = self.curPath.parent.parent
			else:
				self.curPath = self.curPath.parent
		elif self.curPath != None:
			logging.info("         --         missed move?")
		#elif(self.curPath != None):
		#	logging.info("\n!!~~!!~~ OH DAMN LOOKS LIKE WE MISSED A MOVE! ~~!!~~!!")
		#	if (self.curPath.parent != None):
		#		logging.info("!!~~!!~~ [{}: {}] {},{} -> [{}: {}] {},{} ~~!!~~!!\n".format(self.curPath.tile.player, self.curPath.tile.army, self.curPath.tile.x, self.curPath.tile.y, self.curPath.parent.tile.player, self.curPath.parent.tile.army, self.curPath.parent.tile.x, self.curPath.parent.tile.y))
		#	else: 
		#		logging.info("!!~~!!~~ parent was None ~~!!~~!!\n")

		#try: 			
		#	closestCityPath = breadth_first_find(self._map, [general], (lambda tile, army, dist: tile.isCity), 0.01, 10)
		#	if closestCityPath[0] != None and closestCityPath[1] != None:
		#		logging.info("aaaaaaaaaaaaaaaa\naaaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaa{}".format(stringPath(closestCityPath[1])))
		#except:
		#	exc_type, exc_value, exc_traceback = sys.exc_info()
		#	lines = traceback.format_exception(exc_type, exc_value, exc_traceback)
		#	logging.info(''.join('!! ' + line for line in lines))  # Log it or whatever here
		


		if (self.curPathPrio >= 0):
			logging.info("curPathPrio: " + str(self.curPathPrio))

		self.calculate_general_danger()


		turnsTillDanger = -1 
		threat = None
		visionThreat = None
		minAllowable = self.general_min_army_allowable()
		if not self.allIn:
			if (self.dangerAnalyzer.fastestVisionThreat != None):
				threat = self.dangerAnalyzer.fastestVisionThreat
				visionThreat = self.dangerAnalyzer.fastestVisionThreat
				turnsTillDanger = threat.turns

			if (self.dangerAnalyzer.fastestThreat != None):
				threat = self.dangerAnalyzer.fastestThreat
				turnsTillDanger = threat.turns


		# SEARCH FOR BFS KILL ON ENEMY KING

		negativeTiles = set()
		if (len(self.largeTilesNearEnemyKings.keys()) > 0):
			(killStart, killPath) = dest_breadth_first_target(self._map, self.largeTilesNearEnemyKings.keys(), 1, 0.05, len(self.target_player_gather_targets) / 2, None, self.general.player, False, 4)
			if (killPath != None and killStart.turn >= 0) and (threat == None or (turnsTillDanger > killStart.turn)):
				logging.info("DEST BFS K found kill path length {} :^)".format(killStart.turn))
				self.curPath = killPath
				self.curPathPrio = 5
				move = Move(killPath.tile, killPath.parent.tile)
				if self.is_move_safe_valid(move):
					self.viewInfo.infoText = "Killpath against general length {}".format(killStart.turn)
					return move
				


		for king in self.largeTilesNearEnemyKings.keys():
			tiles = self.largeTilesNearEnemyKings[king]
			furtherTiles = []
			if (len(tiles) > 0):	
				logging.info("Attempting to find kill path against general {} ({},{})".format(king.player, king.x, king.y))
				bestTurn = 1000
				bestPath = None
				for tile in tiles:
					if dist(tile, king) < 10:
						(pathEnd, path) = a_star_kill(self._map, [tile], king, 0.02, len(self.target_player_gather_targets) / 2, self.general_safe_func_set)
						
						if (path != None and pathEnd.turn >= 0) and (threat == None or (turnsTillDanger > pathEnd.turn and threat.threatPlayer == king.player)):
							logging.info("A_STAR found kill path length {} :^)".format(pathEnd.turn))
							self.curPath = path
							self.curPathPrio = 5
							if (pathEnd.turn < bestTurn):
								bestPath = path
								bestTurn = pathEnd.turn
					else:
						furtherTiles.append(tile)
				if (bestPath != None):
					self.viewInfo.infoText = "A* Killpath {},{} length {}".format(king.x, king.y, bestPath.turn)
					self.viewInfo.lastEvaluatedGrid[king.x][king.y] = 200
					return Move(bestPath.tile, bestPath.parent.tile)
				#(pathEnd, path) = a_star_kill(self._map, furtherTiles, king, 0.03, 30, self.general_safe_func_set)
				#if (path != None and pathEnd.turn >= 0) and (threat == None or (turnsTillDanger > pathEnd.turn and threat.threatPlayer == king.player)):
				#	logging.info("Found kill path length {} :^)".format(pathEnd.turn))
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
		if (genLowArmy) or (turnsTillDanger > -1 and self.dangerAnalyzer.anyThreat):
			armyAmount = (self.general_min_army_allowable() + enemyNearGen) * 1.1 if threat == None else threat.threatValue + general.army + 1

			searchTurns = turnsTillDanger
			#self.turnsTillDeath = turnsTillDanger
			if searchTurns <= 0 or (threat == None and genLowArmy):
				searchTurns = min(40, 20 + self._map.turn / 50)
				logging.info("searchTurns <= 0 or general not really in danger, setting to {}".format(searchTurns))
			#if (searchTurns < 2):
			#	searchTurns = 10
			
			
				
			logging.info("\n!-!-!-!-!-!  general in danger in {}, gather {} to general in {} turns  !-!-!-!-!-!".format(turnsTillDanger, armyAmount, searchTurns))

			self.viewInfo.addSearched(general)
			gatherPaths = []
			for tile in self.largeVisibleEnemyTiles:
				negativeTiles.add(tile)
			if (threat != None and threat.threatType == ThreatType.Kill):
				move = self.get_threat_killer_move(threat)
				if move != None:
					self.viewInfo.infoText = "threat killer move"
					return move
				dangerPath = threat.path.pathMove
				targetTile = None
				dict = {}
				dict[general] = (0, 0)
				#i = 0
				#tileArmy = 0
				#while dangerPath != None:
				#	tileTurn = searchTurns - i
				#	targetTile = dangerPath.move.source
				#	# TODO fix gather length so that we can gather to the whole threat path

				#	#logging.info("will be gathering to {},{} while trying to save general, tileTurn {}".format(dangerPath.move.source.x, dangerPath.move.source.y, tileTurn))
				#	#dict[targetTile] = (tileTurn, tileArmy)
				#	negativeTiles.add(dangerPath.move.dest)
				#	dangerPath = dangerPath.next
				#	i += 1
				if threat != None and threat.saveTile != None:
					dict[threat.saveTile] = (0, threat.saveTile.army)
					self.viewInfo.addSearched(threat.saveTile)
					logging.info("dict[threat.saveTile] = (0, {})  -- threat.saveTile {},{}".format(threat.saveTile.army, threat.saveTile.x, threat.saveTile.y))
				thing = dest_breadth_first_target(self._map, dict, armyAmount, 0.1, searchTurns, negativeTiles)
				if (thing[0] != None and thing[1] != None and thing[0].turn > 0):
					lastNode = thing[0]
					while lastNode.parent != None:
						lastNode = lastNode.parent
					logging.info("thing[0].turn {} lastNode.turn {} thing[1].turn {}".format(thing[0].turn, lastNode.turn, thing[1].turn))
					thing[1].turn = lastNode.turn + 1
					logging.info("a\naa\naaa\naaaa\naaaaa\n            DEST BFS TARGET to save king, \n               turn {}, value {} : {}".format(lastNode.turn, thing[0].value, stringPath(thing[1])))
					gatherPaths.append(thing)
				else:
					logging.info("a\naa\n  aa OH NO DEST BFS COULDN'T FIND SAVE-PATH")
					gatherPaths = self.WeightedBreadthSearch([general], max(1, searchTurns + 1), 0.12, general.player, armyAmount, 200, negativeTiles)
			elif visionThreat != None:
			
				if visionThreat.turns < 2:
					logging.info("\n\n!-!-!-!-!-! \n     !!  VISION THREAT 1 !! \n!-!-!-!-!-!")
					target = visionThreat.path.pathMove.move.dest
					if target in general.moveable and self.general_move_safe(target):
						self.viewInfo.infoText = "Vision threat general move"
						return Move(general, target)
				logging.info("\n\n!-!-!-!-!-! \n         WHEE WHOO WHEE WHOO\n       WE GATHERIN NOW, VISION THREAT\n!-!-!-!-!-!")
				threatTiles = []
				dangerPath = visionThreat.path.pathMove
				i = 0
				while dangerPath != None:
					threatTiles.append(dangerPath.move.source)
					#if i >= (visionThreat.turns / 2 - 1):
					#	threatTiles.append(dangerPath.move.source)
					#	logging.info("will be gathering to {},{} while trying to stop vision threat".format(dangerPath.move.source.x, dangerPath.move.source.y))
					dangerPath = dangerPath.next
					i += 1
				self.gatherNodes = self.breadth_first_gather(threatTiles, 1.0, visionThreat.turns / 2, None, set([general]))
				
				move = self.get_gather_move(self.gatherNodes, None)
				if (move != None):
					self.viewInfo.infoText = "gathering to vision threat????"
					return self.move_half_on_repetition(move, visionThreat.turns, 2)
			else:
				logging.info("\n\n!-!-!-!-!-! \n         WHEE WHOO WHEE WHOO\n       WE GATHERIN NOW, NO THREAT \n!-!-!-!-!-!")
				negSet = set()
				if (self.curPath != None):
					negSet.add(self.curPath.tile)

				kingsPath = get_tile_set_from_path_tuple(self.get_path_to_target_player())

				gathers = self.breadth_first_gather(kingsPath, 1.0, 50, None, negSet)
				self.gatherNodes = gathers
				move = self.get_gather_move(gathers, None)
				if (move != None):
					self.viewInfo.infoText = "no-threat-gather on low army"
					return self.move_half_on_repetition(move, 10, 2)
				# if self._map.turn % 3 > 0:
				# 	for tile in self.largePlayerTiles:
				# 		negativeTiles.add(tile)
				# gatherPaths = self.WeightedBreadthSearch(destinations, max(1, searchTurns + 1), 0.12, general.player, -1, 200, negativeTiles)


			if (len(gatherPaths) == 0 and threat != None and threat.threatType == ThreatType.Kill):
				if not self.allIn and not (self._map.remainingPlayers > 2 and threat.threatPlayer != self.targetPlayer):
					logging.info("\n\n!-!-!-!-!-! \nIt may be too late to save general, using longer turncount {} to attempt defense :( \n!-!-!-!-!-!".format(searchTurns + 2))
					gatherPaths = self.WeightedBreadthSearch([self.general], searchTurns + 5, 0.15, general.player, -1, 200, negativeTiles)
				else:
					logging.info("\n\n!-!-!-!-!-! \nIt may be too late to save general, SKIPPING DEFENSE, YOLO, allIn {} remainingPlayers {}\n!-!-!-!-!-!".format(self.allIn, self._map.remainingPlayers))


			queue = PriorityQueue()
			queueShortest = PriorityQueue()
			for path in gatherPaths:
				gatherVal = (path[1].value - general.army - path[1].turn / 2)
				if (gatherVal > 0 and path[1].turn > 1):					
					pathVal = gatherVal / 1.5 + gatherVal / path[1].turn
					if path[1].turn > searchTurns:
						pathVal = (pathVal / 100.0 - 1.0) / (path[1].turn - searchTurns)					
					queue.put((0 - pathVal, path))

			if (threat != None):
				for path in gatherPaths:
					if (gatherVal >= threat.threatValue and path[1].turn < searchTurns):
						queueShortest.put((0 - path[1].turn, 0 - path[1].value, path))

			if (not queueShortest.empty()):
				(negTurn, negPathVal, savePath) = queueShortest.get()
				logging.info("SHORT path to save king, turn {}, value {} : {}".format(savePath[1].turn, savePath[1].value, stringPath(savePath[1])))
				paths = []
				saveNode = savePath[1]
				if (saveNode.turn > searchTurns - 2):
					while saveNode != None:
						negativeTiles.add(saveNode.tile)
						saveNode = saveNode.parent

				# GATHER TO THREAT PATH
				#dangerPath = threat.path.pathMove.next
				#logging.info("WE HAVE A SAVE, GATHERING TO THREAT PATH HOWEVER".format(dangerPath.move.dest.x, dangerPath.move.dest.y))	
				#threatTiles = [general]
				#while dangerPath != None:
				#	threatTiles.append(dangerPath.move.source)
				#	dangerPath = dangerPath.next

				#negSet = set()
				#if (self.curPath != None):
				#	negSet.add(self.curPath.tile)
				#negSet.add(general)
				#self.gatherNodes = self.breadth_first_gather(threatTiles, 1.0, threat.turns / 2, negativeTiles, negSet)
				#move = self.get_gather_move(self.gatherNodes, None)
				#if (move != None):
				#	#self.curPath = None
				#	#self.curPathPrio = -1
				#	return self.move_half_on_repetition(move, 5)
				## else:
				## 	logging.info("IGNORED with low value / length: " + stringPath(path[1]))
			else:				
				while not queue.empty() and len(paths) < 5:
					node = queue.get()
					path = node[1]
					paths.append(path)
					self.info("path to save king, ({}) turn {}, value {} : {}".format(node[0], path[1].turn, path[1].value, stringPath(path[1])))

			
			if (len(paths) > 0): 
				self.lastGeneralGatherTurn = self._map.turn
				#if (threat != None and threat.threatType == ThreatType.Kill):
				#	self.curPathPrio = 100
				#else:
				#	self.curPathPrio = 10
				savePath = paths[0][1]
				end = time.time()
				logging.info("Time calculating defensive gather to general: {}".format(end - start))
				depth = 3
				node = savePath
				while node.parent != None and depth > 0:
					node = savePath.parent
					depth -= 1
				node.parent = None
				self.curPath = savePath
				self.info("set curpath to save general." + stringPath(savePath))
				return Move(savePath.tile, savePath.parent.tile)
				
			end = time.time()
			logging.info("Time calculating defensive gather to general: {}".format(end - start))
		####    CITY RECAP
		####
		####
	

		dangerTiles = self.get_danger_tiles()
		if (len(dangerTiles) > 0):
			logging.info("trying to kill danger tiles")
			for tile in dangerTiles:
				self.viewInfo.addSearched(tile)
				armyToSearch = self.get_target_army_inc_adjacent_enemy(tile)
				(killStart, killPath) = dest_breadth_first_target(self._map, [tile], armyToSearch, 0.1, 10, None, dontEvacCities=False)
				if (killPath != None):
					self.info("found depth {} dest bfs kill on danger tile {},{} \n{}".format(killStart.turn, tile.x, tile.y, stringPath(killPath)))
					self.curPath = killPath
				else:
					self.gatherNodes = self.breadth_first_gather(dangerTiles, 1.0, 10, None, set([general]))
					move = self.get_gather_move(self.gatherNodes, None)
					if (move != None):
						self.info("gathering to danger tile??? {},{}".format(tile.x, tile.y))
						return self.move_half_on_repetition(move, 4, 2)


		#if not (len(paths) > 0) and (not (self.danger != None and self.danger[3]) and (self.curPath == None or self.curPath.parent == None or self.curPathPrio <= 0)):
		# if len(paths) == 0 and (self.curPath == None or self.curPath.parent == None) and not self._map.turn % 20 == 1: 
		if len(paths) == 0 and (self.curPath == None or self.curPath.parent == None) and self.worth_attacking_target():
			
			logging.info("\n\nOOOOOOOOOOOOMG attacking\n\n")
			path = self.get_value_per_turn_subsegment(reverse_path_tuple(self.target_player_gather_path))
			#paths.append(path)
			if path != None and path[0] != None:
				self.info("attacking because self.worth_attacking_target()")
				#paths.append(path)
				self.lastTargetAttackTurn = self._map.turn
				#return self.move_half_on_repetition(Move(path[1].tile, path[1].parent.tile, path[1].move_half), 7, 3)
				self.curPath = path[1]
			else:
				logging.info("WTF PATH WAS NONEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEE")
				
		if len(paths) == 0 and (self.curPath == None or self.curPath.parent == None) and self._map.turn >= 100: 

			largestEnemyAdj = None
			sumAdj = 0
			armyToGather = self.get_target_army_inc_adjacent_enemy(self.general)
			enemyGenAdj = []
			for generalAdj in self.general.adjacents:
				if (generalAdj.player != self._map.player_index and generalAdj.player != -1):
					self.viewInfo.addSearched(generalAdj)
					enemyGenAdj.append(generalAdj)
			if len(enemyGenAdj) > 0:
				logging.info("KILLING GENERAL VISION TILES searching for dest bfs kill")
				largest = max(enemyGenAdj, key=lambda tile: tile.army)
				(killStart, killPath) = dest_breadth_first_target(self._map, [largest], armyToGather, 0.2, 11)
				if (killPath != None):
					self.info("found depth {} dest bfs kill on general vision tile: {}".format(killStart.turn, stringPath(killPath)))
					paths.append((killStart, killPath))
			else:	
				undiscNeg = negativeTiles.copy()				
				for city in self._map.players[self._map.player_index].cities:
					undiscNeg.add(city)
				undiscNeg.add(self.general)
				(pathStart, path) = self.explore_target_player_undiscovered(undiscNeg)	
				if (path != None):
					self.info("found depth {} dest bfs kill on target undisc\n{}".format(pathStart.turn, stringPath(path)))
					paths.append((pathStart, path))
				else:
					if not (self.generalApproximations[self.targetPlayer][2] == 0 or self._map.generals[self.targetPlayer] != None or self.generalApproximations[self.targetPlayer][3] == None):
						playerApproxArr = self.generalApproximations[self.targetPlayer]
						approxGen = playerApproxArr[3]
						armyToSearch = min(self._map.players[self._map.player_index].standingArmy / 50 + 1, 30)
						logging.info(" !!! ~~~~~~~~~ !!!! \nsearching for {} army depth {} dest bfs kill on GENERAL APPROX {},{}".format(armyToSearch, len(self.target_player_gather_targets) / 8, approxGen.x, approxGen.y))
						self.viewInfo.addSearched(approxGen)
						sumAdj = 0
	
						(killStart, killPath) = dest_breadth_first_target(self._map, [approxGen], armyToSearch, 0.1, max(2, len(self.target_player_gather_targets) / 10), undiscNeg, dontEvacCities=True)
						if (killPath != None):
							self.info("found depth {} dest bfs kill on GENERAL APPROX {},{} \n{}".format(killStart.turn, approxGen.x, approxGen.y, stringPath(killPath)))
							paths.append((killStart, killPath))
						if (len(paths) == 0):				
							armyToSearch = min(self._map.players[self._map.player_index].standingArmy / 10 + 1, 50)
							logging.info(" !!! ~~~~~~~~~ !!!! \nsearching for {} army depth {} dest bfs kill on GENERAL APPROX {},{}".format(armyToSearch, len(self.target_player_gather_targets) / 4, approxGen.x, approxGen.y))
							sumAdj = 0
	
							(killStart, killPath) = dest_breadth_first_target(self._map, [approxGen], armyToSearch, 0.1, len(self.target_player_gather_targets) / 4, undiscNeg, dontEvacCities=True)
							if (killPath != None):
								self.info("found depth {} dest bfs kill on GENERAL APPROX {},{} \n{}".format(killStart.turn, approxGen.x, approxGen.y, stringPath(killPath)))
								paths.append((killStart, killPath))
				if not self.allIn and (len(paths) == 0):
					# TODO REDUCE CITYDEPTHSEARCH NOW THAT WE HAVE CITY FIGHTING BASIC IMPL
					cityDepthSearch = int(self._map.players[self._map.player_index].tileCount**0.5 / 2)
					#if (len(self.enemyCities) > 5):
					#	cityDepthSearch = 5
					for enemyCity in self.enemyCities:
						logging.info("searching for depth {} dest bfs kill on city {},{}".format(cityDepthSearch, enemyCity.x, enemyCity.y))
						self.viewInfo.addSearched(enemyCity)
						armyToSearch = self.get_target_army_inc_adjacent_enemy(enemyCity)
						(killStart, killPath) = dest_breadth_first_target(self._map, [enemyCity], armyToSearch, 0.1, cityDepthSearch, negativeTiles, dontEvacCities=True)
						if (killPath != None):
							self.info("found depth {} dest bfs kill on city {},{} \n{}".format(killStart.turn, enemyCity.x, enemyCity.y, stringPath(killPath)))
							if (killPath.tile.isCity):
								killPath.move_half = True
							paths.append((killStart, killPath))
					(pathStart, path, gatherMove) = self.capture_cities(targets, negativeTiles)
					if pathStart != None:
						paths.append((pathStart, path))
					elif gatherMove != None:
						return gatherMove

				#Gather to threat
				#if (self.threat != None and threat.threatPlayer == self.targetPlayer and self.curPath == None):
				#	threatNextTile = self.threat.path.pathMove.move.dest
				#	move = self.gather_to_target_tile(threatNextTile, 0.1, self.threat.turns)
				#	if (self.is_move_safe_valid(move)):
				#		logging.info("////////// Gathering to threat {},{}: {},{} -> {},{}".format(threatNextTile.x, threatNextTile.y, move.source.x, move.source.y, move.dest.x, move.dest.y))
				#		return move
				if not self.allIn and (len(paths) == 0):
					for city in self._map.players[self._map.player_index].cities:
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
							(killStart, killPath) = dest_breadth_first_target(self._map, [largestEnemyAdj], sumAdj - largestEnemyAdj.army + 3, 0.2, 6, negativeTiles)
							if (killPath != None):
								self.info("found depth {} dest bfs kill on general vision tile {},{}\n{}".format(killPath.turn, largestEnemyAdj.x, largestEnemyAdj.y, stringPath(killPath)))
								paths.append((killStart, killPath))
				# if largestEnemyAdj != None:
				# 	logging.info("KILLING GENERAL VISION TILES searching for dest bfs kill on tile {},{}".format(largestEnemyAdj.x, largestEnemyAdj.y))
				# 	self.viewInfo.addSearched(largestEnemyAdj)
				# 	(killStart, killPath) = self.dest_breadth_first_kill(largestEnemyAdj, sumAdj - largestEnemyAdj.army + 5, 0.2, 11, negativeTiles)
				# 	if (killPath != None):
				# 		logging.info("found depth {} dest bfs kill on general vision tile {},{}\n{}".format(killPath.turn, largestEnemyAdj.x, largestEnemyAdj.y, stringPath(killPath)))
				# 		paths.append((killStart, killPath))


			paths = sorted(paths, key=lambda x: x[1].turn)

		if len(paths) == 0 and (self.curPath == None or self.curPath.parent == None):
			tryGather = False
			player = self._map.players[self._map.player_index]
			modVal = 0
			enemyGather = False
			neutralGather = len(targets) <= 2
			turn = self._map.turn
			tiles = player.tileCount
			if tiles < 50:
				if turn % 50 < 20:
					tryGather = True
				if turn % 50 > 40 and turn % 50 < 46:
					enemyGather = True
			elif tiles < 75:
				if turn % 50 < 24:
					tryGather = True
				if turn % 50 > 40 and turn % 50 < 46:
					enemyGather = True
			elif tiles < 90:
				if turn % 50 < 30:
					tryGather = True
				if turn % 50 > 38 and turn % 50 < 45:
					enemyGather = True
			elif tiles < 110:
				if turn % 100 < 50:
					tryGather = True
				if turn % 100 > 80 and turn % 100 < 92:
					enemyGather = True
			elif tiles < 150:
				if turn % 100 < 60:
					tryGather = True
				if turn % 100 > 80 and turn % 100 < 92:
					enemyGather = True
			elif tiles < 200:
				if turn % 200 < 120:
					tryGather = True
				if turn % 100 > 80 and turn % 100 < 92:
					enemyGather = True
			elif tiles < 250:
				if turn % 200 < 130:
					tryGather = True
				if turn % 100 > 80 and turn % 100 < 92:
					enemyGather = True
			else:
				if turn % 200 < 140:
					tryGather = True
				if turn % 100 > 80 and turn % 100 < 92:
					enemyGather = True
			
			tileDeficitThreshold = self._map.players[self.targetPlayer].tileCount * 1.0 - 3
			if (self.makingUpTileDeficit):
				tileDeficitThreshold = self._map.players[self.targetPlayer].tileCount * 1.1 + 10
			
			if len(targets) > 2 and player.tileCount < tileDeficitThreshold and not self.all_in_counter > 40:
				logging.info("ayyyyyyyyyyyyyyyyyyyyyyyyy set enemyGather to True because we're behind on tiles")
				enemyGather = True
				neutralGather = True
				self.makingUpTileDeficit = True
			else:
				self.makingUpTileDeficit = False

			if (self.makingUpTileDeficit):
				leafMove = self.find_leaf_move(allLeaves)
				if (None != leafMove):
					return leafMove

			if tryGather:
				gatherTargets = targets.copy()
				gatherNegatives = negativeTiles.copy()
				negSet = set()
				#for tile in self.largePlayerTiles:
				#	gatherNegatives.add(tile)
				if (self.curPath != None):
					negSet.add(self.curPath.tile)


				if (enemyGather or neutralGather) and not self.all_in_counter > 40:
					# ENEMY TILE GATHER
					leafGatherTargets = []
					#for leaf in filter(lambda move: move.dest.army > 0 and (move.source.player == move.dest.player or move.source.army - 1 > move.dest.army), self.leafMoves):
					for leaf in filter(lambda move: move.dest.player == self.targetPlayer or neutralGather, self.leafMoves):
						if not (leaf.dest.isCity and leaf.dest.player == -1):
							leafGatherTargets.append(leaf.dest)
					# removed as this doesn't actually help due to low gather distance
					#for node in gatherTargets:
					#	leafGatherTargets.append(node)
					for city in player.cities:
						gatherNegatives.add(city)
					negSet.add(general)
					leafGatherDepth = player.tileCount**0.25 - 1
					logging.info("    ****   leafGatherDepth: {}".format(leafGatherDepth))
					leafGatherNodes = self.breadth_first_gather(leafGatherTargets, 1.0, leafGatherDepth, gatherNegatives, negSet)				
					leafMove = self.get_gather_move(leafGatherNodes, None, minGatherAmount = 1, pruneThreshold = 80, preferNeutral = True)
					if (leafMove != None):
						self.info("LEAF MST GATHER MOVE! {},{} -> {},{}  leafGatherDepth: {}".format(leafMove.source.x, leafMove.source.y, leafMove.dest.x, leafMove.dest.y, leafGatherDepth))
						self.gatherNodes = leafGatherNodes
						self.curGather = None
						#self.curPath = None
						#self.curPathPrio = -1
						return self.move_half_on_repetition(leafMove, 6)

				# TARGET PATH GATEHR
				self.gatherNodes = self.breadth_first_gather(gatherTargets, 1.0, 40, gatherNegatives, negSet)
				
				move = self.get_gather_move(self.gatherNodes, None)
				if (move != None):
					self.info("TARGET-PATH GATHER MOVE! {},{} -> {},{}".format(move.source.x, move.source.y, move.dest.x, move.dest.y))
					self.curGather = self.gatherNodes
					#self.curPath = None
					#self.curPathPrio = -1
					return self.move_half_on_repetition(move, 6)
			#if len(paths) == 0 and (self.curPath == None or self.curPath.parent == None) and self.worth_attacking_target() and self.lastTargetAttackTurn + 30 < self._map.turn:
			elif self.curGather != None and self.targetPlayer >= 0:
				move = self.get_gather_move(self.gatherNodes, None)
				if (move != None):
					self.info("POST-GATHER-COMPLETE GATHER MOVE! {},{} -> {},{}".format(move.source.x, move.source.y, move.dest.x, move.dest.y))
					#self.curPath = None
					#self.curPathPrio = -1
					return self.move_half_on_repetition(move, 6)
				else:
					logging.info(".\n ..\n  ...\n   ....\n    .....self.curGather MOVE WAS NULL REEEEEEEEEEEEEEEEEEEEE")
					self.curGather = None
			#elif self.worth_attacking_target():
			#	logging.info("\n\nOOOOOOOOOOOOMG attacking\n\n")
			#	self.info("attacking because self.worth_attacking_target() POSTGATHER")
			#	path = self.get_value_per_turn_subsegment(reverse_path_tuple(self.target_player_gather_path))
			#	if path != None and path[0] != None:
			#		#paths.append(path)
			#		self.lastTargetAttackTurn = self._map.turn
			#		return self.move_half_on_repetition(Move(path[1].tile, path[1].parent.tile, path[1].move_half), 7, 3)
			#	else:
			#		logging.info("WTF PATH WAS NONEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEE")
			
			leafMove = self.find_leaf_move(allLeaves)
			if (None != leafMove):
				return leafMove
			

		if (self.curPath == None or self.curPath.parent == None):
					
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
				
				toAttack = random.sample(attackable, min(1, len(attackable)))


				if (len(paths) == 0 and len(toAttack) > 0):
					for attackee in toAttack:
						self.viewInfo.addSearched(attackee)
					self.attacks += 1
					logging.info("\n------------\nGathering to attack {} tiles\n------------\n".format(len(toAttack)))
					self.info("weightedbreadthsearch on toAttack")
					paths = self.WeightedBreadthSearch(toAttack, 75, 0.15, -2, -1, 10, negativeTiles)
					if (highPriAttack):
						self.attackFailedTurn = self._map.turn
					if (len(paths) == 0 and highPriAttack):
						self.countFailedQuickAttacks += 1
						logging.info("\n------------\nCOULD NOT FIND QUICK ROUTE TO ATTACK TILES {} TIMES, RUNNING LONGER SEARCH\n------------\n".format(self.countFailedQuickAttacks))
						(pathStart, path) = dest_breadth_first_target(self._map, toAttack, 10, 0.2, 90, negativeTiles, noNeutralCities=False)
						if path != None:
							self.info("assorted attack path")
							paths.append((pathStart, path))
						#paths = self.WeightedBreadthSearch(toAttack, 90, 1.0, -2, -1, 10, negativeTiles)
						
					elif len(paths) == 0:
						logging.info("failed a non-highpri attack, a* searching for undiscovered kill")
						self.failedUndiscoveredSearches += 1
						if self.failedUndiscoveredSearches > 5:
							self.failedUndiscoveredSearches = 0
							(pathEnd, path) = a_star_kill(self._map, self.largePlayerTiles, toAttack[0], 0.10, 50, self.general_safe_func_set)
							if (path != None):
								self.info("found a* path to attackable: " + stringPath(path))
								self.curPath = path
					self.curPathPrio = 8

				if (len(paths) == 0): #if we're not attacking a general. God my code is bad						
					if (len(allLeaves) > 0):
						#gather on leaf
						#TODO pick good leaf targets. Cities? Enemy 1's? Emptier areas of the map?
						
						destinations = []
						if not self.allIn and (self.gathers % 3 == 0):
							logging.info("    Gather to enemy cities")
							destinations.extend(self.enemyCities)
						if (len(destinations) == 0 and (self.targetPlayer == -1 or self._map.turn < 50)):
							logging.info("    Gather to leaves")
							moves = self.find_target_gather_leaves(allLeaves)
							if (len(moves) == 0):
								logging.info("\n\nNO LEAF MOVES FOUND??????????\n")
							includeNeutralTiles = True
							botPlayer = self._map.players[self.general.player]
							if self.targetPlayer >= 0 and botPlayer.tileCount > 1.1 * self._map.players[self.targetPlayer].tileCount + 3:
								includeNeutralTiles = False
								logging.info("SKIPPING NEUTRAL TILES ON TARGET GATHER LEAVES!")
							for move in moves:
								if move.dest.player == self.targetPlayer or (move.dest.player == -1 and includeNeutralTiles):
									destinations.append(move.dest)
						if (len(destinations) > 0):
							targets = destinations
							for dest in targets:
								self.viewInfo.addSearched(dest)
							self.info("non-general assorted weightedbreadthsearch")
							
							if (self._map.turn >= 50):
								#use BFS only early game to avoid wasted moves
								paths = self.WeightedBreadthSearch(targets, 50, 0.11, -2, -1, 10, negativeTiles)
							else:
								(pathStart, path) = dest_breadth_first_target(self._map, destinations, 1, 0.2, 90, negativeTiles, noNeutralCities=False)
								if path != None:
									self.info("non-general assorted attack path dest BFS because turn < 50")
									paths.append((pathStart, path))
							self.curPathPrio = 1
							if (len(paths) == 0):
								for dest in targets:
									logging.info("NO PATHS WERE RETURNED FOR {},{}??????????".format(dest.x, dest.y))
								if (targets[0].isCity):
									outstandingArmy = self._map.players[self._map.player_index].standingArmy - self.general.army
									gather = outstandingArmy * 0.2
									self.info("Gathering to general to avoid stalling on city taking")
									paths = self.WeightedBreadthSearch([self.general], 50, 0.11, -2, gather + self.general.army, 10, negativeTiles)
			

									
				if (len(paths) > 0):
					self.curPath = paths[0][1]
					self.gathers += 1
				else:
					self.curPathPrio = -1
		if (self.curPath != None):
			while ((self.curPath.tile.army <= 1 or self.curPath.tile.player != self._map.player_index) and self.curPath.parent != None):
				if (self.curPath.tile.army <= 1):
					logging.info("!!!!\nMove was from square with 1 or 0 army\n!!!!! {},{} -> {},{}".format(self.curPath.tile.x, self.curPath.tile.y, self.curPath.parent.tile.x, self.curPath.parent.tile.y))
				elif (self.curPath.tile.player != self._map.player_index):
					logging.info("!!!!\nMove was from square OWNED BY THE ENEMY\n!!!!! [{}] {},{} -> {},{}".format(self.curPath.tile.player, self.curPath.tile.x, self.curPath.tile.y, self.curPath.parent.tile.x, self.curPath.parent.tile.y))
				self.curPath = self.curPath.parent
				
			if (self.curPath.parent != None):
				dest = self.curPath.parent.tile
				source = self.curPath.tile
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
							self.curPath = paths[0][1]
							logging.info("Found path to cap the city: {}".format(stringPath(self.curPath)))
						elif dest.isGeneral:
							self.attackFailedTurn = self._map.turn
							self.curPath = None	
							self.curPathPrio = -1
						else:							
							self.curPath = None	
							self.curPathPrio = -1

				if (self.curPath != None and self.curPath.parent != None and self.curPath.tile.isGeneral and not self.general_move_safe(self.curPath.parent.tile)):
					#self.curPath = None	
					#self.curPathPrio = -1
					#logging.info("General move in path would have violated general min army allowable. Repathing.")					
					if (self.general_move_safe(self.curPath.parent.tile, move_half=True)):
						logging.info("General move in path would have violated general min army allowable. Moving half.")
						move = Move(self.curPath.tile, self.curPath.parent.tile, True)
						return move
					else:
						self.curPath = None	
						self.curPathPrio = -1
						logging.info("General move in path would have violated general min army allowable. Repathing.")					

				else:
					cleanPath = False
					while self.curPath != None and not cleanPath:
						if (self.curPath.tile in negativeTiles and self.curPath.tile.army > 5):
							tile = self.curPath.tile
							# self.curPathPrio = -1
							logging.info("\n\n\n~~~~~~~~~~~\nSKIPPED: Move was from a negative tile {},{}\n~~~~~~~~~~~~~\n\n~~~\n".format(tile.x, tile.y))
							self.curPath = None
							self.curPathPrio = -1
						elif (self.curPath.parent != None and self.curPath.parent.parent != None and self.curPath.tile == self.curPath.parent.parent.tile and self.curPath.parent.tile.player == self.curPath.tile.player):
							logging.info("\n\n\n~~~~~~~~~~~\nCleaned double-back from path\n~~~~~~~~~~~~~\n\n~~~\n")
							self.curPath = self.curPath.parent
						elif (self.curPath.tile.player != self._map.player_index or self.curPath.tile.army < 2):
							logging.info("\n\n\n~~~~~~~~~~~\nCleaned useless move from path\n~~~~~~~~~~~~~\n\n~~~\n")
							self.curPath = self.curPath.parent
						else:
							cleanPath = True
					if (self.curPath != None and self.curPath.parent != None):
						if self.curPath.tile == self.general and not self.general_move_safe(self.curPath.parent.tile, self.curPath.move_half):
							self.curPath = None
							self.curPathPrio = -1
						else:
							move = Move(self.curPath.tile, self.curPath.parent.tile)
							if (self.curPath.move_half):
								move.move_half = True
							end = time.time()
							logging.info("Path Move Duration: {}".format(end - start))
							return self.move_half_on_repetition(move, 10, 6)
				

			self.curPath = None
		self.curPathPrio = -1
		end = time.time()
		self.info("!!!!\nFOUND NO MOVES, GONNA GATHER {}\n!!!!!".format(end - start))
		logging.info("\n\n!-!-!-!-!-! \n         WHEE WHOO WHEE WHOO NO MOVES \n       WE GATHERIN NOW CUZ NO MOVES \n!-!-!-!-!-!")
		
		kingsPath = get_tile_set_from_path_tuple(self.get_path_to_target_player())
		
		gathers = self.breadth_first_gather(kingsPath, 1.0, 50, None)
		self.gatherNodes = gathers
		move = self.get_gather_move(gathers, None)
		if (self.is_move_safe_valid(move)):
			return move
		elif move != None:
			self.info("Found-no-moves-gather move {},{} -> {},{} was not safe or valid!".format(move.source.x, move.source.y, move.dest.x, move.dest.y))
		else:
			self.info("Found-no-moves-gather found no move ?????")
		if (allowRetry):
			logging.info("Retrying.")
			return self.dummyMover(False)
		return None
	

	def gather_to_target(self, target, maxTime, maxDepth, gatherNegatives = None, negativeSet = None):
		targets = get_tile_set_from_path_tuple(self.get_path_to_target(target, maxTime, maxDepth, True))
		gatherNodes = self.breadth_first_gather(targets, maxTime, maxDepth, gatherNegatives, negativeSet)
		move = self.get_gather_move(gatherNodes, None)
		if (move != None):
			self.gatherNodes = gatherNodes
			#self.curPath = None
			#self.curPathPrio = -1
			return self.move_half_on_repetition(move, 5)
		return None


	def gather_to_target_tile(self, target, maxTime, maxDepth, gatherNegatives = None, negativeSet = None):
		gatherNodes = self.breadth_first_gather([target], maxTime, maxDepth, gatherNegatives, negativeSet)
		move = self.get_gather_move(gatherNodes, None, target.army + 1, 0)
		if (move != None):
			self.gatherNodes = gatherNodes
			#self.curPath = None
			#self.curPathPrio = -1
			return self.move_half_on_repetition(move, 5)
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
		player = self._map.players[self._map.player_index]
		enemyPlayer = self._map.players[enemyGen.player]

		armyBase = player.standingArmy - self.general_min_army_allowable()

		if (enemyPlayer.tileCount == 1 and enemyGen.army > 30 and self._map.remainingPlayers > 2):
			return False

		if (armyBase * 0.7 < enemyGen.army + 15):
			return False
		return True

	def enemy_army_near(self, tile):
		enemyNear = 0
		for adj in tile.adjacents:
			if (adj.player != self._map.player_index and adj.player != -1):
				enemyNear += adj.army
		return enemyNear

	
	def explore_target_player_undiscovered(self, negativeTiles):
		if self._map.turn < 100 or self.targetPlayer == -1 or self._map.generals[self.targetPlayer] != None:
			return (None, None)
		enemyUndiscBordered = []
		if self.targetPlayer != -1:
			for tile in self.allUndiscovered:
				for move in tile.moveable:
					if move.player == self.targetPlayer:
						enemyUndiscBordered.append(move)
		return dest_breadth_first_target(self._map, enemyUndiscBordered, 5, 0.01, 3, negativeTiles, self._map.player_index, False, 1, True)
					
			

	def breadth_first_gather(self, startTiles, maxTime = 0.1, maxDepth = 30, negativeTiles = None, avoidTiles = None):
		origStartTiles = startTiles
		startTiles = set(startTiles)
		self.leafValueGrid = [[None for x in range(self._map.rows)] for y in range(self._map.cols)]
		searchingPlayer = self._map.player_index
		frontier = PriorityQueue()
		visitedBack = [[None for x in range(self._map.rows)] for y in range(self._map.cols)]
		visitedFwd = [[None for x in range(self._map.rows)] for y in range(self._map.cols)]
		visitedSet = set()
		# visitedSet.add((goal.x, goal.y))
		# visited[goal.x][goal.y][0] = (startArmy, None)

		# sort on distance, then army, then x and y (to stop the paths from shuffling randomly and looking annoying)
		start = time.time()
		for tile in startTiles:
			startArmy = tile.army
			if (tile.player != searchingPlayer):
				startArmy = 0 - tile.army
			frontier.put((0, 0 - startArmy, tile.x, tile.y, tile, None, 0))
		iter = 0
		depthEvaluated = 0
		while not frontier.empty():
			iter += 1
			if (iter % 100 == 0 and time.time() - start > maxTime):
				break
			
			(dist, popArmy, x, y, current, cameFrom, neutCount) = frontier.get()
			army = 0 - popArmy
			
			
			if (current in visitedSet):
				continue
			if (current.mountain or not current.discovered and current.isobstacle()):
				continue
			if (current.isCity and current.player != searchingPlayer and not current in startTiles):
				continue
			visitedSet.add(current)
			visitedBack[current.x][current.y] = cameFrom
			if cameFrom != None:
				visitedFwd[cameFrom.x][cameFrom.y] = current
			x = current.x
			y = current.y
			# if (current.isGeneral and current.player == searchingPlayer and not self.general_move_safe(visited[current.x][current.y][dist - 1][1])):
			# if (current.isGeneral and current.player == searchingPlayer):
			# 	continue

			if dist > depthEvaluated:
				depthEvaluated = dist
			if (dist <= maxDepth):
				for next in current.moveable: #new spots to try
					if avoidTiles != None and next in avoidTiles:
						continue
					# self.viewInfo.evaluatedGrid[next.x][next.y] += 1
					# inc = 0 if not (next.isCity or next.isGeneral) else dist / 2
					#new_cost = cost_so_far[current] + graph.cost(current, next)
					nextArmy = army - 1
					if (negativeTiles == None or next not in negativeTiles):
						if (searchingPlayer == next.player):
							nextArmy += next.army
						else:
							nextArmy -= next.army
					newNeutCount = neutCount
					if (next.player == -1):
						newNeutCount += 1
					newDist = dist + 1
					# if newDist not in visited[next.x][next.y] or visited[next.x][next.y][newDist][0] < nextArmy:
					# 	visited[next.x][next.y][newDist] = (nextArmy, current)
					frontier.put((newDist, 0 - nextArmy, next.x, next.y, next, current, newNeutCount))

		logging.info("BFS GATHER ITERATIONS {}, DURATION: {}, DEPTH: {}".format(iter, time.time() - start, depthEvaluated))

		result = self.breadth_first_gather_rebuild(startTiles, visitedBack, self._map.player_index)
		
		return result

	def breadth_first_gather_rebuild(self, startTiles, fromMap, searchingPlayer):
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
		thisNode = GatherNode(tile, fromTile, turn)
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
		if thisNode.tile.isCity:
			thisNode.value -= 10
		if (thisNode.value > 0):
			self.leafValueGrid[thisNode.tile.x][thisNode.tile.y] = thisNode.value
		# logging.info("{},{} ({}  {})".format(thisNode.tile.x, thisNode.tile.y, thisNode.value, thisNode.gatherTurns))
		return thisNode

	def get_gather_move(self, gathers, parent, minGatherAmount = 0, pruneThreshold = None, preferNeutral = True):
		if pruneThreshold == None:
			player = self._map.players[self.general.player]
			pruneThreshPercent = 50
			pruneThreshold = self.get_median_tile_value(pruneThreshPercent) - 1
			logging.info("~!~!~!~!~!~!~ MEDIAN {}: {}".format(20, self.get_median_tile_value(20)))
			logging.info("~!~!~!~!~!~!~ MEDIAN {}: {}".format(35, self.get_median_tile_value(35)))
			logging.info("~!~!~!~!~!~!~ MEDIAN {}: {}".format(50, self.get_median_tile_value(50)))
			logging.info("~!~!~!~!~!~!~ MEDIAN {}: {}".format(65, self.get_median_tile_value(65)))
			logging.info("~!~!~!~!~!~!~ MEDIAN {}: {}".format(75, self.get_median_tile_value(75)))
			logging.info("~!~!~!~!~!~!~ pruneThreshold {}: {}".format(pruneThreshPercent, pruneThreshold))

			pruneThreshold = (player.standingArmy - self.general.army) / player.tileCount
			logging.info("~!~!~!~!~!~!~ pruneThreshold via average {}%: {}".format(pruneThreshPercent, pruneThreshold))
		start = time.time()
		logging.info("Gathering :)")
		move = self._get_gather_move_int(gathers, parent, minGatherAmount, pruneThreshold, preferNeutral)
		if move == None and pruneThreshold > 0:
			newThreshold = max(0, self.get_median_tile_value(40) - 2)
			logging.info("\nEEEEEEEEEEEEEEEEEEEEEEEE\nEEEEEEEEE\nEE\nNo move found for pruneThreshold {}, retrying with {}".format(pruneThreshold, newThreshold))
			move = self._get_gather_move_int(gathers, parent, minGatherAmount, newThreshold, preferNeutral)
		if move == None:
			logging.info("\nNo move found......... :(")
			newThreshold = 0
			logging.info("\nEEEEEEEEEEEEEEEEEEEEEEEE\nEEEEEEEEE\nEE\nNo move found for pruneThreshold {}, retrying with {}".format(pruneThreshold, newThreshold))
			move = self._get_gather_move_int(gathers, parent, minGatherAmount, newThreshold, preferNeutral)
		if move == None:
			logging.info("\nNo move found......... :(")
		logging.info("GATHER MOVE DURATION: {}".format(time.time() - start))
		return move

	def get_median_tile_value(self, percentagePoint = 50):
		tiles = [tile for tile in self._map.players[self.general.player].tiles]
		tiles = sorted(tiles, key = lambda tile: tile.army)
		tileIdx = max(0, len(tiles)*percentagePoint//100 - 1)
		return tiles[tileIdx].army


	def _get_gather_move_int(self, gathers, parent, minGatherAmount = 0, pruneThreshold = 0, preferNeutral = False):
		move = None
		maxGather = None
		for gather in gathers:
			#if maxGather == None or (gather.value - gather.tile.army) / gather.gatherTurns > (maxGather.value - maxGather.tile.army) / maxGather.gatherTurns:
			if (gather.value / gather.gatherTurns > pruneThreshold and gather.value >= minGatherAmount 
					and compare_gathers(maxGather, gather, preferNeutral)):
				maxGather = gather
		# if maxGather != None and (parent == None or maxGather.value / maxGather.gatherTurns > parent.value / parent.gatherTurns):
		if maxGather != None:
			gatherWorthwhile = is_gather_worthwhile(maxGather, parent)
			if parent == None or gatherWorthwhile:
				move = self._get_gather_move_int(maxGather.children, maxGather, minGatherAmount, pruneThreshold, preferNeutral)
			if self.is_move_safe_valid(move):
				logging.info("Returning child move {},{} -> {},{}".format(move.source.x, move.source.y, move.dest.x, move.dest.y))
				return move
			if parent != None:
				if maxGather.tile.army <= 1 or maxGather.tile.player != self._map.player_index:
					logging.info("WTF tried to move {},{} with 1 or less army :v".format(maxGather.tile.x, maxGather.tile.y))
				elif maxGather.value > 0:
					logging.info("Returning {},{} -> {},{}".format(maxGather.tile.x, maxGather.tile.y, parent.tile.x, parent.tile.y))
					parent.children.remove(maxGather)
					return Move(maxGather.tile, parent.tile)
		logging.info("FUCK! NO POSITIVE GATHER MOVE FOUND")
		return None

	def get_threat_killer_move(self, threat):
		threatSource = threat.path.pathMove.move.source
		saveTile = None
		for tile in threatSource.moveable:
			if tile.player == self._map.player_index and tile != threat.path.pathMove.move.dest:
				if threat.threatValue - tile.army + 1 < 0 and (saveTile == None or saveTile.army > tile.army):
					logging.info("reeee\n reeeee\n   reeeeeeeeee\n       reeeeeeeeeeeeeeeee\nFUCK YES KILLING THREAT TILE {},{}".format(tile.x, tile.y))
					saveTile = tile
		if saveTile != None:
			return Move(saveTile, threatSource)
		return None

	def get_cities_bordered_by_enemy(self, enemyTileCount = 1):
		player = self._map.players[self._map.player_index]
		cities = where(player.cities, lambda x: x.player == player.index and count(x.adjacents, lambda y: y.player >= 0 and y.player != player.index) >= enemyTileCount)
		return cities


	#def get_gather_move_(self, gathers, parent):
	#	start = time.time()
	#	move = None
	#	maxGather = None
	#	for gather in gathers:
	#		if maxGather == None or gather.value / gather.gatherTurns > maxGather.value / maxGather.gatherTurns:
	#			maxGather = gather
	#	# if maxGather != None and (parent == None or maxGather.value / maxGather.gatherTurns > parent.value / parent.gatherTurns):
	#	if maxGather != None:
	#		gatherWorthwhile = False
	#		if (parent != None):
	#			gatherWorthwhile = maxGather.value > parent.value / 4
	#			logging.info("Gather worthwhile? {} {},{}   maxGath {}  parent {}".format(gatherWorthwhile, maxGather.tile.x, maxGather.tile.y, maxGather.value, parent.value))
	#		else:
	#			logging.info("No parent. {},{}   maxGath {}".format(maxGather.tile.x, maxGather.tile.y, maxGather.value))
	#		if parent == None or gatherWorthwhile:
	#			move = self.get_gather_move(maxGather.children, maxGather)
	#		logging.info("GATHER MOVE DURATION: {}".format(time.time() - start))
	#		if move != None and self.is_move_safe(move):
	#			return move
	#		if parent != None:
	#			if maxGather.tile.army <= 1 or maxGather.tile.player == -1:
	#				logging.info("WTF tried to move {},{} with 1 or less army :v".format(maxGather.tile.x, maxGather.tile.y))
	#			else:
	#				return Move(maxGather.tile, parent.tile)
	#	logging.info("FUCK! NO GATHER MOVE FOUND")
	#	return None



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




	def capture_cities(self, targets, negativeTiles):
		maxDist = len(targets) * 0.6
		isNeutCity = False
		(pathStart, path) = self.find_enemy_city_path(targets, negativeTiles)
		player = self._map.players[self.general.player]
		targetPlayer = None
		if self.targetPlayer != -1:
			targetPlayer = self._map.players[self.targetPlayer]
		#if path == None and (targetPlayer == None or (player.standingArmy > targetPlayer.standingArmy + 60 and player.cityCount < targetPlayer.cityCount + 1) or player.cityCount < targetPlayer.cityCount):
		if path == None and (targetPlayer == None or player.cityCount < targetPlayer.cityCount or (player.standingArmy > 700 and player.cityCount < targetPlayer.cityCount * 1.3)):
			logging.info("..........NO ENEMY CITY PATH FOUND, searching neutral city target.........")
			(pathStart, path) = self.find_neutral_city_path(targets, negativeTiles)
			isNeutCity = True

		if path != None:
			target = path.tile
			self.viewInfo.lastEvaluatedGrid[target.x][target.y] = 140
			targetArmy = 1 + self.enemy_army_near(target) * 2
			searchDist = maxDist
			if not isNeutCity:
				targetArmy = min(10, target.army / 4 + self.enemy_army_near(target) * 1.2)
				searchDist = maxDist // 2 + 1
			logging.info("xxxxxxxxx\n  xxxxx\n    SEARCHED AND FOUND NEAREST NEUTRAL / ENEMY CITY {},{} dist {}. Searching {} army dist {}\n  xxxxx\nxxxxxxxx".format(target.x, target.y, pathStart.turn, targetArmy, searchDist))
			(killStart, killPath) = dest_breadth_first_target(self._map, [target], targetArmy, 0.1, searchDist, negativeTiles, dontEvacCities=True)
			if (killPath != None):
				logging.info("found depth {} dest bfs kill on Neutral or Enemy city {},{} \n{}".format(killStart.turn, target.x, target.y, stringPath(killPath)))
				self.info("City killpath {},{}  setting gatherNodes to None".format(target.x, target.y))
				self.viewInfo.lastEvaluatedGrid[target.x][target.y] = 300
				self.curGather = None
				self.gatherNodes = None
				return (killStart, killPath, None)
			else:
				gatherDist = max(10, len(targets) / 2) + (30 - self._map.turn % 25) / 3
				negativeTiles = negativeTiles.copy()
				#negativeTiles.add(self.general)
				logging.info("self.gather_to_target_tile gatherDist {}".format(gatherDist))
				move = self.gather_to_target_tile(target, 0.1, gatherDist)
				if move != None:
					logging.info("xxxxxxxxx\n  xxxxx\n         GATHERING TO CITY {},{}\n  xxxxx\nxxxxxxxx".format(target.x, target.y))
					self.info("Gathering to target city {},{}".format(target.x, target.y))
					self.viewInfo.lastEvaluatedGrid[target.x][target.y] = 300
					return (None, None, move)
				
				logging.info("xxxxxxxxx\n  xxxxx\n    GATHERING TO CITY FAILED :( {},{} \n  xxxxx\nxxxxxxxx".format(target.x, target.y))
		else:
			logging.info("xxxxxxxxx\n  xxxxx\n    NO ENEMY CITY FOUND / Neutral city prioritized??? \n  xxxxx\nxxxxxxxx")
		return (None, None, None)

	def mark_tile(self, tile, alpha = 100):
		self.viewInfo.lastEvaluatedGrid[tile.x][tile.y] = alpha

	def find_neutral_city_path(self, targets, negativeTiles):
		maxDist = 0
		playerArmy = self._map.players[self._map.player_index].standingArmy
		# our general has less than 500 standing army, only target cities owned by our target player
		searchLambda = lambda tile, dist, army: tile.isCity and tile.player == -1
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
		return breadth_first_find(self._map, [self.general], searchLambda, 0.1, maxDist)


	def find_enemy_city_path(self, targets, negativeTiles):
		maxDist = 0
		playerArmy = self._map.players[self._map.player_index].standingArmy
		# our general has less than 500 standing army, only target cities owned by our target player
		searchLambda = lambda tile, dist, army: tile.isCity and tile.player == self.targetPlayer
		if playerArmy > 1000: # our general has greater than 1000 standing army, capture neutrals up to 0.8* the dist to enemy general
			maxDist = len(targets) * 0.95
		elif playerArmy > 700: # our general has greater than 700 standing army, capture neutrals
			maxDist = len(targets) * 0.85
		elif playerArmy > 500:
			maxDist = len(targets) * 0.75
		elif playerArmy > 400:
			maxDist = len(targets) * 0.7
		else:
			maxDist = len(targets) * 0.65
		return breadth_first_find(self._map, [self.general], searchLambda, 0.1, maxDist)

	def get_value_per_turn_subsegment(self, path, minFactor = 1.0, minLengthFactor = 0.25):
		pathMoveList = get_tile_list_from_path_tuple(path)
		totalCount = len(pathMoveList)
		fullValue = 0
		for tile in pathMoveList:
			if tile.player == self.general.player:
				fullValue += tile.army - 1
		i = 1
		curSum = 0
		maxValuePerTurn = 0
		
		logging.info("len(pathMoveList) == {}".format(len(pathMoveList)))
		for tile in reversed(pathMoveList):
			if tile.player == self.general.player:
				curSum += tile.army - 1
			valuePerTurn = curSum / i
			logging.info("[{}]  {},{}  value per turn was {}".format(i, tile.x, tile.y, "%.1f" % valuePerTurn))
			if valuePerTurn >= maxValuePerTurn and i <= totalCount and i > totalCount * minLengthFactor:
				logging.info("![{}]  {},{}  new max!    {} > {}".format(i, tile.x, tile.y, "%.1f" % valuePerTurn, "%.1f" % maxValuePerTurn))
				maxValuePerTurn = valuePerTurn
			i += 1

		lastValueIndex = 0
		i = 1
		curSum = 0
		for tile in reversed(pathMoveList):
			if tile.player == self.general.player:
				curSum += tile.army - 1
			valuePerTurn = curSum / i
			logging.info("[{}]  {},{}   2nd pass {}".format(i, tile.x, tile.y, "%.1f" % valuePerTurn))
			if valuePerTurn >= maxValuePerTurn * minFactor:
				lastValueIndex = i
				logging.info("!![{}]  {},{}    minFactor max   {} > {}".format(i, tile.x, tile.y, "%.1f" % valuePerTurn, "%.1f" % maxValuePerTurn))
			i += 1
		logging.info("       -----   ---- lastValueIndex was {}".format(lastValueIndex))
		if lastValueIndex > 0:
			i = totalCount
			while i > lastValueIndex:
				path = (path[0], path[1].parent)
				logging.info("!![{}]  {},{}  set to start".format(i, path[1].tile.x, path[1].tile.y))
				i -= 1
		return path

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
			logging.info("best: " + str(best[0][0]) + "\n" + stringPath(best[0][1]))
		end = time.time()
		logging.info("SEARCH ITERATIONS {}, TARGET SKIPPED {}, DURATION: {}".format(iter, skippedTargetCount, end - start))
		#if (undiscoveredTileSearchCount > 0):
		#	logging.info("~~evaluated undiscovered tiles during search: " + str(undiscoveredTileSearchCount))
		return best



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
		generalPlayer = self._map.players[self._map.player_index]
		
		realDanger = False
		dangerousPath = None
		dangerValue = -1
		self.allIn = False
		for player in self._map.players:
			if player == generalPlayer or player == None or player.dead:
				continue
			#give up if we're massively losing
			if self._map.remainingPlayers == 2:
				if self._map.turn > 150 and player.tileCount + 25 * player.cityCount > generalPlayer.tileCount * 1.55 + 5 + 25 * generalPlayer.cityCount and player.standingArmy > generalPlayer.standingArmy * 1.65 + 5:
					self.allIn = True
					self.all_in_counter = 100
				elif self._map.turn > 150 and player.tileCount + 25 * player.cityCount > generalPlayer.tileCount * 1.15 + 5 + 25 * generalPlayer.cityCount and player.standingArmy > generalPlayer.standingArmy * 1.25 + 5:
					self.all_in_counter += 1
					if (self.all_in_counter > max(40, player.tileCount ** 0.9 / 2)):
						self.allIn = True
				else:
					self.all_in_counter = 0
				if player.tileCount + 30 * player.cityCount > generalPlayer.tileCount * 1.4 + 5 + 30 * generalPlayer.cityCount and player.score > generalPlayer.score * 1.7 + 5:
					self.giving_up_counter += 1
					logging.info("~ ~ ~ ~ ~ ~ ~ giving_up_counter: {}. Player {} with {} tiles and {} army.".format(self.giving_up_counter, player.index, player.tileCount, player.score))
					if self.giving_up_counter > self._map.players[self.targetPlayer].tileCount:
						logging.info("~ ~ ~ ~ ~ ~ ~ giving up due to player {} with {} tiles and {} army.".format(player.index, player.tileCount, player.score))
						time.sleep(3)
						self._map.result = False
						self._map.complete = True
				else:
					self.giving_up_counter = 0
			if self._map.turn > GENERAL_HALF_TURN:
				# when we have 30% income lead and 5% army disadvantage or better
				if (10.0 * (generalPlayer.tileCount + 25*generalPlayer.cityCount) / max(1, player.tileCount + 25*player.cityCount) > 10 and 10.0 * generalPlayer.standingArmy / max(1, player.standingArmy) > 9):
					if (player.knowsKingLocation):
						#potentialArmy = player.standingArmy / 2.1
						potentialArmy = player.standingArmy / 5
					else:
						#potentialArmy = player.standingArmy / 4
						potentialArmy = player.standingArmy / 20
					if (maxPlayerPotentialArmy < potentialArmy):
						maxPlayerPotentialArmy = potentialArmy
			
		## TODO min army hack?
		self._minAllowableArmy = 1
		return 1
		##

		minAllowableArmy = maxPlayerPotentialArmy

		self._minAllowableArmy = minAllowableArmy
		return minAllowableArmy
		
	def is_move_safe_valid(self, move):
		if (move == None):
			return False
		if (move.source == self.general):
			return self.general_move_safe(move.dest)
		if (move.source.player != move.dest.player and move.source.army - 2 < move.dest.army):
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
		player = self._map.players[self._map.player_index]
		cityRatio = self.get_city_ratio(self._map.player_index)
		logging.info("CityRatio: {}".format(cityRatio))
		genArmy = self.general.army
		if (self.general.army // 2 > self.general_min_army_allowable()):
			genArmy = self.general.army // 2
		standingArmyWeighted = (self._map.players[self._map.player_index].standingArmy - genArmy) * 0.85
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
			#	leafValue = leafValue + player.standingArmy * 5 / max(2, dist(leaf.dest, general))			
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


	def worth_attacking_target(self):
		timingFactor = 1.0
		if self._map.turn < 50:
			return False
		
		knowsWhereEnemyGeneralIs = self.targetPlayer != -1 and self._map.generals[self.targetPlayer] != None

		player = self._map.players[self._map.player_index]
		#factor in some time for exploring after the attack, + 1 * 1.1
		if self.target_player_gather_path == None or self.target_player_gather_path[0] == None:
			logging.info("ELIM due to no path")
			return False
		value = get_player_army_amount_on_path(self.target_player_gather_path[1], self._map.player_index, 0, self.target_player_gather_path[0].turn)
		subsegment = self.get_value_per_turn_subsegment(reverse_path_tuple(self.target_player_gather_path))
		subsegmentTargets = get_tile_set_from_path_tuple(subsegment)

		lengthRatio = len(self.target_player_gather_targets) / max(1, len(subsegmentTargets))

		sqrtVal = 0
		if (value > 0):
			sqrtVal = value ** 0.5
			logging.info("value ** 0.5 -> sqrtVal {}".format(sqrtVal))
		if player.tileCount < 60:
			sqrtVal = value / 2.3
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
		
		playerEffectiveStandingArmy = player.standingArmy - 9 * (player.cityCount - 1)**1.1
		if self.target_player_gather_path[0].turn < 2:
			logging.info("ELIM due to path length {}".format(self.target_player_gather_path[0].turn))
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
					if (not destAdj.isvisible):
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
				leafValue = leafValue / 20
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


	def get_optimal_expansion(self, turns):
		
		return None
		


	def get_path_to_target_player(self):
		if (self.targetPlayer != None and self.generalApproximations[self.targetPlayer][3] != None):
			target = self.generalApproximations[self.targetPlayer][3]
			return self.get_path_to_target(target)
		else:
			return (PathNode(self.general, None, self.general.army, 0, 0, None), PathNode(self.general, None, self.general.army, 0, 0, None))
		
	def info(self, text):
		self.viewInfo.infoText = text
		logging.info(text)

	def get_path_to_target(self, target, maxTime = 0.1, maxDepth = 85, skipNeutralCities = True):
		path = breadth_first_find(self._map, [self.general], lambda tile, dist, army: tile == target, maxTime, maxDepth, skipNeutralCities)
		startNode = path[1]
		while startNode != None:
			self.viewInfo.addSearched(startNode.tile)
			startNode = startNode.parent
		return path

	
	def distance_from_general(self, sourceTile):
		if sourceTile == self.general:
			return 0
		if self._gen_distances == None:
			self._gen_distances = [[INF for x in range(self._map.rows)] for y in range(self._map.cols)]

			def bfs_dist_mapper(tile, army, dist):
				if dist < self._gen_distances[tile.x][tile.y]:
					self._gen_distances[tile.x][tile.y] = dist
				return False
			
			#breadth_first_find(self._map, [self.general], bfs_dist_mapper, 0.04, 200, noNeutralCities=False)
			breadth_first_find_queue(self._map, [self.general], bfs_dist_mapper, 0.04, 200, noNeutralCities=False)
		val = self._gen_distances[sourceTile.x][sourceTile.y]
		#if (val == INF):
		#	logging.info("----------INF {},{}".format(sourceTile.x, sourceTile.y))
		#if (val <= 0):
		#	logging.info("----------<=0 {},{}".format(sourceTile.x, sourceTile.y))
		return val
		
		

	def scan_map(self):
		self.general_safe_func_set[self.general] = self.general_move_safe
		self.numPlayers = self._map.remainingPlayers
		self.leafMoves = []
		self.largeTilesNearEnemyKings = {}
		self.allUndiscovered = []
		self.largePlayerTiles = []
		player = self._map.players[self._map.player_index]
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
						if tile.army > enemyGen.army and dist(tile, enemyGen) < 15:
							self.largeTilesNearEnemyKings[enemyGen].append(tile)
						
			
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
				for x in range(self._map.cols):
					for y in range(self._map.rows):
						tile = _map.grid[y][x]
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
		for player in self._map.players:
			seenPlayer = self.generalApproximations[player.index][2] > 0 or self._map.generals[player.index] != None
			if not player.dead and not player.index == self._map.player_index and seenPlayer:
				curScore = 300
				if player.index == self.targetPlayer:
					curScore = 400
				if self._map.generals[player.index] != None:
					curScore += 150
				curScore = curScore + player.tileCount + player.cityCount * 20 - player.score / 2
				# stars = max(20, player.stars - minStars + 20)
				# curScore = curScore * stars
				if generalApproximations[player.index][3] != None:
					genDist = self.distance_from_general(generalApproximations[player.index][3])
				else:
					logging.info("           wot {} didn't have a gen approx tile???".format(self._map.usernames[targetPlayer]))
					genDist = self.euclidDist(generalApproximations[player.index][0], generalApproximations[player.index][1], self.general.x, self.general.y)
				curScore = curScore + curScore / max(1, genDist) / 2
				if (player.knowsKingLocation):
					curScore += 100
					curScore *= 2
				if player.tileCount < 4:
					curScore = -100
				if (curScore > playerScore):
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
	
	move = _eklipzBot.find_move()
	if (move != None):
		if not place_move(move.source, move.dest, move.move_half):
			logging.info("!!!!!!!!! {},{} -> {},{} was an illegal / bad move!!!!".format(move.source.x, move.source.y, move.dest.x, move.dest.y))
			_eklipzBot.curPath = None
			_eklipzBot.curPathPrio = -1
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


"""
