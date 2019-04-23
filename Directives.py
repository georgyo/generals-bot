'''
	@ Travis Drake (EklipZ) eklipz.io - tdrake0x45 at gmail)
	April 2017
	Generals.io Automated Client - https://github.com/harrischristiansen/generals-bot
	EklipZ bot - Tries to play generals lol
'''

import logging
import random
from copy import deepcopy
import time
import json
from collections import deque 
from queue import PriorityQueue
from pprint import pprint,pformat
from SearchUtils import a_star_kill, dest_breadth_first_target
from DataModels import stringPath, PathFromPathNode
from enum import Enum


class Directive(object):
	def __init__(self, moveCount, threatValue, path, type):
		self.turns = moveCount
		self.threatValue = threatValue
		self.path = path
		self.threatPlayer = path.pathMove.move.source.player
		self.threatType = type


class DangerAnalyzer(object):
	def __init__(self, map):
		self.map = map
		self.fastestVisionThreat = None
		self.fastestThreat = None
		self.highestThreat = None
		
		self.anyThreat = False

		self.ignoreThreats = False

		self.largeVisibleEnemyTiles = []
		
	def analyze(self, general):
		
		self.scan(general)
		minDanger = 1000
		
		generalScore = self.map.scores[self.map.player_index]

		self.fastestVisionThreat = self.getVisionThreat(general)
		self.fastestThreat = self.getFastestThreat(general)
		self.highestThreat = self.getHighestThreat(general)

		self.anyThreat = self.fastestThreat != None or self.fastestVisionThreat != None or self.highestThreat != None
		
		
		#for player in self.largeVisibleEnemyTiles:
		#	if (len(player) > 0 and len(player) < 4):
		#		killPath = None
		#		killPathEnd = None
		#		for tile in player:	
		#			(potKillPathEnd, potKillPath) = a_star_kill(self.map, [tile], general, 0.030, 25)
		#			if (potKillPath != None and (killPath == None or potKillPathEnd.turn < killPathEnd.turn)):
		#				killPath = potKillPath		
		#				killPathEnd = potKillPathEnd
		#		if (killPath != None and killPathEnd.turn < minRealDanger):
		#			#self.viewInfo.addSearched(path[1].tile)
		#			logging.info("A*  Kill path against our general:\n{}".format(stringPath(killPath)))
		#			dangerousPath = killPath
		#			dangerValue = killPathEnd.value
		#			minRealDanger = killPathEnd.turn
		#			realDanger = True
		#		#else: #attempt BFS
		#		#	closeTiles = []
		#		#	for tile in player:
		#		#		if dist(tile, general) < 10:
		#		#			closeTiles.append(tile)
		#		#	if len(closeTiles) > 0:
		#		#		(killPathBreadthEnd, killPathBreadth) = self.breadth_first_kill(closeTiles, general, 0.04, 10)
		#		#		if (killPathBreadth != None and killPathBreadthEnd.turn < minRealDanger):
		#		#			logging.info("BFS Kill path against our general:\n{}".format(stringPath(killPathBreadth)))
		#		#			#self.viewInfo.addSearched(path[1].tile)
		#		#			dangerousPath = killPathBreadth
		#		#			dangerValue = killPathBreadthEnd.value
		#		#			minRealDanger = killPathBreadthEnd.turn
		#		#			realDanger = True
		#	if (len(player) >= 4):
		#		(potKillPathEnd, potKillPath) = a_star_kill(self.map, player, general, 0.035, 25)
		#		if (potKillPath != None):
		#			killPath = potKillPath		
		#			killPathEnd = potKillPathEnd
		#			logging.info("A*  Kill path against our general:\n{}".format(stringPath(killPath)))
		#			dangerousPath = killPath
		#			dangerValue = killPathEnd.value
		#			minRealDanger = killPathEnd.turn
		#minDanger = min(minDanger, minRealDanger)

		#if (minDanger == 1000):
		#	minDanger = -1
		#if (minDanger != -1):
		#	logging.info("    Evaluated if general is in danger from {} players: {} turns to death by value {}".format(len(playerTiles), minDanger, dangerValue))
		#	self.danger = (minDanger, dangerValue, dangerousPath, realDanger)
			

	def getVisionThreat(self, general):
		curThreat = None
		#hack vision threat broken todo fix
		# DO NOT COMMENT UNTIL TILE RESTRICTIONS IS IMPLEMENTED :V
		return None
		for tile in general.adjacents:
			if tile.player != -1 and tile.player != general.player:
				logging.info("not searching general vision due to tile {},{} of player {}".format(tile.x, tile.y, tile.player))
				# there is already general vision.
				return None
		for player in self.map.players:
			if not player.dead and (player.index != general.player):
				(visionPathEnd, visionPath) = dest_breadth_first_target(self.map, general.adjacents, 1, 0.01, 7, None, player.index, False, 2)
				path = PathFromPathNode(visionPathEnd, visionPath)
				if path != None and (curThreat == None or path.movesLeft < curThreat.movesLeft or (path.movesLeft == curThreat.movesLeft and path.value > curThreat.value)):
					#self.viewInfo.addSearched(path[1].tile)
					logging.info("dest BFS found VISION against our general:\n{}".format(stringPath(visionPath)))
					curThreat = path
		if (curThreat == None):
			return None
		return ThreatObj(curThreat.movesLeft, curThreat.value, curThreat, ThreatType.Vision)
	
	def getFastestThreat(self, general):
		curThreat = None
		for player in self.map.players:
			if not player.dead and (player.index != general.player):
				(pathEnd, pathNode) = dest_breadth_first_target(self.map, [general], 0.5, 0.05, 22, None, player.index, False, 6)
				path = PathFromPathNode(pathEnd, pathNode)
				if path != None and (curThreat == None or path.movesLeft < curThreat.movesLeft or (path.movesLeft == curThreat.movesLeft and path.value > curThreat.value)):
					#self.viewInfo.addSearched(path[1].tile)
					logging.info("dest BFS found KILL against our general:\n{}".format(stringPath(pathNode)))
					curThreat = path
		if (curThreat == None):
			return None
		return ThreatObj(curThreat.movesLeft, curThreat.value, curThreat, ThreatType.Kill)
	
	
	def getHighestThreat(self, general):
		return self.fastestThreat
	

	def scan(self, general):
		self.largeVisibleEnemyTiles = []
		for x in range(self.map.cols):
			for y in range(self.map.rows):
				tile = self.map.grid[y][x]
				
				if(tile.player != -1 and tile.player != general.player and tile.army > max(2, general.army / 4) and tile.isvisible() and not tile.isGeneral):
					self.largeVisibleEnemyTiles.append(tile)