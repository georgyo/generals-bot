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
from SearchUtils import *
from DataModels import *
from Path import PathFromPathNode
from enum import Enum

class ThreatType(Enum):
    Kill = 1
    Vision = 2

class ThreatObj(object):
	def __init__(self, moveCount, threatValue, path, type, saveTile = None):
		self.turns = moveCount
		self.threatValue = threatValue
		self.path = path
		self.threatPlayer = path.start.tile.player
		self.threatType = type
		self.saveTile = saveTile






class DangerAnalyzer(object):
	def __init__(self, map):
		self.map = map
		self.fastestVisionThreat = None
		self.fastestThreat = None
		self.highestThreat = None
		self.playerTiles = None
		
		self.anyThreat = False

		self.ignoreThreats = False

		self.largeVisibleEnemyTiles = []
		
	def analyze(self, general, depth):
		self.scan(general)
		minDanger = 1000
		
		generalScore = self.map.scores[self.map.player_index]

		self.fastestVisionThreat = self.getVisionThreat(general, 10)
		self.fastestThreat = self.getFastestThreat(general, depth)
		self.highestThreat = self.getHighestThreat(general, depth)

		self.anyThreat = self.fastestThreat != None or self.fastestVisionThreat != None or self.highestThreat != None
		


	def getVisionThreat(self, general, depth):
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
			if not player.dead and (player.index != general.player) and len(self.playerTiles[player.index]) > 0 and self.map.players[player.index].tileCount > 10:
				path = dest_breadth_first_target(self.map, general.adjacents, 0, 0.01, depth, None, player.index, False, 2)
				if path != None and (curThreat == None or path.length < curThreat.length or (path.length == curThreat.length and path.value > curThreat.value)):
					#self.viewInfo.addSearched(path[1].tile)
					logging.info("dest BFS found VISION against our general:\n{}".format(visionPath.toString()))
					curThreat = path
		if (curThreat == None):
			return None
		return ThreatObj(curThreat.length, curThreat.value, curThreat, ThreatType.Vision)
	
	def getFastestThreat(self, general, depth):
		startTime = time.time()
		logging.info("------\nfastest threat analyzer: depth {}".format(depth))
		curThreat = None
		saveTile = None
		for player in self.map.players:
			if not player.dead and (player.index != general.player) and player.index not in self.map.teammates and len(self.playerTiles[player.index]) > 0 and self.map.players[player.index].tileCount > 10:
				# -1.5 because of the stupid increment we're using.
				path = dest_breadth_first_target(self.map, [general], 0, 0.05, depth, None, player.index, False, 6)
				if path != None and (curThreat == None or path.length < curThreat.length or (path.length == curThreat.length and path.value > curThreat.value)):
					# If there is NOT another path to our general that doesn't hit the same tile next to our general, then we can use one extra turn on defense
					# gathering to that 'saveTile'.
					lastTile = path.tail.prev.tile
					altPath = dest_breadth_first_target(self.map, [general], 0, 0.05, path.length + 5, None, player.index, False, 6, skipTiles = [lastTile])
					if altPath == None or altPath.length > path.length:
						saveTile = lastTile
						logging.info("saveTile blocks path to our king: {},{}".format(saveTile.x, saveTile.y))
					logging.info("dest BFS found KILL against our general:\n{}".format(path.toString()))
					curThreat = path
		logging.info("fastest threat analyzer took {:.3f}".format(time.time() - startTime))
		if (curThreat == None):
			return None
		return ThreatObj(curThreat.length - 1, curThreat.value, curThreat, ThreatType.Kill, saveTile)
	
	
	def getHighestThreat(self, general, depth):
		return self.fastestThreat
	

	def scan(self, general):
		self.largeVisibleEnemyTiles = []
		self.playerTiles = [[] for player in self.map.players]
		for x in range(self.map.cols):
			for y in range(self.map.rows):
				tile = self.map.grid[y][x]
				if (tile.player != -1):
					self.playerTiles[tile.player].append(tile)
					if(tile.player not in self.map.teammates and tile.player != general.player and tile.army > max(2, general.army / 4) and tile.visible and not tile.isGeneral):
						self.largeVisibleEnemyTiles.append(tile)