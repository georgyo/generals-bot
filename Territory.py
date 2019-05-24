'''
	@ Travis Drake (EklipZ) eklipz.io - tdrake0x45 at gmail)
	April 2017
	Generals.io Automated Client - https://github.com/harrischristiansen/generals-bot
	EklipZ bot - Tries to play generals lol
'''

import logging
import time
import json
from SearchUtils import *
from test.test_float import INF

# attempts to classify tiles into territories.
class TerritoryClassifier():
	def __init__(self, map):
		self.territories = [None for player in map.players]
		self.map = map
		self.lastCalculatedTurn = -1
		self.territoryMap = new_map_matrix(self.map, lambda x,y: -1)
		self.needToUpdateAroundTiles = set()
		for tile in self.map.reachableTiles:
			self.needToUpdateAroundTiles.add(tile)

	def should_recalculate(self, turn):
		if len(self.needToUpdateAroundTiles) > 0:
			return True
		return False

	def scan(self):
		logging.info("Scanning map for territories, aww geez")
		counts = new_map_matrix(self.map, lambda x,y: [0 for n in range(len(self.map.players)+1)])
		startTime = time.time()
		undiscoveredCounterDepth = 4
		# count the number of tiles for each player within range 3 to determine whose territory this is
		neutralNewIndex = len(self.map.players)
		
		# do a BFS foreach within a BFS foreach. Normal everyday stuff nbd
		def foreach_near_updated_tiles(evaluatingTile):
			def countFunc(tile):
				if tile.mountain:
					return
				pIndex = tile.player
				if pIndex != -1:
					counts[evaluatingTile.x][evaluatingTile.y][pIndex] += 1
				elif tile.discovered:
					# only discovered neutral tiles count.
					counts[evaluatingTile.x][evaluatingTile.y][neutralNewIndex] += 1
			breadth_first_foreach(self.map, [evaluatingTile], undiscoveredCounterDepth, countFunc, noLog = True)
			maxPlayer = -1
			maxValue = 0
			for pIndex, value in enumerate(counts[evaluatingTile.x][evaluatingTile.y]):
				if value > maxValue:
					maxPlayer = pIndex
					maxValue = value
			userName = "Neutral"
			# convert back to -1 index for neutral
			if maxPlayer == neutralNewIndex:
				maxPlayer = -1
			else:
				userName = self.map.usernames[maxPlayer]

			if evaluatingTile.player != maxPlayer and evaluatingTile.player != -1:
				logging.info("Tile {} is in player {} {} territory".format(evaluatingTile.toString(), maxPlayer, userName))
			self.territoryMap[evaluatingTile.x][evaluatingTile.y] = maxPlayer
		breadth_first_foreach(self.map, list(self.needToUpdateAroundTiles), undiscoveredCounterDepth, foreach_near_updated_tiles, None, lambda tile: tile.mountain, None, self.map.player_index)
		duration = time.time() - startTime
			
		logging.info("Completed scanning territories in {:.3f}".format(duration))
		self.needToUpdateAroundTiles = set()