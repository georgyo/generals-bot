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
import math

math = math.inf

# attempts to classify tiles into territories.
class TerritoryClassifier():
	def __init__(self, map):
		self.territories = [None for player in map.players]
		self.map = map
		self.lastCalculatedTurn = -1
		self.territoryMap = new_value_matrix(self.map, -1)
		self.needToUpdateAroundTiles = set()
		for tile in self.map.reachableTiles:
			self.needToUpdateAroundTiles.add(tile)

	def should_recalculate(self, turn):
		if len(self.needToUpdateAroundTiles) > 0:
			return True
		return False

	# When a tile is initially discovered, it should be used to weight territories as the player
    # it was discovered as (to prevent the creep of neutral weighted discovery).
	# Note that this gets immediately overwritten by the actual territory value for this tile, 
	# it is just used to weight the tiles around it during that cycle.
	def revealed_tile(self, tile):
		self.territoryMap[tile.x][tile.y] = tile.player
		if tile.player != -1:
			for moveable in tile.moveable:
				if not moveable.discovered:
					self.territoryMap[moveable.x][moveable.y] = tile.player

	def scan(self):
		logging.info("Scanning map for territories, aww geez")
		counts = new_map_matrix(self.map, lambda x,y: [0 for n in range(len(self.map.players)+1)])
		startTime = time.time()
		undiscoveredCounterDepth = 5
		# count the number of tiles for each player within range 3 to determine whose territory this is
		neutralNewIndex = len(self.map.players)
		
		# do a BFS foreach within a BFS foreach. Normal everyday stuff nbd
		def foreach_near_updated_tiles(evaluatingTile):
			def countFunc(tile):
				if tile.mountain:
					return
				
				currentTerritory = self.territoryMap[tile.x][tile.y]
				if not evaluatingTile.discovered:
					# weight based on territory already owned, making it harder to flip a territory (and hopefully better encapsulate who owns what)
					if currentTerritory != -1:
						# do NOT allow our player to own undiscovered territory. If owned by us, is neutral.
						# This prevents the undiscovered-tile-friendly-territory cascade from happening.
						if tile.discovered and not evaluatingTile.discovered and currentTerritory != self.map.player_index:
							counts[evaluatingTile.x][evaluatingTile.y][currentTerritory] += 0.3
						elif currentTerritory == self.map.player_index:
							counts[evaluatingTile.x][evaluatingTile.y][neutralNewIndex] += 0.06
					else:
						# only discovered neutral tiles count, and only if we're trying to classify a neutral tile.
						counts[evaluatingTile.x][evaluatingTile.y][neutralNewIndex] += 0.02
				else:
					# undiscovereds count for the evaluating tile player
					if not tile.discovered:
						counts[evaluatingTile.x][evaluatingTile.y][evaluatingTile.player] += 0.2
					else:
						pIndex = tile.player
						if pIndex != -1 and pIndex != self.map.player_index:
							counts[evaluatingTile.x][evaluatingTile.y][pIndex] += 1
						elif pIndex != -1: 
							# weight our tiles less because we see more of them.
							counts[evaluatingTile.x][evaluatingTile.y][pIndex] += 0.8
				
			skip = lambda tile: tile.player == -1 and tile.discovered
			breadth_first_foreach(self.map, [evaluatingTile], undiscoveredCounterDepth, countFunc, skipFunc = skip, noLog = True)
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
		startTiles = list(self.needToUpdateAroundTiles)
		logging.info("  Scanning territory around {}".format(" - ".join([tile.toString() for tile in startTiles])))
		breadth_first_foreach(self.map, startTiles, undiscoveredCounterDepth, foreach_near_updated_tiles, None, lambda tile: tile.mountain, None, self.map.player_index)
		duration = time.time() - startTime
			
		logging.info("Completed scanning territories in {:.3f}".format(duration))
		self.needToUpdateAroundTiles = set()
