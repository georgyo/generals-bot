'''
	@ Travis Drake (EklipZ) eklipz.io - tdrake0x45 at gmail)
	July 2019
	Generals.io Automated Client - https://github.com/harrischristiansen/generals-bot
	EklipZ bot - Tries to play generals lol
'''

import logging
import time
import json
from ArmyAnalyzer import *
from SearchUtils import *
from collections import deque 
from queue import PriorityQueue 
from Path import Path


class BoardAnalyzer:
	def __init__(self, map, general):
		startTime = time.time()
		self.map = map
		self.general = general

		self.innerChokes = None
		self.outerChokes = None

		self.intergeneral_analysis = None

		self.rescan_chokes()

		logging.info("BoardAnalyzer completed in {:.3f}".format(time.time() - startTime))

	def rescan_chokes(self):
		oldInner = self.innerChokes
		oldOuter = self.outerChokes
		self.innerChokes = [[False for x in range(self.map.rows)] for y in range(self.map.cols)]
		self.outerChokes = [[False for x in range(self.map.rows)] for y in range(self.map.cols)]
		self.genDistMap = build_distance_map(self.map, [self.general])
		for tile in self.map.reachableTiles:
			logging.info("Rescanning chokes for {}".format(tile.toString()))
			tileDist = self.genDistMap[tile.x][tile.y]
			moveableOuterCount = count(tile.moveable, lambda adj: tileDist == self.genDistMap[adj.x][adj.y] + 1)
			if moveableOuterCount == 1:
				self.innerChokes[tile.x][tile.y] = True
			moveableInnerCount = count(tile.moveable, lambda adj: tileDist == self.genDistMap[adj.x][adj.y] - 1)
			if moveableInnerCount == 1:
				self.outerChokes[tile.x][tile.y] = True
			if self.map.turn > 4:
				if oldInner != None and oldInner[tile.x][tile.y] != self.innerChokes[tile.x][tile.y]:
					logging.info("  inner choke change: tile {}, old {}, new {}".format(tile.toString(), oldInner[tile.x][tile.y], self.innerChokes[tile.x][tile.y]))
				if oldOuter != None and oldOuter[tile.x][tile.y] != self.outerChokes[tile.x][tile.y]:
					logging.info("  outer choke change: tile {}, old {}, new {}".format(tile.toString(), oldOuter[tile.x][tile.y], self.outerChokes[tile.x][tile.y]))

	def rebuild_intergeneral_analysis(self, opponentGeneral):
		self.intergeneral_analysis = ArmyAnalyzer(self.map, self.general, opponentGeneral)
