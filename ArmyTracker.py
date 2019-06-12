'''
	@ Travis Drake (EklipZ) eklipz.io - tdrake0x45 at gmail)
	April 2017
	Generals.io Automated Client - https://github.com/harrischristiansen/generals-bot
	EklipZ bot - Tries to play generals lol
'''

import logging
import time
import json
from collections import deque 
from queue import PriorityQueue 
from Path import Path


class Army(object):
	def __init__(self, tile):
		self.tile = tile
		self.path = Path()
		self.player = tile.player
		self.update_tile(tile)
		self.expectedPath = None

	def update_tile(self, tile):
		self.path.add_next(tile)
		self.tile = tile
		self.value = tile.army - 1


class ArmyTracker(object):
	def __init__(self, map):
		self.map = map
		self.armies = {}
		self.scrapped_armies = []

	def scan(self):
		logging.info("ARMY TRACKER SCANNING BEEEEEEEEEEEEEEEEEEEEEEEEEEP BOOOOOOOOOOOOP")
		start = time.time()
		self.scrapped_armies = []
		self.track_army_movement()
		self.find_new_armies()
		logging.info("ARMY TRACKER TOOK {:.2f}\n".format(time.time() - start))

	def track_army_movement(self):
		#for army in list(self.armies.values()):
		#	self.determine_army_movement(army, adjArmies)
		trackingArmies = self.armies.copy()

		for army in list(trackingArmies.values()):
			foundLocation = False
			#if not army.tile.visible:
			#	# handle enemy army fogging things up as it moves
			#	for adjacent in army.tile.moveable:
			#		logging.info("armyDeltas: tile {} {} - adj {} {}".format(army.tile.toString(), abs(army.tile.delta.armyDelta), adjacent.toString(), abs(adjacent.delta.armyDelta)))
			#		if abs(abs(adjacent.delta.armyDelta) - abs(army.tile.delta.armyDelta)) == 0:
			#			foundLocation = True
			#			logging.info("Army probably moved from {} to {}".format(army.tile.toString(), adjacent.toString()))
			#			del self.armies[army.tile]
			#			del trackingArmies[army.tile]
			#			army.update_tile(adjacent)
			#			if army.value > 0 and army.player == army.tile.player:
			#				self.armies[army.tile] = army
			#			else:
			#				logging.info("Army {} scrapped for being low value or run into larger tile".format(army.tile.toString()))
			#				self.scrapped_armies.append(army)
			#			break

			if army.value + 1 != army.tile.army or army.tile.player != army.player:
				# army probably moved. Check adjacents for the army
				for adjacent in army.tile.moveable:
					adjDelta = abs(adjacent.delta.armyDelta)
					armyTileDelta = abs(army.tile.delta.armyDelta)
					logging.info("armyDeltas: tile {} {} - adj {} {}".format(army.tile.toString(), armyTileDelta, adjacent.toString(), adjDelta))
					if abs(adjDelta - armyTileDelta) == 0:
						foundLocation = True
						logging.info("Army probably moved from {} to {}".format(army.tile.toString(), adjacent.toString()))
						del self.armies[army.tile]
						del trackingArmies[army.tile]
						army.update_tile(adjacent)
						if army.value > 0 and army.player == army.tile.player:
							self.armies[army.tile] = army
						else:
							logging.info("Army {} scrapped for being low value or run into larger tile".format(army.tile.toString()))
							self.scrapped_armies.append(army)
						break
					elif abs(adjDelta - abs(army.value - 1)) == 0:
						# handle fog moves?
						foundLocation = True
						logging.info("Army (FOG?) probably moved from {} to {}".format(army.tile.toString(), adjacent.toString()))
						del self.armies[army.tile]
						del trackingArmies[army.tile]
						army.update_tile(adjacent)
						if army.value > 0 and army.player == army.tile.player:
							self.armies[army.tile] = army
						else:
							logging.info("Army (FOG?) {} scrapped for being low value or run into larger tile".format(army.tile.toString()))
							self.scrapped_armies.append(army)
						break
		# trackingArmies now contains only the armies that we didn't find an exact match for.
		
		#	adjArmies = self.get_nearby_armies(army, trackingArmies)

			#if not foundLocation:
			#	# army was killed?
			#	logging.info("Army {} probably was killed? Scrapping".format(army.tile.toString()))
			#	self.scrapped_armies.append(army)
			#	del self.armies[army.tile]

	def get_nearby_armies(self, army, armyMap = None):
		if armyMap == None:
			armyMap = self.armies
		# super fast depth 2 bfs effectively
		nearbyArmies = []
		for tile in army.tile.moveable:
			if tile in armyMap:
				nearbyArmies.append(armyMap[tile])
			for nextTile in tile.moveable:
				if nextTile != army.tile and nextTile in armyMap:
					nearbyArmies.append(armyMap[nextTile])
		for nearbyArmy in nearbyArmies:
			logging.info("Army {} had nearbyArmy {}".format(army.tile.toString(), nearbyArmy.tile.toString()))
		return nearbyArmies

	def find_new_armies(self):
		for tile in self.map.reachableTiles:
			if tile not in self.armies and tile.army > 10 and tile.player != -1:
				# then tile is an army.
				logging.info("Army discovered: {}".format(tile.toString()))
				army = Army(tile)
				self.armies[tile] = army
