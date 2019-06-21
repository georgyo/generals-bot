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
from collections import deque 
from queue import PriorityQueue 
from Path import Path


class Army(object):
	start = 'A'
	end = 'Z'
	curLetter = start

	def get_letter():
		ch = Army.curLetter
		if (ord(ch) + 1 > ord(Army.end)):
			Army.curLetter = Army.start
		else:
			Army.curLetter = chr(ord(ch) + 1)
		return ch

	def __init__(self, tile):
		self.tile = tile
		self.path = Path()
		self.player = tile.player
		self.visible = tile.visible
		self.value = 0
		self.update_tile(tile)
		self.expectedPath = None
		self.distMap = None
		self.entangledArmies = []
		self.name = Army.get_letter()

	def update_tile(self, tile):
		self.path.add_next(tile)
		self.tile = tile
		self.update()

	def update(self):
		self.value = self.tile.army - 1
		self.visible = self.tile.visible

	def get_split_for_fog(self, fogTiles):
		split = []
		for tile in fogTiles:
			splitArmy = self.clone()
			split.append(splitArmy)
		# entangle the armies
		for splitBoi in split:
			splitBoi.entangledArmies = list(where(split, lambda army: army != splitBoi))
		return split


	def clone(self):
		newDude = Army(self.tile)
		if self.path != None:
			newDude.path = self.path.clone()
		newDude.player = self.player
		newDude.visible = self.visible
		newDude.value = self.value
		if self.expectedPath != None:
			newDude.expectedPath = self.expectedPath.clone()
		newDude.distMap = self.distMap
		newDude.entangledArmies = list(self.entangledArmies)
		newDude.name = self.name
		return newDude

class ArmyTracker(object):
	def __init__(self, map):
		self.map = map
		self.armies = {}
		self.scrapped_armies = []
		self.isArmyBonus = map.turn % 50 == 0
		self.isCityBonus = map.turn % 2 == 0
		self.distMap = None
		self.lastMove = None
		self.track_threshold = 10

	# distMap used to determine how to move armies under fog
	def scan(self, distMap, lastMove):
		self.lastMove = lastMove
		logging.info("ARMY TRACKER SCANNING BEEEEEEEEEEEEEEEEEEEEEEEEEEP BOOOOOOOOOOOOP")
		self.distMap = distMap
		self.isArmyBonus = self.map.turn % 50 == 0
		self.isCityBonus = self.map.turn % 2 == 0
		start = time.time()
		self.scrapped_armies = []
		self.track_army_movement()
		self.find_new_armies()
		logging.info("ARMY TRACKER TOOK {:.3f}\n".format(time.time() - start))

	def track_army_movement(self):
		#for army in list(self.armies.values()):
		#	self.determine_army_movement(army, adjArmies)
		trackingArmies = self.armies.copy()

		for army in list(trackingArmies.values()):
			expectedDelta = self.get_expected_delta(army.tile)
			logging.info("{} army.value {} expectedDelta {}".format(army.tile.toString(), army.value, expectedDelta))
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
			#				self.scrap_army(army)
			#			break
			#elif
			if army.player == army.tile.player and army.value < army.tile.army - 1:
				logging.info("Army {} tile was just gathered to, nbd, update it".format(army.tile.toString()))
				if army.tile in trackingArmies:
					del trackingArmies[army.tile]
				army.update()
				continue

			lostVision = (army.visible and not army.tile.visible)
			if lostVision or (army.value + 1 + expectedDelta != army.tile.army or army.tile.player != army.player):
				# army probably moved. Check adjacents for the army
				armyTileDelta = 0 - army.tile.delta.armyDelta
				for adjacent in army.tile.moveable:
					if adjacent.mountain:
						continue
					expectedAdjDelta = self.get_expected_delta(adjacent)
					logging.info("  adjacent delta raw {} expectedAdjDelta {}".format(adjacent.delta.armyDelta, expectedAdjDelta))
					adjDelta = abs(adjacent.delta.armyDelta - expectedAdjDelta)
					logging.info("  armyDeltas: army {} {} - adj {} {}  -  lostVision {}".format(army.tile.toString(), armyTileDelta, adjacent.toString(), adjDelta, lostVision))
					if armyTileDelta > 0 and adjDelta - armyTileDelta == expectedDelta:
						foundLocation = True
						logging.info("    Army probably moved from {} to {}".format(army.tile.toString(), adjacent.toString()))
						if army.tile in self.armies:
							del self.armies[army.tile]
						if army.tile in trackingArmies:
							del trackingArmies[army.tile]
						army.update_tile(adjacent)
						if army.value > 0 and army.player == army.tile.player:
							self.armies[army.tile] = army
						else:
							logging.info("    Army {} scrapped for being low value or run into larger tile".format(army.tile.toString()))
							self.scrap_army(army)
						break
					elif adjDelta != 0 and adjDelta - (army.value) == 0:
						# handle fog moves?
						foundLocation = True
						logging.info("    Army (SOURCE FOGGED?) probably moved from {} to {}. adj (dest) visible? {}".format(army.tile.toString(), adjacent.toString(), adjacent.visible))
						del self.armies[army.tile]
						del trackingArmies[army.tile]
						oldTile = army.tile
						if oldTile.army > army.value - adjDelta and not oldTile.visible:
							oldTile.army = army.value - adjDelta
						army.update_tile(adjacent)
						if army.value > 0 and army.player == army.tile.player:
							self.armies[army.tile] = army
						else:
							logging.info("    Army (SOURCE FOGGED?) {} scrapped for being low value or run into larger tile".format(army.tile.toString()))
							self.scrap_army(army)
						break
					elif self.isArmyBonus and armyTileDelta > 0 and abs(adjDelta - armyTileDelta) == 2:
						# handle bonus turn capture moves?
						foundLocation = True
						logging.info("    Army (BONUS CAPTURE?) probably moved from {} to {}".format(army.tile.toString(), adjacent.toString()))
						del self.armies[army.tile]
						del trackingArmies[army.tile]
						army.update_tile(adjacent)
						if army.value > 0 and army.player == army.tile.player:
							self.armies[army.tile] = army
						else:
							logging.info("    Army (BONUS CAPTURE?) {} scrapped for being low value or run into larger tile".format(army.tile.toString()))
							self.scrap_army(army)
						break
				if not foundLocation:
					# first check if the map decided where it went
					if army.tile.delta.toTile != None:
						foundLocation = True
						logging.info("  army.tile.delta.toTile != None, using {}".format(army.tile.delta.toTile.toString()))
						del self.armies[army.tile]
						del trackingArmies[army.tile]
						army.update_tile(army.tile.delta.toTile)
						if army.value > 0 and army.player == army.tile.player:
							self.armies[army.tile] = army
						else:
							logging.info("    Army (delta.toTile?) {} scrapped for being low value or run into larger tile".format(army.tile.toString()))
							self.scrap_army(army)
				if not foundLocation:
					# now try fog movements?
					fogBois = []
					fogCount = 0
					for adjacent in army.tile.moveable:
						if adjacent.mountain:
							continue
						# fogged armies cant move to other fogged tiles when army is uncovered unless that player already owns the other fogged tile
						legalFogMove = (army.visible or adjacent.player == army.player)
						if not adjacent.visible and self.army_could_capture(army, adjacent) and legalFogMove:
							#if (closestFog == None or self.distMap[adjacent.x][adjacent.y] < self.distMap[closestFog.x][closestFog.y]):
							#	closestFog = adjacent
							fogBois.append(adjacent)
							fogCount += 1
						expectedAdjDelta = self.get_expected_delta(adjacent)
						logging.info("  adjacent delta raw {} expectedAdjDelta {}".format(adjacent.delta.armyDelta, expectedAdjDelta))
						adjDelta = abs(adjacent.delta.armyDelta - expectedAdjDelta)
						logging.info("  armyDeltas: army {} {} - adj {} {} expAdj {}".format(army.tile.toString(), armyTileDelta, adjacent.toString(), adjDelta, expectedAdjDelta))
						# expectedDelta is fine because if we took the expected tile we would get the same delta as army remaining on army tile.
						if (armyTileDelta > 0 or not army.tile.visible) and adjDelta - armyTileDelta == expectedDelta:
							foundLocation = True
							logging.info("    Army (Based on expected delta?) probably moved from {} to {}".format(army.tile.toString(), adjacent.toString()))
							del self.armies[army.tile]
							del trackingArmies[army.tile]
							army.update_tile(adjacent)
							if army.value > 0 and army.player == army.tile.player:
								self.armies[army.tile] = army
							else:
								logging.info("    Army (Based on expected delta?) {} scrapped for being low value or run into larger tile".format(army.tile.toString()))
								self.scrap_army(army)
							break
					if not foundLocation and len(fogBois) > 0 and army.player != self.map.player_index and (army.tile.visible or army.tile.delta.lostSight): # prevent entangling and moving fogged cities and stuff that we stopped incrementing
						fogArmies = []
						if len(fogBois) == 1:
							foundLocation = True
							logging.info("    WHOO! Army {} moved into fog at {}!?".format(army.tile.toString(), fogBois[0].toString()))
							del self.armies[army.tile]
							del trackingArmies[army.tile]
							self.move_fogged_army(army, fogBois[0])
							if fogCount == 1:
								logging.info("closestFog and fogCount was 1, converting fogTile to be owned by player")
								fogBois[0].player = army.player
							#if army.value > 0 and army.player == army.tile.player:
							if army.value > 0:
								self.armies[army.tile] = army
							else:
								logging.info("    Army {} scrapped for being low value or run into larger tile".format(army.tile.toString()))
								self.scrap_army(army)
						else:
							logging.info("    Army {} IS BEING ENTANGLED! WHOO! EXCITING!".format(army.tile.toString()))
							del self.armies[army.tile]
							del trackingArmies[army.tile]
							entangledArmies = army.get_split_for_fog(fogBois)
							for i, fogBoi in enumerate(fogBois):
								logging.info("    Army {} entangled moved to {}".format(army.tile.toString(), fogBoi.toString()))
								self.move_fogged_army(entangledArmies[i], fogBoi)

				army.update()
			else:
				army.update()
				# army hasn't moved
				if army.value < self.track_threshold - 1:
					logging.info("  Army {} Stopped moving. Scrapped for being low value".format(army.tile.toString()))
					del trackingArmies[army.tile]
					self.scrap_army(army)
				else:
					if army.tile in trackingArmies:
						# don't continue to track on this army because it didn't move and wont be valuable for evaluating tiles that aren't basic tracking
						del trackingArmies[army.tile]
					else: 
						logging.info("    WTF? Army {} no longer in trackingArmies, can't remove it?".format(army.tile.toString()))

		# trackingArmies now contains only the armies that we didn't find an exact match for.
		
		#	adjArmies = self.get_nearby_armies(army, trackingArmies)

			#if not foundLocation:
			#	# army was killed?
			#	logging.info("Army {} probably was killed? Scrapping".format(army.tile.toString()))
			#	self.scrap_army(army)
			#	del self.armies[army.tile]

	def scrap_army(self, army):
		if army.tile in self.armies:
			del self.armies[army.tile]
		self.scrapped_armies.append(army)
		for entangledArmy in army.entangledArmies:
			self.scrapped_armies.append(entangledArmy)
		self.resolve_entangled_armies(army)

	def resolve_entangled_armies(self, army):
		if len(army.entangledArmies) > 0:
			logging.info("{} resolving {} entangled armies".format(army.tile.toString(), len(army.entangledArmies)))
			for entangledArmy in army.entangledArmies:
				logging.info("    {} entangled".format(entangledArmy.tile.toString()))
				if entangledArmy.tile in self.armies:
					del self.armies[entangledArmy.tile]
				entangledArmy.entangledArmies = []
			army.entangledArmies = []

	def army_could_capture(self, army, fogTargetTile):
		if army.player != fogTargetTile.player:
			return army.value > fogTargetTile.army
		return True

	def move_fogged_army(self, army, fogTargetTile):
		if army.tile in self.armies:
			del self.armies[army.tile]
		if fogTargetTile.player == army.player:
			fogTargetTile.army += army.value
		else:
			fogTargetTile.army = army.value - fogTargetTile.army
		logging.info("      fogTargetTile {} updated army to {}".format(fogTargetTile.toString(), fogTargetTile.army))
		# breaks stuff real bad. Don't really want to do this anyway. 
		# Rather track the army through fog with no consideration of owning the tiles it crosses
		#fogTargetTile.player = army.player
		army.update_tile(fogTargetTile)
		self.armies[fogTargetTile] = army

	def get_expected_delta(self, tile):
		expected = 0
		if (tile.isCity or tile.isGeneral) and self.isCityBonus:
			expected += 1
		if self.lastMove != None and tile == self.lastMove.dest:
			if self.lastMove.non_friendly:
				expected -= self.lastMove.army_moved
			else:
				expected += self.lastMove.army_moved
			logging.info("Using lastMove.dest {} non_friendly {} army_moved {} to change expected delta to {}".format(self.lastMove.dest.toString(), self.lastMove.non_friendly, self.lastMove.army_moved, expected))
		#if tile == self.lastMove.source:
		#	if self.lastMove.non_friendly:
		#		expected -= self.lastMove.armyMoved
		#	else:
		#		expected += self.lastMove.armyMoved

		#army bonus should cancel out between source and dest tiles on movements
		#if tile.player != -1 and self.isArmyBonus:
		#	expected += 1
		return expected


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
		playerLargest = [None for x in range(len(self.map.players))]
		# don't do largest tile for now?
		#for tile in self.map.reachableTiles:
		#	if tile.player != -1 and (playerLargest[tile.player] == None or tile.army > playerLargest[tile.player].army):
		#		playerLargest[tile.player] = tile
		for tile in self.map.reachableTiles:
			tileNewlyCapturedByEnemy = tile.delta.oldOwner != tile.delta.newOwner and not tile.delta.gainedSight and tile.player != self.map.player_index
			if abs(tile.delta.armyDelta) > tile.army / 2:
				# maybe this came out of the fog?
				sourceFogArmy = self.find_fog_source(tile)
			if tile not in self.armies and tile.player != -1 and (playerLargest[tile.player] == tile or tile.army >= self.track_threshold or tileNewlyCapturedByEnemy):
				# then tile is an army.
				logging.info("{} Discovered as Army!".format(tile.toString()))
				army = Army(tile)
				self.armies[tile] = army

				# if tile WAS bordered by fog find the closest fog army and remove it (not tile.visible or tile.delta.gainedSight)
	def find_fog_source(self, tile):
		def valFunc(thisTile, prioObject):
			(dist, negArmy) = prioObject
			if (0-negArmy) - dist*2 < tile.army:
				return (0-negArmy)
			return -1

		def pathSortFunc(nextTile, prioObject):
			(dist, negArmy) = prioObject
			if nextTile.player == tile.player:
				negArmy -= nextTile.army
			else:
				negArmy += nextTile.army
			dist += 1
			return (dist, negArmy)
		fogSkipFunc = lambda nextTile, prioObject: nextTile.visible
		inputTiles = {}
		inputTiles[tile] = ((0, 0), 0)

		fogSourcePath = breadth_first_dynamic_max(self.map, inputTiles, valFunc, noNeutralCities=True, priorityFunc=pathSortFunc, skipFunc=fogSkipFunc, searchingPlayer = tile.player, noLog = True)
		if (fogSourcePath != None):
			logging.info("        For new army at tile {} we found fog source path???? {}".format(tile.toString(), fogSourcePath.toString()))
		else:
			logging.info("        NO fog source path for new army at {}".format(tile.toString()))
