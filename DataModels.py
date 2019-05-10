'''
	@ Travis Drake (EklipZ) eklipz.io - tdrake0x45 at gmail)
	April 2017
	Generals.io Automated Client - https://github.com/harrischristiansen/generals-bot
	EklipZ bot - Tries to play generals lol
'''

import logging
from copy import deepcopy
import time
import json
from collections import deque 
from queue import PriorityQueue
from pprint import pprint,pformat


class PathNode(object):
	def __init__(self, tile, parent, value, turn, cityCount, pathDict):
		self.tile = tile
		self.parent = parent
		self.value = value
		self.turn = turn
		self.move_half = False
		self.cityCount = cityCount
		self.pathDict = pathDict
	def __gt__(self, other):
		if (other == None):
			return True
		return self.turn > other.turn
	def __lt__(self, other):
		if (other == None):
			return True
		return self.turn < other.turn	

def get_tile_list_from_path(pathObject):
	path = pathObject.start
	if path == None:
		return None
	pathList = []
	while path != None:
		pathList.append(path.tile)
		path = path.next
	return pathList
	

def get_tile_set_from_path(pathObject):
	return pathObject.tileSet


def reverse_path(path):
	newPath = path.get_reversed()
	return newPath


def get_player_army_amount_on_path(path, player, startIdx = 0, endIdx = 1000):
	value = 0
	idx = 0
	pathNode = path.start
	while (pathNode != None):
		if (pathNode.tile.player == player and idx >= startIdx and idx <= endIdx):
			value += (pathNode.tile.army - 1)
		pathNode = pathNode.next
		idx += 1
	return value


class GatherNode(object):
	def __init__(self, tile, fromTile, turn):
		self.tile = tile
		self.fromTile = fromTile
		self.value = 0
		self.turn = turn
		self.neutrals = 0
		self.children = []


class Move(object):
	def __init__(self, source, dest, move_half = False):
		self.source = source
		self.dest = dest
		self.move_half = move_half

	def __gt__(self, other):
		if (other == None):
			return True
		return self.source.army - self.dest.army > other.source.army - other.dest.army
	def __lt__(self, other):
		if (other == None):
			return False
		return self.source.army - self.dest.army < other.source.army - other.dest.army
	def __eq__(self, other):
		if (None == other):
			return False
		return self.source.army - self.dest.army == other.source.army - other.dest.army
