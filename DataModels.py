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


class Path(object):
	def __init__(self, pathMove, pathLength, value, cityCount, pathDict):
		self.pathMove = pathMove
		self.value = value
		self.movesLeft = pathLength
		self.cityCount = cityCount
		self.pathDict = pathDict

	def GetNextMove():
		move = self.pathMove.move
		self.pathMove = self.pathMove.next
		self.movesLeft -= 1
		return move

def PathFromPathNode(pathEnd, path):
	if pathEnd == None or path == None:
		return None
	pathLength = pathEnd.turn
	value = pathEnd.value
	cityCount = path.cityCount
	pathDict = pathEnd.pathDict

	node = path
	turn = 0
	
	curVal = node.tile.army
	head = PathMove(Move(node.tile, node.parent.tile), None, node.parent.value, turn)
	
	prev = head
	node = node.parent
	while (node.parent != None):
		turn += 1
		prev.next = PathMove(Move(node.tile, node.parent.tile), None, node.parent.value, turn)
		prev = prev.next
		node = node.parent
	
	return Path(head, pathLength, value, cityCount, pathDict)

def get_tile_list_from_path_tuple(pathObj):
	return get_tile_list_from_path(pathObj[1])

def get_tile_list_from_path(path):
	if path == None:
		return None
	pathList = []
	while path != None:
		pathList.append(path.tile)
		path = path.parent
	return pathList
	

def get_tile_set_from_path_tuple(pathObj):
	return get_tile_set_from_path(pathObj[1])

def get_tile_set_from_path(path):
	tiles = set()
	while path != None:
		tiles.add(path.tile)
		path = path.parent
	return tiles


def reverse_path_tuple(pathTuple):
	(pathStart, path) = pathTuple
	return (reverse_path(pathStart), reverse_path(path))

def reverse_path(path):
	pathLast = path
	dist = path.turn
	newPath = PathNode(path.tile, None, path.value, 0, 0, None)
	path = path.parent
	while (path != None):		
		newPath = PathNode(path.tile, newPath, path.value, 0, 0, None)
		path = path.parent
	return newPath


def get_player_army_amount_on_path(path, player, startIdx = 0, endIdx = 1000):
	value = 0
	idx = 0
	while (path != None):
		if (path.tile.player == player and idx >= startIdx and idx <= endIdx):
			value += (path.tile.army - 1)
		path = path.parent
		idx += 1
	return value


class PathMove(object):
	def __init__(self, move, next, value, turn):
		self.move = move
		self.next = next
		self.turn = turn
	def __gt__(self, other):
		if (other == None):
			return True
		return self.turn > other.turn
	def __lt__(self, other):
		if (other == None):
			return True
		return self.turn < other.turn	

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

def stringPath(pathNode):
	val = "[{}] ".format(pathNode.value) 
	while (pathNode != None):
		val = val + str(pathNode.tile.x) + "," + str(pathNode.tile.y) + " "
		pathNode = pathNode.parent
	return val		


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
