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
import math
from collections import deque 
from queue import PriorityQueue
from pprint import pprint,pformat



class PathMove(object):
	def __init__(self, tile, next = None, prev = None, move_half = False):
		self.tile = tile
		self.next = next
		self.prev = prev
		self.move_half = move_half

	def clone(self):
		return PathMove(self.tile, self.next, self.prev)
	
	def toString(self):
		prevVal = "[]"
		if self.prev != None:
			prevVal = "[{},{}]".format(self.prev.tile.x, self.prev.tile.y)
		nextVal = "[]"
		if self.next != None:
			nextVal = "[{},{}]".format(self.next.tile.x, self.next.tile.y)
		myVal = "[{},{}]".format(self.tile.x, self.tile.y)

		val = "(prev:{} me:{} next:{})".format(prevVal, myVal, nextVal)
		return val
	#def __gt__(self, other):
	#	if (other == None):
	#		return True
	#	return self.turn > other.turn
	#def __lt__(self, other):
	#	if (other == None):
	#		return True
	#	return self.turn < other.turn


class Path(object):
	def __init__(self, value = 0):
		self.start = None
		self._pathQueue = deque()
		self._pathSet = None
		self.tail = None
		self._tileSet = None
		self.value = value
	def __gt__(self, other):
		if (other == None):
			return True
		return self.length > other.length
	def __lt__(self, other):
		if (other == None):
			return True
		return self.length < other.length

	@property
	def length(self):
		return len(self._pathQueue) - 1

	@property
	def tileSet(self):
		if self._tileSet == None:
			self._tileSet = set()
			node = self.start
			while node != None:
				self._tileSet.add(node.tile)
				node = node.next
		return self._tileSet
	@tileSet.setter
	def tileSet(self, value):
		raise AssertionError("NO SETTING!")

	def add_next(self, nextTile):
		move = PathMove(nextTile)
		move.prev = self.tail
		if self.start == None:
			self.start = move
		if self.tail != None:
			self.tail.next = move
		if self._tileSet != None:
			self._tileSet.add(nextTile)
		self.tail = move
		self._pathQueue.append(move)

	def add_start(self, startTile):
		move = PathMove(startTile)
		if self.start != None:
			move.next = self.start
			self.start.prev = move
		self.start = move
		if self._tileSet != None:
			self._tileSet.add(startTile)
		self._pathQueue.appendleft(move)

	def made_move(self):
		if len(self._pathQueue) == 0:
			logging.info(", bitch? Why you tryin to made_move when there aint no moves to made?")
			return
		if self._tileSet != None:
			self._tileSet.remove(self.start.tile)
		self.start = self.start.next
		return self._pathQueue.popleft()

	def remove_end(self):
		if len(self._pathQueue) == 0:
			logging.info(", bitch? Removing nothing??")
			return
		if self._tileSet != None:
			self._tileSet.remove(self.tail.tile)
		move = self._pathQueue.pop()
		self.tail = self.tail.prev
		if self.tail != None:
			self.tail.next = None
		return move

	def calculate_value(self, forPlayer):
		val = 0
		node = self.start
		i = 0
		while (node != None):
			tile = node.tile
			if tile.player == forPlayer:
				val += tile.army - 1
				if tile.isCity or tile.isGeneral:
					val += math.floor(i * 0.5)
			else:
				val -= tile.army + 1
				if tile.isCity or tile.isGeneral and tile.player != -1:
					val -= math.floor(i * 0.5)
			node = node.next
			i += 1
		self.value = val
		return val

	def clone(self):
		newPath = Path()
		node = self.start
		while node != None:
			newPath.add_next(node.tile)
			node = node.next
		return newPath

	def get_reversed(self):
		if (self.start == None or self.start.next == None):
			return self.clone()

		newPath = Path()
		temp = self.tail
		while temp != None:
			newPath.add_next(temp.tile)
			temp = temp.prev

		return newPath
	
	# 10 things, want 3 end
	def get_subsegment(self, count, end=False):
		newPath = self.clone()
		length = len(self._pathQueue)
		i = 0
		while i < length - count:
			i += 1
			if end:
				newPath.made_move()
			else:
				newPath.remove_end()
		return newPath

	def toString(self):
		val = "[{} len {}] ".format(self.value, self.length)
		node = self.start
		while (node != None):
			val = val + str(node.tile.x) + "," + str(node.tile.y) + " "
			node = node.next
		return val

	
		
	

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
