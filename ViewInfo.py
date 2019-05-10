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



class PathColorer(object):
	def __init__(self, path, r, g, b, alpha = 200, alphaDecreaseRate = 4, alphaMinimum = 100):
		self.path = path
		self.color = (r, g, b)
		self.alpha = alpha
		self.alphaDecreaseRate = alphaDecreaseRate
		self.alphaMinimum = alphaMinimum


class ViewInfo(object):
	def __init__(self, countHist, cols, rows):
		self.lastSearched = []
		self.searchHistory = []
		for i in range(countHist):
			self.searchHistory.append([])
		self.evaluatedGrid = []
		self.lastEvaluatedGrid = []
		self.infoText = "(replace with whatever text here)"
		self.cols = cols
		self.rows = rows
		self.paths = deque()
		self.readyToDraw = False

	
	def turnInc(self):
		countHist = len(self.searchHistory)
		for i in range(countHist):
			if (i == countHist - 2):
				break
			self.searchHistory[countHist - i - 1] = self.searchHistory[countHist - i - 2]
		self.searchHistory[0] = self.lastSearched
		self.lastSearched = []

		self.lastEvaluatedGrid = self.evaluatedGrid
		if (len(self.lastEvaluatedGrid) == 0):
			self.lastEvaluatedGrid = [[0 for x in range(self.rows)] for y in range(self.cols)]
		self.evaluatedGrid = [[0 for x in range(self.rows)] for y in range(self.cols)]

	def addSearched(self, tile):
		self.lastSearched.append(tile)