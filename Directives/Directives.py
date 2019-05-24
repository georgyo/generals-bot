'''
	@ Travis Drake (EklipZ) eklipz.io - tdrake0x45 at gmail)
	April 2017
	Generals.io Automated Client - https://github.com/harrischristiansen/generals-bot
	EklipZ bot - Tries to play generals lol
'''

import logging
from enum import Enum

class Timings():
	def __init__(self, cycleTurns, splitTurns, offsetTurns):
		self.cycleTurns = cycleTurns
		self.splitTurns = splitTurns
		self.offsetTurns = offsetTurns

	def should_recalculate(self, turn):
		recalculateTurn = (turn + self.offsetTurns) % self.cycleTurns == 0
		#logging.info("Should recalculate? ((turn {} + self.offsetTurns {}) % self.cycleTurns {}) {} == 0: {}".format(turn, self.offsetTurns, self.cycleTurns, (turn + self.offsetTurns) % self.cycleTurns, recalculateTurn))
		if recalculateTurn:
			return True
		return False
	
	def toString(self):
		return "cycle {}, split {}, offset {}".format(self.cycleTurns, self.splitTurns, self.offsetTurns)


class Directive():
	def __init__(self, type = None):
		self.type = type

	# Return some number to indicate how important this move is. -1 or lower will not be made.
	# This doesn't necessarily need to calculate a full move etc, and should be performant.
	def get_priority(self):
		return -1

	# Returns the move to be made.
	def get_move(self):
		return None

	# Doesn't necessarily need to recalculate if the directive is cycle-based etc.
	def recalculate(self, turn):
		return

