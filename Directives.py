"""
	@ Travis Drake (EklipZ) eklipz.io - tdrake0x45 at gmail)
	April 2017
	Generals.io Automated Client - https://github.com/harrischristiansen/generals-bot
	EklipZ bot - Tries to play generals lol
"""

import logging
from enum import Enum


class Timings:
    def __init__(
        self,
        cycleTurns,
        quickExpandSplitTurns,
        splitTurns,
        launchTiming,
        offsetTurns,
        recalcTurn,
    ):
        self.cycleTurns = cycleTurns
        self.quickExpandTurns = quickExpandSplitTurns
        self.splitTurns = splitTurns
        self.offsetTurns = offsetTurns
        self.launchTiming = launchTiming
        self.nextRecalcTurn = recalcTurn

    def should_recalculate(self, turn):
        return turn == self.nextRecalcTurn

    def in_quick_expand_split(self, turn):
        adjustedTurn = self.get_split_turn(turn)
        return adjustedTurn <= self.quickExpandTurns

    def in_gather_split(self, turn):
        adjustedTurn = self.get_split_turn(turn)
        return self.quickExpandTurns < adjustedTurn < self.splitTurns

    def in_expand_split(self, turn):
        adjustedTurn = self.get_split_turn(turn)
        return adjustedTurn >= self.splitTurns

    def in_launch_split(self, turn):
        adjustedTurn = self.get_split_turn(turn)
        return (
            adjustedTurn >= self.launchTiming and adjustedTurn - self.launchTiming < 5
        )

    def get_split_turn(self, turn):
        adjustedTurn = (turn + self.offsetTurns) % self.cycleTurns
        return adjustedTurn

    def toString(self):
        return "C {}   Q {}   G {}   L {}   Off {}".format(
            self.cycleTurns,
            self.quickExpandTurns,
            self.splitTurns,
            self.launchTiming,
            self.offsetTurns,
        )

    def __str__(self):
        return self.toString()


class Directive:
    def __init__(self, type=None):
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
