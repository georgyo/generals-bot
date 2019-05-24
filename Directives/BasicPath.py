

from Directives.Directives import *

class BasicPath(Directive):
	def __init__(self, path, priority = 100):
		super("BasicPath")
		self.path = path
		self.priority = priority

	# 100 will be the default priority for paths
	def get_priority(self):
		return self.priority

	def get_move(self):
		inc = 0
		while ((self.path.start.tile.army <= 1 or self.path.start.tile.player != self.bot._map.player_index) and self.path.start.next != None):
			inc += 1
			if (self.path.start.tile.army <= 1):
				logging.info("!!!!\nMove was from square with 1 or 0 army\n!!!!! {},{} -> {},{}".format(self.path.start.tile.x, self.path.start.tile.y, self.path.start.next.tile.x, self.path.start.next.tile.y))
			elif (self.path.start.tile.player != self.bot._map.player_index):
				logging.info("!!!!\nMove was from square OWNED BY THE ENEMY\n!!!!! [{}] {},{} -> {},{}".format(self.path.start.tile.player, self.path.start.tile.x, self.path.start.tile.y, self.path.start.next.tile.x, self.path.start.next.tile.y))
			logging.info("{}: doing made move thing? Path: {}".format(inc, self.path.toString()))
			self.path.made_move()
			if inc > 20:
				raise ArithmeticError("bitch, what you doin?")
				
		if (self.path.start.next != None):
			dest = self.path.start.next.tile
			source = self.path.start.tile
			cleanPath = False
			while self.path != None and not cleanPath:
				if (self.path.start.next != None and self.path.start.next.next != None and self.path.start.tile == self.path.start.next.next.tile and self.path.start.next.tile.player == self.path.start.tile.player):
					logging.info("\n\n\n~~~~~~~~~~~\nCleaned double-back from path\n~~~~~~~~~~~~~\n\n~~~\n")
					self.path.made_move()
				elif (self.path.start.tile.player != self.bot._map.player_index or self.path.start.tile.army < 2):
					logging.info("\n\n\n~~~~~~~~~~~\nCleaned useless move from path\n~~~~~~~~~~~~~\n\n~~~\n")
					self.path.made_move()
				else:
					cleanPath = True
			if (self.path != None and self.path.start.next != None):
				move = Move(self.path.start.tile, self.path.start.next.tile, self.path.start.move_half)
				#self.info("MAKING MOVE FROM NEW PATH CLASS! Path {}".format(self.path.toString()))
				return self.bot.move_half_on_repetition(move, 6, 3)
		return None

	def recalculate(self, turn):
		if self.path != None and self.path.start.next != None and not self.bot.droppedMove(self.path.start.tile, self.path.start.next.tile):
			self.path.made_move()
			if self.path.length <= 0:
				logging.info("TERMINATING path BECAUSE <= 0 ???? Path better be over")
				self.path = None
			if self.path != None:
				if (self.path.start.next != None and self.path.start.next.next != None and self.path.start.next.next.next != None and self.path.start.tile == self.path.start.next.next.tile and self.path.start.next.tile == self.path.start.next.next.next.tile):
					logging.info("\n\n\n~~~~~~~~~~~\nDe-duped path\n~~~~~~~~~~~~~\n\n~~~\n")
					self.path.made_move()
					self.path.made_move()
					self.path.made_move()
					self.path.made_move()
				elif (self.path.start.next != None and self.path.start.tile.x == self.path.start.next.tile.x and self.path.start.tile.y == self.path.start.next.tile.y):
					logging.warning("           wtf, doubled up tiles in path?????")
					self.path.made_move()
					self.path.made_move()	
		elif self.path != None:
			logging.info("         --         missed move?")