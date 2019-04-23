'''
	@ Harris Christiansen (Harris@HarrisChristiansen.com)
	January 2016
	Generals.io Automated Client - https://github.com/harrischristiansen/generals-bot
	Game Viewer
'''
import os
import pygame
import threading
import time
from collections import deque 
from copy import deepcopy
from base.client.generals import _spawn


# Color Definitions
BLACK = (0,0,0)
GRAY_DARK = (52,52,52)
UNDISCOVERED_GRAY = (110,110,110)
GRAY = (160,160,160)
WHITE = (255,255,255)
RED = (200,40,40)
P_RED = (235,55,40)
P_BLUE = (30,30,230)
P_GREEN = (70,130,30)
P_PURPLE = (128,30,128)
P_TEAL = (30,128,128)
P_DARK_GREEN = (20,90,50)
P_DARK_RED = (128,10,40)
P_YELLOW = (170,140,20)
P_BRIGHT_GREEN = (10,20,10)
#P_BRIGHT_GREEN = (10,225,90)
PLAYER_COLORS = [P_RED, P_BLUE, P_GREEN, P_PURPLE, P_TEAL, P_DARK_GREEN, P_YELLOW, P_DARK_RED, P_BRIGHT_GREEN]
FOG_COLOR_OFFSET = 25
KING_COLOR_OFFSET = 35

UP_ARROW = "^"
DOWN_ARROW = "v"
LEFT_ARROW = "<"
RIGHT_ARROW = ">"

# Table Properies
CELL_WIDTH = 32
CELL_HEIGHT = 30
CELL_MARGIN = 1
SCORES_ROW_HEIGHT = 33
INFO_ROW_HEIGHT = 25
PLUS_DEPTH = 9




class GeneralsViewer(object):
	def __init__(self, name=None):
		self._name = name
		self._receivedUpdate = False
		self._readyRender = False
		self.Arrow = None
		self.lineArrow = None
		

	def updateGrid(self, update):
		updateDir = dir(update)
		self._map = update
		if "bottomText" in updateDir:
			self._bottomText = update.bottomText
		self._scores = sorted(update.scores, key=lambda general: general['total'], reverse=True) # Sort Scores
		
		self._receivedUpdate = True

		if "collect_path" in updateDir:
			self._collect_path = [(path.x, path.y) for path in update.collect_path]
		else:
			self._collect_path = None

	def _initViewier(self, position):
		os.environ['SDL_VIDEO_WINDOW_POS'] = "%d,%d" % position
		os.environ['SDL_VIDEO_ALLOW_SCREENSAVER'] = "1"
		os.environ['SDL_HINT_VIDEO_ALLOW_SCREENSAVER'] = "1"
		pygame.init()

		# Set Window Size
		window_height = self._map.rows * (CELL_HEIGHT + CELL_MARGIN) + CELL_MARGIN + SCORES_ROW_HEIGHT + INFO_ROW_HEIGHT
		window_width = self._map.cols * (CELL_WIDTH + CELL_MARGIN) + CELL_MARGIN
		self._window_size = [window_width, window_height]
		self._screen = pygame.display.set_mode(self._window_size)
		self._transparent = pygame.Surface(self._window_size, pygame.SRCALPHA)

		window_title = "Generals IO Bot"
		if (self._name != None):
			window_title += " - " + str(self._name)
		pygame.display.set_caption(window_title)
		self._font = pygame.font.SysFont('Arial', int(CELL_HEIGHT / 2) - 2)
		self._fontSmall = pygame.font.SysFont('Arial', int(CELL_HEIGHT / 3))
		self._fontLrg = pygame.font.SysFont('Arial', CELL_HEIGHT - 5) 
		self._bottomText = ""

		self._clock = pygame.time.Clock()
		
		self.pathAlphas = []
		self.Arrow = [(CELL_WIDTH / 2, 0), (CELL_WIDTH / 8, CELL_HEIGHT / 2), (CELL_WIDTH / 2, CELL_HEIGHT / 4), (7 * CELL_WIDTH / 8, CELL_HEIGHT / 2)]
		# self.Arrow = [(CELL_WIDTH / 2, 0), (CELL_WIDTH / 8, CELL_HEIGHT / 2), (CELL_WIDTH / 2, CELL_HEIGHT / 4), (7 * CELL_WIDTH / 8, CELL_HEIGHT / 2)]
		
		s = pygame.Surface((CELL_WIDTH, CELL_HEIGHT))
		# first, "erase" the surface by filling it with a color and
		# setting this color as colorkey, so the surface is empty
		s.fill(WHITE)
		s.set_colorkey(WHITE)
		pygame.draw.line(s, BLACK, (CELL_WIDTH / 2, 0), (CELL_WIDTH / 2, CELL_HEIGHT), 2)
		# pygame.draw.line(s, WHITE, (CELL_WIDTH / 2, 0), (CELL_WIDTH / 2, CELL_HEIGHT), 1)
		pygame.draw.line(s, BLACK, (CELL_WIDTH / 2, CELL_HEIGHT), (CELL_WIDTH * 3 / 8, CELL_HEIGHT * 5 / 8), 2)
		# pygame.draw.line(s, WHITE, (CELL_WIDTH / 2, CELL_HEIGHT), (CELL_WIDTH * 3 / 8, CELL_HEIGHT * 5 / 8), 1)
		pygame.draw.line(s, BLACK, (CELL_WIDTH / 2, CELL_HEIGHT), (CELL_WIDTH * 5 / 8 - 1, CELL_HEIGHT * 5 / 8), 2)
		# pygame.draw.line(s, WHITE, (CELL_WIDTH / 2, CELL_HEIGHT), (CELL_WIDTH * 5 / 8, CELL_HEIGHT * 5 / 8), 1)
		self.lineArrow = s
		self.repId = self._map.replay_url.split("/").pop()
		self.logDirectory = "H:\\GeneralsLogs\\{}-{}".format(self._map.usernames[self._map.player_index], self.repId)
		if not os.path.exists(self.logDirectory):
			try:
				os.makedirs(self.logDirectory)
			except:
				logging.info("Couldn't create dir")
		_spawn(self.save_images)



	def mainViewerLoop(self, alignTop = True, alignLeft = True):
		while not self._receivedUpdate: # Wait for first update
			time.sleep(0.1)
		x = 3 if alignLeft else 1920 - 3 - (CELL_WIDTH + CELL_MARGIN) * self._map.cols 
		y = 3 if alignTop else 1080 - 3 - (CELL_HEIGHT + CELL_MARGIN) * self._map.rows
		self._initViewier((x, y))

		done = False
		while not done:
			if (self._receivedUpdate):
				self._drawGrid()
				self._receivedUpdate = False
				self._readyRender = True
			for event in pygame.event.get(): # User did something
				if event.type == pygame.QUIT: # User clicked quit
					done = True # Flag done
				elif event.type == pygame.MOUSEBUTTONDOWN: # Mouse Click
					pos = pygame.mouse.get_pos()
					
					# Convert screen to grid coordinates
					column = pos[0] // (CELL_WIDTH + CELL_MARGIN)
					row = pos[1] // (CELL_HEIGHT + CELL_MARGIN)
					
					print("Click ", pos, "Grid coordinates: ", row, column)


			time.sleep(0.1)
		time.sleep(2.0)
		pygame.quit() # Done.  Quit pygame.

	def _drawGrid(self):
		try:


			self._screen.fill(BLACK) # Set BG Color
			self._transparent.fill((0,0,0,0)) # transparent
			allInText = " "
			if self._map.ekBot.allIn:
				allInText = "+"

			# Draw Bottom Info Text
			self._screen.blit(self._fontLrg.render("Turn: %d, %s%s" % (self._map.turn, allInText, self._map.ekBot.all_in_counter), True, WHITE), (10, self._window_size[1] - INFO_ROW_HEIGHT))
			self._screen.blit(self._font.render(self._map.ekBot.viewInfo.infoText, True, WHITE), (200, self._window_size[1] - INFO_ROW_HEIGHT))
		
			# Draw Scores
			pos_top = self._window_size[1] - INFO_ROW_HEIGHT - SCORES_ROW_HEIGHT
			score_width = self._window_size[0] / len(self._map.players)
			      #self._scores = sorted(update.scores, key=lambda general: general['total'], reverse=True)
			if (self._map != None):				
				playersByScore = sorted(self._map.players, key=lambda player: player.score, reverse=True) # Sort Scores
				
				for i, player in enumerate(playersByScore):
					if player != None:
						score_color = PLAYER_COLORS[player.index]
						if (player.leftGame):
							score_color = BLACK
						if (player.dead):
							score_color = GRAY_DARK
						pygame.draw.rect(self._screen, score_color, [score_width * i, pos_top, score_width, SCORES_ROW_HEIGHT])
						userName = self._map.usernames[player.index]
						userString = "{} ({})".format(userName, player.stars)
						try:
							self._screen.blit(self._font.render(userString, True, WHITE), (score_width * i + 3, pos_top + 1))
						except:
							userString = "{} ({})".format("INVALID_NAME", player.stars)
							self._screen.blit(self._font.render(userString, True, WHITE), (score_width * i + 3, pos_top + 1))
							

						playerSubtext = "{} on {} ({})".format(player.score, player.tileCount, player.cityCount)
						if player.index != self._map.player_index:
							playerSubtext += " [{}]".format(str(int(self._map.ekBot.playerTargetScores[player.index])))
						self._screen.blit(self._font.render(playerSubtext, True, WHITE), (score_width * i + 3, pos_top + 1 + self._font.get_height()))
			#for i, score in enumerate(self._scores):
			#	score_color = PLAYER_COLORS[int(score['i'])]
			#	if (score['dead'] == True):
			#		score_color = GRAY_DARK
			#	pygame.draw.rect(self._screen, score_color, [score_width * i, pos_top, score_width, SCORES_ROW_HEIGHT])
			#	userString = self._map.usernames[int(score['i'])]
			#	if (self._map.stars): 
			#		userString = userString + " (" + str(self._map.stars[int(score['i'])]) + ")"
			#	self._screen.blit(self._font.render(userString, True, WHITE), (score_width * i + 3, pos_top + 1))
			#	self._screen.blit(self._font.render(str(score['total']) + " on " + str(score['tiles']), True, WHITE), (score_width * i + 3, pos_top + 1 + self._font.get_height()))
		
			# Draw Grid
			#print("drawing grid")
			for row in range(self._map.rows):
				for column in range(self._map.cols):
					tile = self._map.grid[row][column]
					# Determine BG Color
					color = WHITE
					color_font = WHITE
					if tile.ismountain(): # Mountain
						color = BLACK
					elif tile.player >= 0:
						playercolor = PLAYER_COLORS[tile.player]
						colorR = playercolor[0]
						colorG = playercolor[1]
						colorB = playercolor[2]				
						if (tile.isCity or tile.isGeneral):
							colorR = colorR + KING_COLOR_OFFSET if colorR <= 255 - KING_COLOR_OFFSET else 255
							colorG = colorG + KING_COLOR_OFFSET if colorG <= 255 - KING_COLOR_OFFSET else 255
							colorB = colorB + KING_COLOR_OFFSET if colorB <= 255 - KING_COLOR_OFFSET else 255
						if (not tile.isvisible()): 
							colorR = colorR / 2.3 + FOG_COLOR_OFFSET
							colorG = colorG / 2.3 + FOG_COLOR_OFFSET
							colorB = colorB / 2.3 + FOG_COLOR_OFFSET
						color = (colorR, colorG, colorB)
					elif tile.isobstacle(): # Obstacle
						color = GRAY_DARK
					elif not tile.discovered:
						color = UNDISCOVERED_GRAY					
					elif tile.isCity and tile.player == -1:
						color = UNDISCOVERED_GRAY
						if (tile.isvisible()):
							color = GRAY
						color_font = WHITE
					elif not tile.isvisible(): 
						color = GRAY
					else:
						color_font = BLACK

					pos_left = (CELL_MARGIN + CELL_WIDTH) * column + CELL_MARGIN
					pos_top = (CELL_MARGIN + CELL_HEIGHT) * row + CELL_MARGIN
					if (tile in self._map.generals): # General
						# Draw Plus
						pygame.draw.rect(self._screen, color, [pos_left + PLUS_DEPTH, pos_top, CELL_WIDTH - PLUS_DEPTH * 2, CELL_HEIGHT])
						pygame.draw.rect(self._screen, color, [pos_left, pos_top + PLUS_DEPTH, CELL_WIDTH, CELL_HEIGHT - PLUS_DEPTH * 2])
					elif (tile.isCity): # City
						# Draw Circle
						
						pos_left_circle = int(pos_left + (CELL_WIDTH / 2))
						pos_top_circle = int(pos_top + (CELL_HEIGHT / 2))
						pygame.draw.circle(self._screen, color, [pos_left_circle, pos_top_circle], int(CELL_WIDTH / 2))
					else:
						# Draw Rect
						pygame.draw.rect(self._screen, color, [pos_left, pos_top, CELL_WIDTH, CELL_HEIGHT])


			# Draw path
			#print("drawing path")
			path = self._map.ekBot.curPath
			alpha = 255
			alphaDec = 8
			alphaMin = 145
			while (path != None and path.parent != None):
				s = pygame.Surface((CELL_WIDTH, CELL_HEIGHT))
				# first, "erase" the surface by filling it with a color and
				# setting this color as colorkey, so the surface is empty
				s.fill(WHITE)
				s.set_colorkey(WHITE)
			
				# after drawing the circle, we can set the 
				# alpha value (transparency) of the surface
				tile = path.tile
				toTile = path.parent.tile			
				#print("drawing path {},{} -> {},{}".format(tile.x, tile.y, toTile.x, toTile.y))
				pos_left = (CELL_MARGIN + CELL_WIDTH) * tile.x + CELL_MARGIN
				pos_top = (CELL_MARGIN + CELL_HEIGHT) * tile.y + CELL_MARGIN
				xOffs = 0
				yOffs = 0
				pygame.draw.polygon(s, BLACK, self.Arrow)
				if (tile.x - toTile.x > 0): #left
					#print("left " + str(tile.x) + "," + str(tile.y))
					s = pygame.transform.rotate(s, 90)
					xOffs = -0.3
				elif (tile.x - toTile.x < 0): #right
					#print("right " + str(tile.x) + "," + str(tile.y))
					s = pygame.transform.rotate(s, 270)
					xOffs = 0.3		
				elif (tile.y - toTile.y > 0): #up
					#print("up " + str(tile.x) + "," + str(tile.y))
					yOffs = -0.3
				elif (tile.y - toTile.y < 0): #down
					#print("down " + str(tile.x) + "," + str(tile.y))
					s = pygame.transform.flip(s, False, True)
					yOffs = 0.3

			
				s.set_alpha(alpha)
				self._screen.blit(s, (pos_left + xOffs * CELL_WIDTH, pos_top + yOffs * CELL_HEIGHT))
				path = path.parent	
				alpha -= alphaDec					
				if (alpha < alphaMin):
					alpha = alphaMin

			self.drawGathers()

			
			if (self._map.ekBot.dangerAnalyzer != None and self._map.ekBot.dangerAnalyzer.anyThreat):

				for threat in [self._map.ekBot.dangerAnalyzer.fastestVisionThreat, self._map.ekBot.dangerAnalyzer.fastestThreat, self._map.ekBot.dangerAnalyzer.highestThreat]:
					if threat == None:
						continue
					# Draw danger path
					#print("drawing path")
					alpha = 255
					alphaDec = 10
					alphaMin = 145				
				
					path = threat.path.pathMove
					while path != None:
						s = pygame.Surface((CELL_WIDTH, CELL_HEIGHT))
						# first, "erase" the surface by filling it with a color and
						# setting this color as colorkey, so the surface is empty
						s.fill(WHITE)
						s.set_colorkey(WHITE)
			
						# after drawing the circle, we can set the 
						# alpha value (transparency) of the surface
						tile = path.move.source
						toTile = path.move.dest
						#print("drawing path {},{} -> {},{}".format(tile.x, tile.y, toTile.x, toTile.y))
						pos_left = (CELL_MARGIN + CELL_WIDTH) * tile.x + CELL_MARGIN
						pos_top = (CELL_MARGIN + CELL_HEIGHT) * tile.y + CELL_MARGIN
						xOffs = 0
						yOffs = 0
						pygame.draw.polygon(s, BLACK, self.Arrow)
						if (tile.x - toTile.x > 0): #left
							#print("left " + str(tile.x) + "," + str(tile.y))
							s = pygame.transform.rotate(s, 90)
							xOffs = -0.3
						elif (tile.x - toTile.x < 0): #right
							#print("right " + str(tile.x) + "," + str(tile.y))
							s = pygame.transform.rotate(s, 270)
							xOffs = 0.3		
						elif (tile.y - toTile.y > 0): #up
							#print("up " + str(tile.x) + "," + str(tile.y))
							yOffs = -0.3
						elif (tile.y - toTile.y < 0): #down
							#print("down " + str(tile.x) + "," + str(tile.y))
							s = pygame.transform.flip(s, False, True)
							yOffs = 0.3

			
						s.set_alpha(alpha)
						self._screen.blit(s, (pos_left + xOffs * CELL_WIDTH, pos_top + yOffs * CELL_HEIGHT))
						path = path.next	
						alpha -= alphaDec					
						if (alpha < alphaMin):
							alpha = alphaMin
		
			for tile in self._map.ekBot.viewInfo.lastSearched:
				pos_left = (CELL_MARGIN + CELL_WIDTH) * tile.x + CELL_MARGIN
				pos_top = (CELL_MARGIN + CELL_HEIGHT) * tile.y + CELL_MARGIN
				pos_left_circle = int(pos_left + (CELL_WIDTH / 2))
				pos_top_circle = int(pos_top + (CELL_HEIGHT / 2))
				pygame.draw.circle(self._screen, BLACK, [pos_left_circle, pos_top_circle], int(CELL_WIDTH / 2 - 2), 7)
				pygame.draw.circle(self._screen, RED, [pos_left_circle, pos_top_circle], int(CELL_WIDTH / 2) - 5, 1)
				#pygame.draw.circle(self._screen, RED, [pos_left_circle, pos_top_circle], int(CELL_WIDTH / 2) - 10, 1)
			for approx in self._map.ekBot.generalApproximations:
				if (approx[2] > 0):
					pos_left = (CELL_MARGIN + CELL_WIDTH) * approx[0] + CELL_MARGIN
					pos_top = (CELL_MARGIN + CELL_HEIGHT) * approx[1] + CELL_MARGIN
					pos_left_circle = int(pos_left + (CELL_WIDTH / 2))
					pos_top_circle = int(pos_top + (CELL_HEIGHT / 2))
					pygame.draw.circle(self._screen, BLACK, [pos_left_circle, pos_top_circle], int(CELL_WIDTH / 2 - 2), 7)
					pygame.draw.circle(self._screen, RED, [pos_left_circle, pos_top_circle], int(CELL_WIDTH / 2) - 5, 1)
					#pygame.draw.circle(self._screen, RED, [pos_left_circle, pos_top_circle], int(CELL_WIDTH / 2) - 10, 1)
			#print("history")
			s = pygame.Surface((CELL_WIDTH, CELL_HEIGHT))
			s.fill(WHITE)
			s.set_colorkey(WHITE)

			pygame.draw.circle(s, BLACK, [int(CELL_WIDTH / 2), int(CELL_HEIGHT / 2)], int(CELL_WIDTH / 2 - 2), 7)
			pygame.draw.circle(s, RED, [int(CELL_WIDTH / 2), int(CELL_HEIGHT / 2)], int(CELL_WIDTH / 2) - 5, 1)
			#pygame.draw.circle(s, RED, [int(CELL_WIDTH / 2), int(CELL_HEIGHT / 2)], int(CELL_WIDTH / 2) - 10, 1)
			for i in range(len(self._map.ekBot.viewInfo.searchHistory)):
				hist = self._map.ekBot.viewInfo.searchHistory[i]
				alpha = 200 - 20 * i
				s.set_alpha(alpha)
				for tile in hist:
					pos_left = (CELL_MARGIN + CELL_WIDTH) * tile.x + CELL_MARGIN
					pos_top = (CELL_MARGIN + CELL_HEIGHT) * tile.y + CELL_MARGIN
					# first, "erase" the surface by filling it with a color and
					# setting this color as colorkey, so the surface is empty
					self._screen.blit(s, (pos_left, pos_top))
			#print("surface")
			s = pygame.Surface((CELL_WIDTH, CELL_HEIGHT))
			s.fill(WHITE)
			s.set_colorkey(WHITE)
			pygame.draw.line(s, BLACK, (0, 0), (CELL_WIDTH, CELL_HEIGHT), 4)
			pygame.draw.line(s, RED, (0, 0), (CELL_WIDTH, CELL_HEIGHT), 2)
			pygame.draw.line(s, BLACK, (0, CELL_HEIGHT), (CELL_WIDTH, 0), 4)
			pygame.draw.line(s, RED, (0, CELL_HEIGHT), (CELL_WIDTH, 0), 2)
			#print("val")
			if (self._map != None and self._map.ekBot != None and self._map.ekBot.viewInfo.evaluatedGrid != None and len(self._map.ekBot.viewInfo.evaluatedGrid) > 0):
				#print("if")
				for row in range(self._map.rows):
					for column in range(self._map.cols):		
						#print("loop")
						countEvaluated = int(self._map.ekBot.viewInfo.evaluatedGrid[column][row] + self._map.ekBot.viewInfo.lastEvaluatedGrid[column][row]);
						#print("loopVal")
						if (countEvaluated > 0):					
							#print("CountVal: {},{}: {}".format(column, row, countEvaluated))
							pos_left = (CELL_MARGIN + CELL_WIDTH) * column + CELL_MARGIN
							pos_top = (CELL_MARGIN + CELL_HEIGHT) * row + CELL_MARGIN
							alpha = int(75 + countEvaluated * 3)
							s.set_alpha(alpha if alpha < 255 else 255)
							self._screen.blit(s, (pos_left, pos_top))
			#print("deltas")
			#print("drawing deltas")
			# Draw deltas
			for row in range(self._map.rows):
				for column in range(self._map.cols):
					tile = self._map.grid[row][column]
					pos_left = (CELL_MARGIN + CELL_WIDTH) * column + CELL_MARGIN
					pos_top = (CELL_MARGIN + CELL_HEIGHT) * row + CELL_MARGIN

					if (tile.delta.toTile != None):
						if (tile.x - tile.delta.toTile.x > 0): #left
							#print("left " + str(tile.x) + "," + str(tile.y))
							pygame.draw.polygon(self._screen, GRAY_DARK, [(pos_left + CELL_WIDTH / 4, pos_top), (pos_left + CELL_WIDTH / 4, pos_top + CELL_HEIGHT), (pos_left - CELL_WIDTH / 4, pos_top + CELL_HEIGHT / 2)])
						elif (tile.x - tile.delta.toTile.x < 0): #right
							#print("right " + str(tile.x) + "," + str(tile.y))
							pygame.draw.polygon(self._screen, GRAY_DARK, [(pos_left + 3 * CELL_WIDTH / 4, pos_top), (pos_left + 3 * CELL_WIDTH / 4, pos_top + CELL_HEIGHT), (pos_left + 5 * CELL_WIDTH / 4, pos_top + CELL_HEIGHT / 2)])			
						elif (tile.y - tile.delta.toTile.y > 0): #up
							#print("up " + str(tile.x) + "," + str(tile.y))
							pygame.draw.polygon(self._screen, GRAY_DARK, [(pos_left, pos_top + CELL_HEIGHT / 4), (pos_left + CELL_WIDTH, pos_top + CELL_HEIGHT / 4), (pos_left + CELL_WIDTH / 2, pos_top - CELL_HEIGHT / 4)])	
						elif (tile.y - tile.delta.toTile.y < 0): #down
							#print("down " + str(tile.x) + "," + str(tile.y))
							pygame.draw.polygon(self._screen, GRAY_DARK, [(pos_left, pos_top + 3 * CELL_HEIGHT / 4), (pos_left + CELL_WIDTH, pos_top + 3 * CELL_HEIGHT / 4), (pos_left + CELL_WIDTH / 2, pos_top + 5 * CELL_HEIGHT / 4)])			



			#print("drawing text")
			#draw text
			for row in range(self._map.rows):
				for column in range(self._map.cols):
					tile = self._map.grid[row][column]	
					pos_left = (CELL_MARGIN + CELL_WIDTH) * column + CELL_MARGIN
					pos_top = (CELL_MARGIN + CELL_HEIGHT) * row + CELL_MARGIN
					color = WHITE
					color_font = WHITE
					if tile.ismountain(): # Mountain
						color = BLACK
					elif tile.player >= 0:
						playercolor = PLAYER_COLORS[tile.player]
						colorR = playercolor[0]
						colorG = playercolor[1]
						colorB = playercolor[2]				
						if (tile.isCity or tile.isGeneral):
							colorR = colorR + KING_COLOR_OFFSET if colorR <= 255 - KING_COLOR_OFFSET else 255
							colorG = colorG + KING_COLOR_OFFSET if colorG <= 255 - KING_COLOR_OFFSET else 255
							colorB = colorB + KING_COLOR_OFFSET if colorB <= 255 - KING_COLOR_OFFSET else 255
						if (not tile.isvisible()): 
							colorR = colorR / 2 + 40
							colorG = colorG / 2 + 40
							colorB = colorB / 2 + 40
						color = (colorR, colorG, colorB)
					elif tile.isobstacle(): # Obstacle
						color = GRAY_DARK
					elif not tile.discovered:
						color = UNDISCOVERED_GRAY					
					elif tile.isCity and tile.player == -1:
						color = UNDISCOVERED_GRAY
						if (tile.isvisible()):
							color = GRAY
						color_font = WHITE
					elif not tile.isvisible(): 
						color = GRAY
					else:
						color_font = BLACK

					# Draw Text Value
					if (tile.army != 0 and tile.discovered): # Don't draw on empty tiles
						textVal = str(tile.army)
						self._screen.blit(self._font.render(textVal, True, color_font), (pos_left + 2, pos_top + CELL_HEIGHT / 4))			
					# Draw delta
					if (tile.delta.armyDelta != 0): # Don't draw on empty tiles
						textVal = str(tile.delta.armyDelta)
						self._screen.blit(self._fontSmall.render(textVal, True, color_font), (pos_left + 2, pos_top + CELL_HEIGHT / 2))
					# Draw coords					
					textVal = "{},{}".format(tile.x, tile.y)
					self._screen.blit(self._fontSmall.render(textVal, True, color_font), (pos_left, pos_top - 2))
					
					if (self._map.ekBot.leafValueGrid != None):
						leafVal = self._map.ekBot.leafValueGrid[column][row]
						if (leafVal != None):
							textVal = "{0:.0f}".format(leafVal)
							if (leafVal == -1000000): #then was skipped
								textVal = "x"		
							self._screen.blit(self._fontSmall.render(textVal, True, color_font), (pos_left + CELL_WIDTH / 3, pos_top + 2 * CELL_HEIGHT / 3))
							
			#print("replay {} turn {}".format(self.repId, self._map.turn))
			# Limit to 60 frames per second
			self._clock.tick(60)
 
			# Go ahead and update the screen with what we've drawn.
			pygame.display.flip()
		except:
			raise
			# print("Unexpected error:", sys.exc_info()[0])
	
	def drawGathers(self):
		if (self._map.ekBot.gatherNodes != None):
			q = deque()
			for node in self._map.ekBot.gatherNodes:
				q.appendleft(node)
			while (len(q) > 0):
				node = q.pop()
				for child in node.children:
					q.appendleft(child)
				if node.fromTile != None:
					xDiff = node.tile.x - node.fromTile.x
					yDiff = node.tile.y - node.fromTile.y
					s = None
					if (xDiff > 0):
						pos_left = (CELL_MARGIN + CELL_WIDTH) * node.fromTile.x + CELL_MARGIN + CELL_WIDTH / 2
						pos_top = (CELL_MARGIN + CELL_HEIGHT) * node.fromTile.y + CELL_MARGIN
						s = pygame.transform.rotate(self.lineArrow, -90)
						self._screen.blit(s, (pos_left, pos_top))
					if (xDiff < 0):
						pos_left = (CELL_MARGIN + CELL_WIDTH) * node.fromTile.x + CELL_MARGIN - CELL_WIDTH / 2
						pos_top = (CELL_MARGIN + CELL_HEIGHT) * node.fromTile.y + CELL_MARGIN
						s = pygame.transform.rotate(self.lineArrow, 90)
						self._screen.blit(s, (pos_left, pos_top))
					if (yDiff > 0):
						pos_left = (CELL_MARGIN + CELL_WIDTH) * node.fromTile.x + CELL_MARGIN
						pos_top = (CELL_MARGIN + CELL_HEIGHT) * node.fromTile.y + CELL_MARGIN + CELL_HEIGHT / 2
						s = pygame.transform.rotate(self.lineArrow, 180)
						self._screen.blit(s, (pos_left, pos_top))
					if (yDiff < 0):
						pos_left = (CELL_MARGIN + CELL_WIDTH) * node.fromTile.x + CELL_MARGIN
						pos_top = (CELL_MARGIN + CELL_HEIGHT) * node.fromTile.y + CELL_MARGIN - CELL_HEIGHT / 2
						s = self.lineArrow
						self._screen.blit(s, (pos_left, pos_top))



	def getCenter(self, tile):
		left, top = self.getTopLeft(tile)
		return (left + CELL_WIDTH / 2, top + CELL_HEIGHT / 2)

	def getTopLeft(self, tile):		
		pos_left = (CELL_MARGIN + CELL_WIDTH) * tile.x + CELL_MARGIN
		pos_top = (CELL_MARGIN + CELL_HEIGHT) * tile.y + CELL_MARGIN
		return (pos_left, pos_top)
					

	def save_images(self):		
		while True:
			if self._readyRender:
				#self.images.append(("{}\\{}.bmp".format(self.logDirectory, self._map.turn), pygame.image.tostring(self._screen, "RGB")))
				
				pygame.image.save(self._screen, "{}\\{}.png".format(self.logDirectory, self._map.turn))
				self._readyRender = False
			time.sleep(0.1)