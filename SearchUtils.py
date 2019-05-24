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
from DataModels import PathNode, TreeNode, Move
from Path import Path, PathMove
from test.test_float import INF
from ViewInfo import ViewInfo, PathColorer





class Counter(object):
	def __init__(self, value):
		self.value = value

	def add(self, value):
		self.value = self.value + value
		
def new_map_matrix(map, initialValueFunc):
	return [[initialValueFunc(x,y) for x in range(map.rows)] for y in range(map.cols)]
	

def where(list, filter):
	results = []
	for item in list:
		if filter(item):
			results.append(item)
	return results

def any(list, filter):
	for item in list:
		if filter(item):
			return True
	return False

def count(list, filter):
	count = 0
	for item in list:
		if filter(item):
			count += 1
	return count


def dest_breadth_first_target(map, goalList, targetArmy = 1, maxTime = 0.1, maxDepth = 20, negativeTiles = None, searchingPlayer = -2, dontEvacCities = False, dupeThreshold = 6, noNeutralCities = True, skipTiles = None, ignoreGoalArmy = False, noLog = False):
	'''
	GoalList can be a dict that maps from start tile to (startDist, goalTargetArmy)
	'''
	if (searchingPlayer == -2):
		searchingPlayer = map.player_index
	frontier = PriorityQueue()
	visited = [[{} for x in range(map.rows)] for y in range(map.cols)]
	globalVisitedSet = set()
	visitedSet = set()
	if isinstance(goalList, dict):
		for goal in goalList.keys():
			(startDist, goalTargetArmy) = goalList[goal]			
			if goal.mountain:
				#logging.info("BFS DEST SKIPPING MOUNTAIN {},{}".format(goal.x, goal.y))
				continue
			visitedSet.add((goal.x, goal.y))
			goalInc = 0
			if (goal.isCity or goal.isGeneral) and goal.player != -1:
				goalInc = -0.5
			startArmy = goal.army - 1 - goalTargetArmy
			if goal.player != searchingPlayer:
				startArmy = 0 - goal.army - 1 - goalTargetArmy
				goalInc *= -1
			if ignoreGoalArmy:
				startArmy = 0
			visited[goal.x][goal.y][startDist] = (startArmy, None)
			startVal = (startDist, 0 - startArmy)
			frontier.put((startVal, goal, startDist, startArmy, visitedSet, goalInc))
	else:
		for goal in goalList:
			if goal.mountain:
				#logging.info("BFS DEST SKIPPING MOUNTAIN {},{}".format(goal.x, goal.y))
				continue
			goalInc = 0
			visitedSet.add((goal.x, goal.y))
			startArmy = goal.army - 1
			if ignoreGoalArmy:
				startArmy = 0
			if (goal.isCity or goal.isGeneral) and goal.player != -1:
				goalInc = -0.5
			if goal.player != searchingPlayer:
				startArmy = 0 - goal.army - 1
				goalInc *= -1
			visited[goal.x][goal.y][0] = (startArmy, None)
			startVal = (0, 0 - startArmy)
			frontier.put((startVal, goal, 0, startArmy, visitedSet, goalInc))
	start = time.time()
	iter = 0
	foundGoal = False
	foundArmy = -1
	foundDist = -1
	endNode = None
	depthEvaluated = 0
	while not frontier.empty():
		iter += 1
		if (iter % 100 == 0 and time.time() - start > maxTime):
			logging.info("BFS DEST BREAKING")
			break
			
		(prioVals, current, dist, army, visitedSet, goalInc) = frontier.get()
		if dist > dupeThreshold and current in globalVisitedSet:
			continue
		globalVisitedSet.add(current)
		if army > targetArmy and army > 0 and army > foundArmy:
			foundGoal = True
			foundDist = dist
			foundArmy = army
			endNode = current
		if dist > depthEvaluated:
			depthEvaluated = dist
			targetArmy += goalInc
			if foundGoal:
				break
		if (dist <= maxDepth and not foundGoal):
			for next in current.moveable: #new spots to try
				nextSetEntry = (next.x, next.y)
				if (visitedSet != None and nextSetEntry in visitedSet) or (skipTiles != None and next in skipTiles):
					continue
					
				if (next.mountain or (next.isCity and noNeutralCities and next.player == -1) or (not next.discovered and next.isobstacle())):
					continue
				##TODO HACK, REMOVE AFTER FIXING GENERAL MOVEABILITY
				#if (next.isGeneral and next.player == searchingPlayer):
				#	continue
				inc = 0 if not (next.isCity or next.isGeneral) else dist / 2
				#new_cost = cost_so_far[current] + graph.cost(current, next)
				nextArmy = army - 1
				if (negativeTiles == None or next not in negativeTiles):
					if (searchingPlayer == next.player):
						if (next.isCity and dontEvacCities):								
							nextArmy += next.army // 2 + inc
						else:
							nextArmy += next.army + inc
					else:
						nextArmy -= (next.army + inc)
				newDist = dist + 1
				newVisitedSet = None
				if dist <= dupeThreshold and visitedSet != None:
					newVisitedSet = set(visitedSet)
					newVisitedSet.add(nextSetEntry)
				if newDist not in visited[next.x][next.y] or visited[next.x][next.y][newDist][0] < nextArmy:
					visited[next.x][next.y][newDist] = (nextArmy, current)
				frontier.put(((newDist, 0 - nextArmy), next, newDist, nextArmy, newVisitedSet, goalInc))
	if not noLog:
		logging.info("BFS DEST SEARCH ITERATIONS {}, DURATION: {}, DEPTH: {}, FOUNDDIST: {}".format(iter, time.time() - start, depthEvaluated, foundDist))
	if foundDist < 0:
		return None
		
	node = endNode
	dist = foundDist
	nodes = []
	army = foundArmy
	# logging.info(json.dumps(visited))
	# logging.info("PPRINT FULL")
	# logging.info(pformat(visited))

	while (node != None):
		# logging.info("ARMY {} NODE {},{}  DIST {}".format(army, node.x, node.y, dist))
		nodes.append((army, node))

		# logging.info(pformat(visited[node.x][node.y]))
		(army, node) = visited[node.x][node.y][dist]
		dist -= 1
	nodes.reverse()
	

	(startArmy, startNode) = nodes[0]

	pathObject = Path(foundArmy)
	pathObject.add_next(startNode)

	pathStart = PathNode(startNode, None, foundArmy, foundDist, -1, None)
	path = pathStart
	dist = foundDist
	for i, armyNode in enumerate(nodes[1:]):
		(curArmy, curNode) = armyNode
		if (curNode != None):
			# logging.info("curArmy {} NODE {},{}".format(curArmy, curNode.x, curNode.y))
			path = PathNode(curNode, path, curArmy, dist, -1, None) 
			pathObject.add_start(curNode)
			dist -= 1
	if (path.tile.army <= 1):
		logging.info("IS THIS THE INC BUG? OMG I THINK I FOUND IT!!!!!! Finds path where waiting 1 move for city increment is superior, but then we skip the 'waiting' move and just move the 2 army off the city instead of 3 army?")
		path = path.parent
		pathObject.made_move()
	# while (node != None):
	# 	army, node = visited[node.x][node.y][dist]
	# 	if (node != None):
	# 		dist -= 1
	# 		path = PathNode(node, path, army, dist, -1, None) 

	logging.info("DEST BFS FOUND KILLPATH OF LENGTH {} VALUE {}\n{}".format(pathObject.length, pathObject.value, pathObject.toString()))
	return pathObject



def _shortestPathHeur(goal, cur):
	return abs(goal.x - cur.x) + abs(goal.y - cur.y)




def a_star_kill(map, startTiles, goal, maxTime = 0.1, maxDepth = 20, restrictionEvalFuncs = None, ignoreStartTile = False):
	frontier = PriorityQueue()
	came_from = {}
	cost_so_far = {}
	if isinstance(startTiles, dict):
		for start in startTiles.keys():
			startDist = startTiles[start]			
			logging.info("a* enqueued start tile {},{}".format(start.x, start.y))
			startArmy = start.army
			if ignoreStartTile:
				startArmy = 0
			#if (start.player == map.player_index and start.isGeneral and map.turn > GENERAL_HALF_TURN):
			#	startArmy = start.army / 2
			cost_so_far[start] = (startDist, 0 - startArmy)	
			frontier.put((cost_so_far[start], start))
			came_from[start] = None
	else:
		for start in startTiles:
			logging.info("a* enqueued start tile {},{}".format(start.x, start.y))
			startArmy = start.army
			if ignoreStartTile:
				startArmy = 0
			#if (start.player == map.player_index and start.isGeneral and map.turn > GENERAL_HALF_TURN):
			#	startArmy = start.army / 2
			cost_so_far[start] = (0, 0 - startArmy)	
			frontier.put((cost_so_far[start], start))
			came_from[start] = None	
	start = time.time()
	iter = 0
	foundDist = -1
	foundArmy = -1
	foundGoal = False
	depthEvaluated = 0

	while not frontier.empty():
		iter += 1
		if (iter & 32 == 0 and time.time() - start > maxTime):
			logging.info("breaking early")
			break
		prio, current = frontier.get()
		x = current.x
		y = current.y				
		curCost = cost_so_far[current]
		dist = curCost[0]
		army = 0 - curCost[1]
						
		if dist > depthEvaluated:
			depthEvaluated = dist
		if current == goal:
			if army > 1 and army > foundArmy:
				foundDist = dist
				foundArmy = army
				foundGoal = True
				logging.info("A* found goal, breaking")
				break
			else: # skip paths that go through king, that wouldn't make sense
				#logging.info("a* path went through king")
				continue
		if (dist < maxDepth):
			for next in current.moveable: #new spots to try
				if (next.mountain or ((not next.discovered) and next.isobstacle())):
					#logging.info("a* mountain")
					continue
				if restrictionEvalFuncs != None:
					if current in restrictionEvalFuncs:
						if not restrictionEvalFuncs[current](next):
							logging.info("dangerous, vetod: {},{}".format(current.x, current.y))
							continue
						else:
							logging.info("safe: {},{}".format(current.x, current.y))

				inc = 0 if not ((next.isCity and next.player != -1) or next.isGeneral) else (dist + 1) / 2
					
				#new_cost = cost_so_far[current] + graph.cost(current, next)
				nextArmy = army - 1
				if (startTiles[0].player == next.player):
					nextArmy += next.army + inc
				else:
					nextArmy -= (next.army + inc)
				if (next.isCity and next.player == -1):
					nextArmy -= next.army * 2
				if (nextArmy <= 0):
					#logging.info("a* next army <= 0: {}".format(nextArmy))
					continue
				new_cost = (dist + 1, (0 - nextArmy))
				if next not in cost_so_far or new_cost < cost_so_far[next]:
					cost_so_far[next] = new_cost
					priority = (dist + 1 + _shortestPathHeur(goal, next), 0 - nextArmy)
					frontier.put((priority, next))
					#logging.info("a* enqueued next")
					came_from[next] = current
	logging.info("A* KILL SEARCH ITERATIONS {}, DURATION: {}, DEPTH: {}".format(iter, time.time() - start, depthEvaluated))
	if not goal in came_from:
		return None

	pathObject = Path(foundArmy)
	pathObject.add_next(goal)
	node = goal
	dist = foundDist
	while (came_from[node] != None):
		#logging.info("Node {},{}".format(node.x, node.y))
		node = came_from[node]
		dist -= 1
		pathObject.add_start(node)
	logging.info("A* FOUND KILLPATH OF LENGTH {} VALUE {}\n{}".format(pathObject.length, pathObject.value, pathObject.toString()))
	return pathObject


	#goalInc = 0
	#if (tile.isCity or tile.isGeneral) and tile.player != -1:
	#	goalInc = -0.5
	#startArmy = tile.army - 1
	#if tile.player != searchingPlayer:
	#	startArmy = 0 - tile.army - 1
	#	goalInc *= -1
	#if incrementBackward:
	#	goalInc *= -1
	#if ignoreStartTile:
	#	startArmy = 0
def breadth_first_dynamic(map, startTiles, goalFunc, maxTime = 0.2, maxDepth = 100, 
					   noNeutralCities = False, 
					   negativeTiles = None, 
					   skipTiles = None, 
					   searchingPlayer = -2, 
					   priorityFunc = None,
					   skipFunc = None,
					   ignoreStartTile = False,
					   incrementBackward = False,
					   preferNeutral = False):
	'''
	startTiles dict is (startPriorityObject, distance) = startTiles[tile]
	goalFunc is (currentTile, priorityObject) -> True or False
	priorityFunc is (nextTile, currentPriorityobject) -> nextPriorityObject

	# make sure to initialize the initial base values and account for first priorityObject being None.
	def default_priority_func(nextTile, currentPriorityObject):
		dist = -1
		negCityCount = negEnemyTileCount = negArmySum = x = y = 0
		if currentPriorityObject != None:
			(dist, negCityCount, negEnemyTileCount, negArmySum, x, y) = currentPriorityObject
		dist += 1
		if nextTile.isCity:
			negCityCount -= 1
		if nextTile.player != searchingPlayer and nextTile.player != -1:
			negEnemyTileCount -= 1
		if nextTile.player == searchingPlayer:
			negArmySum -= nextTile.army - 1
		else:
			negArmySum += nextTile.army + 1
		return (dist, negCityCount, negEnemyTileCount, negArmySum, nextTile.x, nextTile.y)
	'''	
	# make sure to initialize the initial base values and account for first priorityObject being None. Or initialize all your start values in the dict.
	def default_priority_func(nextTile, currentPriorityObject):
		(dist, negCityCount, negEnemyTileCount, negArmySum, x, y, goalIncrement) = currentPriorityObject
		dist += 1
		if nextTile.isCity:
			negCityCount -= 1
		if nextTile.player != searchingPlayer and (nextTile.player != -1 or (preferNeutral and nextTile.isCity == False)):
			negEnemyTileCount -= 1
			
		if (negativeTiles == None or next not in negativeTiles):
			if nextTile.player == searchingPlayer:
				negArmySum -= nextTile.army
			else:
				negArmySum += nextTile.army
		# always leaving 1 army behind. + because this is negative.
		negArmySum += 1
		# -= because we passed it in positive for our general and negative for enemy gen / cities
		negArmySum -= goalIncrement
		return (dist, negCityCount, negEnemyTileCount, negArmySum, nextTile.x, nextTile.y, goalIncrement)

	if searchingPlayer == -2:
		searchingPlayer = map.player_index
	if (priorityFunc == None):
		priorityFunc = default_priority_func
	frontier = PriorityQueue()
	visited = [[{} for x in range(map.rows)] for y in range(map.cols)]
	globalVisitedSet = set()
	if isinstance(startTiles, dict):
		for tile in startTiles.keys():
			(startPriorityObject, distance) = startTiles[tile]

			startVal = startPriorityObject
			frontier.put((startVal, distance, tile, None))
	else:
		for tile in startTiles:
			if priorityFunc != default_priority_func:
				raise AssertionError("yo you need to do the dictionary start if you're gonna pass a nonstandard priority func.")
			if tile.mountain:
				#logging.info("BFS DEST SKIPPING MOUNTAIN {},{}".format(goal.x, goal.y))
				continue
			dist = 0
			negCityCount = negEnemyTileCount = negArmySum = x = y = goalIncrement = 0
			
			if not ignoreStartTile and tile.isCity:
				negCityCount = -1
			if not ignoreStartTile and tile.player != searchingPlayer and tile.player != -1:
				negEnemyTileCount = -1
			if not ignoreStartTile and tile.player == searchingPlayer:
				negArmySum = 1 - tile.army
			else:
				negArmySum = tile.army + 1
			if not ignoreStartTile:
				if tile.player != -1 and tile.isCity or tile.isGeneral:
					goalIncrement = 0.5
					if tile.player != searchingPlayer:
						goalIncrement *= -1			

			startVal = (dist, negCityCount, negEnemyTileCount, negArmySum, tile.x, tile.y, goalIncrement)
			frontier.put((startVal, dist, tile, None))
	start = time.time()
	iter = 0
	foundGoal = False
	foundDist = 1000
	endNode = None
	depthEvaluated = 0
	foundVal = None
	while not frontier.empty():
		iter += 1
		if (iter % 1000 == 0 and time.time() - start > maxTime):
			logging.info("BFS-DYNAMIC BREAKING")
			break
			
		(prioVals, dist, current, parent) = frontier.get()
		if dist not in visited[current.x][current.y] or visited[current.x][current.y][dist][0] > prioVals:
			visited[current.x][current.y][dist] = (prioVals, parent)
		#TODO no globalVisitedSet
		if current in globalVisitedSet or (skipTiles != None and current in skipTiles):
			continue
		globalVisitedSet.add(current)
		if goalFunc(current, prioVals):
			foundGoal = True
			foundDist = dist
			foundVal = prioVals
			endNode = current
		if dist > depthEvaluated:
			depthEvaluated = dist
			if foundGoal:
				break
		if (dist <= maxDepth and not foundGoal):
			for next in current.moveable: #new spots to try
				if (next.mountain 
						or (noNeutralCities and next.player == -1 and next.isCity) 
						or (not next.discovered and next.isobstacle())):
					continue
				newDist = dist + 1
				nextVal = priorityFunc(next, prioVals)
				if (skipFunc != None and skipFunc(next, nextVal)):
					continue
				frontier.put((nextVal, newDist, next, current))

	logging.info("BFS-DYNAMIC ITERATIONS {}, DURATION: {}, DEPTH: {}".format(iter, time.time() - start, depthEvaluated))
	if foundDist >= 1000:
		return None
		
	tile = endNode
	dist = foundDist
	tileList = []
	# logging.info(json.dumps(visited))
	# logging.info("PPRINT FULL")
	# logging.info(pformat(visited))

	while (tile != None):
		# logging.info("ARMY {} NODE {},{}  DIST {}".format(army, node.x, node.y, dist))
		tileList.append(tile)

		# logging.info(pformat(visited[node.x][node.y]))
		(prioVal, tile) = visited[tile.x][tile.y][dist]
		dist -= 1
	pathObject = Path()
	for tile in reversed(tileList):
		if tile != None:
			# logging.info("curArmy {} NODE {},{}".format(curArmy, curNode.x, curNode.y))
			pathObject.add_next(tile)

	# while (node != None):
	# 	army, node = visited[node.x][node.y][dist]
	# 	if (node != None):
	# 		dist -= 1
	# 		path = PathNode(node, path, army, dist, -1, None)
	pathObject.calculate_value(searchingPlayer)
	logging.info("DYNAMIC BFS FOUND PATH LENGTH {} VALUE {}\n   {}".format(pathObject.length, pathObject.value, pathObject.toString()))
	return pathObject





def greedy_backpack_gather(map, startTiles, turns, targetArmy = None, valueFunc = None, baseCaseFunc = None,
					   negativeTiles = None,
					   skipTiles = None,
					   searchingPlayer = -2,
					   priorityFunc = None,
					   skipFunc = None,
					   ignoreStartTile = False,
					   incrementBackward = False,
					   preferNeutral = False,
					   viewInfo = None):
	'''
	startTiles is list of tiles that will be weighted with baseCaseFunc, OR dict (startPriorityObject, distance) = startTiles[tile]
	valueFunc is (currentTile, priorityObject) -> POSITIVELY weighted value object
	priorityFunc is (nextTile, currentPriorityobject) -> nextPriorityObject NEGATIVELY weighted
	'''
	# because something?
	turns += 1
	startTime = time.time()
	if negativeTiles != None:
		negativeTiles = negativeTiles.copy()
	else:
		negativeTiles = set()
	#q = PriorityQueue()

	#if isinstance(startTiles, dict):
	#	for tile in startTiles.keys():
	#		(startPriorityObject, distance) = startTiles[tile]

	#		startVal = startPriorityObject

	#		allowedDepth = turns - distance
	#		startTiles = {}
	#		startTiles[tile] = (startPriorityObject, 
				
	# TODO break ties by maximum distance from threat (ideally, gathers from behind our gen are better 
	#           than gathering stuff that may open up a better attack path in front of our gen)

	# TODO factor in cities, right now they're not even incrementing. need to factor them into the timing and calculate when they'll be moved.
	if searchingPlayer == -2:
		searchingPlayer = startTiles.keys()[0].player


	logging.info("Trying greedy-bfs-gather. Turns {}. Searching player {}".format(turns, searchingPlayer))
	if valueFunc == None:
		logging.info("Using default valueFunc")
		def default_value_func_max_gathered_per_turn(currentTile, priorityObject):
			(realDist, negNeutCount, negArmySum, dist, xSum, ySum) = priorityObject
			return (-1 * (negArmySum / (max(1, realDist))), 0-negNeutCount, 0-negArmySum, 0-dist, 0-xSum, 0-ySum)
		valueFunc = default_value_func_max_gathered_per_turn

		
	if priorityFunc == None:
		logging.info("Using default priorityFunc")
		def default_priority_func(nextTile, currentPriorityObject):
			(realDist, negNeutCount, negArmySum, dist, xSum, ySum) = currentPriorityObject
			negArmySum += 1
			if (nextTile not in negativeTiles):
				if (searchingPlayer == nextTile.player):
					negArmySum -= nextTile.army
				else:
					negArmySum += nextTile.army
			if nextTile.player != searchingPlayer and not (nextTile.player == -1 and nextTile.isCity):
				negNeutCount -= 1
				
			#logging.info("prio: nextTile {} got realDist {}, negNextArmy {}, negNeutCount {}, newDist {}, xSum {}, ySum {}".format(nextTile.toString(), realDist + 1, 0-nextArmy, negNeutCount, dist + 1, xSum + nextTile.x, ySum + nextTile.y))
			return (realDist + 1, negNeutCount, negArmySum, dist + 1, xSum + nextTile.x, ySum + nextTile.y)
		priorityFunc = default_priority_func
		

	if baseCaseFunc == None:
		logging.info("Using default baseCaseFunc")
		def default_base_case_func(tile, startingDist):
			startArmy = 0
			# we would like to not gather to an enemy tile without killing it, so must factor it into the path. army value is negative for priority, so use positive for enemy army.
			if tile.player != searchingPlayer:
				logging.info("tile {} was not owned by searchingPlayer {}, adding its army {}".format(tile.toString(), searchingPlayer, tile.army))
				startArmy = tile.army
			
			logging.info("tile {} got base case startArmy {}, startingDist {}".format(tile.toString(), startArmy, startingDist))
			return (0, 0, startArmy, startingDist, tile.x, tile.y)
		baseCaseFunc = default_base_case_func
		

	startTilesDict = {}
	if isinstance(startTiles, dict):
		startTilesDict = startTiles
		for tile in startTiles.keys():
			negativeTiles.add(tile)
	else:
		for tile in startTiles:
			# then use baseCaseFunc to initialize their priorities, and set initial distance to 0
			startTilesDict[tile] = (baseCaseFunc(tile, 0), 0)
			negativeTiles.add(tile)
	
	for tile in startTilesDict.keys():
		(startPriorityObject, distance) = startTilesDict[tile]
		logging.info("Including tile {},{} in startTiles at distance {}".format(tile.x, tile.y, distance))
		if viewInfo:
			viewInfo.bottomRightGridText[tile.x][tile.y] = distance

	startR = 100
	startG = 150
	startB = 200
	valuePerTurnPath = breadth_first_dynamic_max(map, startTilesDict, valueFunc, 0.1, turns, noNeutralCities=True,
						negativeTiles = negativeTiles, 
						skipTiles = skipTiles, 
						searchingPlayer = searchingPlayer, 
						priorityFunc = priorityFunc,
						skipFunc = skipFunc,
						ignoreStartTile = ignoreStartTile,
						incrementBackward = incrementBackward,
						preferNeutral = preferNeutral)
	
	if valuePerTurnPath == None:
		logging.info("Yo, no initial valuePerTurnPath??????? :(")
		return []
	treeNodeLookup = {}
	treeNodes = []
	itr = 0
	remainingTurns = turns
	while valuePerTurnPath != None:
		logging.info("Adding valuePerTurnPath (v/t {:.2f}): {}".format(valuePerTurnPath.value / valuePerTurnPath.length, valuePerTurnPath.toString()))
		#if viewInfo:
		#	newR = (startR + 50 * itr) % 255
		#	newG = (startG - 30 * itr) % 255
		#	newB = (startB + 25 * itr) % 255
		#	viewInfo.paths.appendleft(PathColorer(valuePerTurnPath.get_reversed(), newR, newG, newB, 255, 0, 200))

		remainingTurns = remainingTurns - valuePerTurnPath.length
		itr += 1
		# add the new path to startTiles, rinse, and repeat
		node = valuePerTurnPath.start
		# we need to factor in the distance that the last path was already at (say we're gathering to a threat, 
		# you can't keep adding gathers to the threat halfway point once you're gathering for as many turns as half the threat length
		(startPriorityObject, distance) = startTilesDict[node.tile]
		# TODO? May need to not continue with the previous paths priorityObjects and instead start fresh, as this may unfairly weight branches
		#       towards the initial max path, instead of the highest actual additional value
		curPrioObj = startPriorityObject
		addlDist = 1
		currentTreeNode = None
		
		if node.tile in treeNodeLookup:
			currentTreeNode = treeNodeLookup[node.tile]
		else:
			currentTreeNode = TreeNode(node.tile, None, distance)
			currentTreeNode.gatherTurns = 1
		runningValue = valuePerTurnPath.value
		currentTreeNode.value += runningValue
		runningValue -= node.tile.army
		treeNodeLookup[node.tile] = currentTreeNode
		negativeTiles.add(node.tile)
		# skipping because first tile is actually already on the path
		node = node.next
		# add the new path to startTiles and then search a new path
		while node != None:
			newDist = distance + addlDist
			nextPrioObj = baseCaseFunc(node.tile, newDist)
			startTilesDict[node.tile] = (nextPrioObj, newDist)
			negativeTiles.add(node.tile)
			logging.info("Including tile {},{} in startTilesDict at distance {}".format(node.tile.x, node.tile.y, newDist))
			if viewInfo:
				viewInfo.bottomRightGridText[node.tile.x][node.tile.y] = newDist
			nextTreeNode = TreeNode(node.tile, currentTreeNode.tile, newDist)
			nextTreeNode.value = runningValue
			nextTreeNode.gatherTurns = 1
			runningValue -= node.tile.army
			currentTreeNode.children.append(nextTreeNode)
			currentTreeNode = nextTreeNode
			treeNodeLookup[node.tile] = currentTreeNode
			addlDist += 1
			curPrioObj = nextPrioObj
			node = node.next
		
		logging.info("Searching for the next path with remainingTurns {}".format(remainingTurns))
		valuePerTurnPath = breadth_first_dynamic_max(map, startTilesDict, valueFunc, 0.1, remainingTurns, noNeutralCities=True,
							negativeTiles = negativeTiles, 
							skipTiles = skipTiles, 
							searchingPlayer = searchingPlayer, 
							priorityFunc = priorityFunc,
							skipFunc = skipFunc,
							ignoreStartTile = ignoreStartTile,
							incrementBackward = incrementBackward,
							preferNeutral = preferNeutral)
	

	logging.info("Concluded greedy-bfs-gather built from {} path segments. Duration: {:.2f}".format(itr, time.time() - startTime))
	return list(where(treeNodeLookup.values(), lambda treeNode: treeNode.fromTile == None))

def get_tree_move(gathers, priorityFunc, valueFunc):
	if len(gathers) == 0:
		logging.info("get_tree_move... len(gathers) == 0?")
		return None
	q = PriorityQueue()

	for gather in gathers:
		basePrio = priorityFunc(gather.tile, None)
		q.put((basePrio, gather))

	highestValue = None
	highestValueMove = None
	while q.qsize() > 0:
		(curPrio, curGather) = q.get()
		if len(curGather.children) == 0:
			# WE FOUND OUR FIRST MOVE!
			thisValue = valueFunc(curGather.tile, curPrio)
			if highestValue == None or thisValue > highestValue:
				highestValue = thisValue
				highestValueMove = Move(curGather.tile, curGather.fromTile)
				logging.info("new highestValueMove {}!".format(highestValueMove.toString()))
		for gather in curGather.children:
			nextPrio = priorityFunc(gather.tile, curPrio)
			q.put((nextPrio, gather))
	if highestValueMove == None:
		raise AssertionError("No highestValueMove found?")
	logging.info("highestValueMove in get_tree_move was {}!".format(highestValueMove.toString()))
	return highestValueMove


def breadth_first_dynamic_max(map, startTiles, valueFunc, maxTime = 0.2, maxDepth = 100, 
					   noNeutralCities = False, 
					   negativeTiles = None, 
					   skipTiles = None, 
					   searchingPlayer = -2, 
					   priorityFunc = None,
					   skipFunc = None,
					   ignoreStartTile = False,
					   incrementBackward = False,
					   preferNeutral = False,
					   useGlobalVisitedSet = True):
	'''
	startTiles dict is (startPriorityObject, distance) = startTiles[tile]
	goalFunc is (currentTile, priorityObject) -> True or False
	priorityFunc is (nextTile, currentPriorityobject) -> nextPriorityObject

	# make sure to initialize the initial base values and account for first priorityObject being None.
	def default_priority_func(nextTile, currentPriorityObject):
		dist = -1
		negCityCount = negEnemyTileCount = negArmySum = x = y = 0
		if currentPriorityObject != None:
			(dist, negCityCount, negEnemyTileCount, negArmySum, x, y) = currentPriorityObject
		dist += 1
		if nextTile.isCity:
			negCityCount -= 1
		if nextTile.player != searchingPlayer and nextTile.player != -1:
			negEnemyTileCount -= 1
		if nextTile.player == searchingPlayer:
			negArmySum -= nextTile.army - 1
		else:
			negArmySum += nextTile.army + 1
		return (dist, negCityCount, negEnemyTileCount, negArmySum, nextTile.x, nextTile.y)
	'''	
	# make sure to initialize the initial base values and account for first priorityObject being None. Or initialize all your start values in the dict.
	def default_priority_func(nextTile, currentPriorityObject):
		(dist, negCityCount, negEnemyTileCount, negArmySum, sumX, sumY, goalIncrement) = currentPriorityObject
		dist += 1
		if nextTile.isCity:
			negCityCount -= 1
		if nextTile.player != searchingPlayer and (nextTile.player != -1 or (preferNeutral and nextTile.isCity == False)):
			negEnemyTileCount -= 1
			
		if (negativeTiles == None or next not in negativeTiles):
			if nextTile.player == searchingPlayer:
				negArmySum -= nextTile.army
			else:
				negArmySum += nextTile.army
		# always leaving 1 army behind. + because this is negative.
		negArmySum += 1
		# -= because we passed it in positive for our general and negative for enemy gen / cities
		negArmySum -= goalIncrement
		return (dist, negCityCount, negEnemyTileCount, negArmySum, sumX + nextTile.x, sumY + nextTile.y, goalIncrement)

	if searchingPlayer == -2:
		searchingPlayer = map.player_index
	if (priorityFunc == None):
		priorityFunc = default_priority_func
	frontier = PriorityQueue()
	visited = [[{} for x in range(map.rows)] for y in range(map.cols)]
	globalVisitedSet = set()
	if isinstance(startTiles, dict):
		for tile in startTiles.keys():
			(startPriorityObject, distance) = startTiles[tile]

			startVal = startPriorityObject
			frontier.put((startVal, distance, tile, None))
	else:
		for tile in startTiles:
			if priorityFunc != default_priority_func:
				raise AssertionError("yo you need to do the dictionary start if you're gonna pass a nonstandard priority func.")
			if tile.mountain:
				#logging.info("BFS DEST SKIPPING MOUNTAIN {},{}".format(goal.x, goal.y))
				continue
			dist = 0
			negCityCount = negEnemyTileCount = negArmySum = x = y = goalIncrement = 0
			
			if not ignoreStartTile and tile.isCity:
				negCityCount = -1
			if not ignoreStartTile and tile.player != searchingPlayer and tile.player != -1:
				negEnemyTileCount = -1
			if not ignoreStartTile and tile.player == searchingPlayer:
				negArmySum = 1 - tile.army
			else:
				negArmySum = tile.army + 1
			if not ignoreStartTile:
				if tile.player != -1 and tile.isCity or tile.isGeneral:
					goalIncrement = 0.5
					if tile.player != searchingPlayer:
						goalIncrement *= -1			

			startVal = (dist, negCityCount, negEnemyTileCount, negArmySum, tile.x, tile.y, goalIncrement)
			frontier.put((startVal, dist, tile, None))
	start = time.time()
	iter = 0
	foundDist = 1000
	endNode = None
	depthEvaluated = 0
	maxValue = None
	while not frontier.empty():
		iter += 1
		if (iter % 1000 == 0 and time.time() - start > maxTime):
			logging.info("BFS-DYNAMIC-MAX BREAKING")
			break

		(prioVals, dist, current, parent) = frontier.get()
		if dist not in visited[current.x][current.y] or visited[current.x][current.y][dist][0] > prioVals:
			visited[current.x][current.y][dist] = (prioVals, parent)
		#TODO no globalVisitedSet
		#if current in globalVisitedSet or (skipTiles != None and current in skipTiles):
		if (useGlobalVisitedSet and current in globalVisitedSet) or (skipTiles != None and current in skipTiles):
			continue
		if useGlobalVisitedSet:
			globalVisitedSet.add(current)
		newValue = valueFunc(current, prioVals)
		if maxValue == None or newValue > maxValue:
			foundDist = dist
			maxValue = newValue
			endNode = current
		if dist > depthEvaluated:
			depthEvaluated = dist
		dist += 1
		if (dist < maxDepth):
			for next in current.moveable: #new spots to try
				if (next.mountain 
						or (noNeutralCities and next.player == -1 and next.isCity) 
						or (not next.discovered and next.isobstacle())):
					continue
				nextVal = priorityFunc(next, prioVals)
				if (skipFunc != None and skipFunc(next, nextVal)):
					continue
				frontier.put((nextVal, dist, next, current))

	logging.info("BFS-DYNAMIC-MAX ITERATIONS {}, DURATION: {:.2f}, DEPTH: {}".format(iter, time.time() - start, depthEvaluated))
	if foundDist >= 1000:
		return None
		
	tile = endNode
	dist = foundDist
	tileList = []
	# logging.info(json.dumps(visited))
	# logging.info("PPRINT FULL")
	# logging.info(pformat(visited))

	while (tile != None):
		# logging.info("ARMY {} NODE {},{}  DIST {}".format(army, node.x, node.y, dist))
		tileList.append(tile)

		# logging.info(pformat(visited[node.x][node.y]))
		(prioVal, tile) = visited[tile.x][tile.y][dist]
		dist -= 1
	pathObject = Path()
	for tile in reversed(tileList):
		if tile != None:
			# logging.info("curArmy {} NODE {},{}".format(curArmy, curNode.x, curNode.y))
			pathObject.add_next(tile)

	# while (node != None):
	# 	army, node = visited[node.x][node.y][dist]
	# 	if (node != None):
	# 		dist -= 1
	# 		path = PathNode(node, path, army, dist, -1, None)
	pathObject.calculate_value(searchingPlayer)
	if pathObject.length == 0:
		logging.info("BFS-DYNAMIC-MAX FOUND PATH LENGTH {} VALUE {}, returning NONE!\n   {}".format(pathObject.length, pathObject.value, pathObject.toString()))
		return None
	else:		
		logging.info("BFS-DYNAMIC-MAX FOUND PATH LENGTH {} VALUE {}\n   {}".format(pathObject.length, pathObject.value, pathObject.toString()))
	return pathObject





			#goalInc = 0
			#if (tile.isCity or tile.isGeneral) and tile.player != -1:
			#	goalInc = -0.5
			#startArmy = tile.army - 1
			#if tile.player != searchingPlayer:
			#	startArmy = 0 - tile.army - 1
			#	goalInc *= -1
			#if incrementBackward:
			#	goalInc *= -1
			#if ignoreStartTile:
			#	startArmy = 0
def bidirectional_breadth_first_dynamic(map, startTiles, goalFunc, maxTime = 0.2, maxDepth = 100, 
					   noNeutralCities = False, 
					   negativeTiles = None, 
					   skipTiles = None, 
					   searchingPlayer = -2, 
					   priorityFunc = None,
					   skipFunc = None,
					   ignoreStartTile = False,
					   incrementBackward = False,
					   preferNeutral = False):
	'''
	startTiles dict is (startPriorityObject, distance) = startTiles[tile]
	goalFunc is (currentTile, priorityObject) -> True or False
	priorityFunc is (nextTile, currentPriorityobject) -> nextPriorityObject

	# make sure to initialize the initial base values and account for first priorityObject being None.
	def default_priority_func(nextTile, currentPriorityObject):
		dist = -1
		negCityCount = negEnemyTileCount = negArmySum = x = y = 0
		if currentPriorityObject != None:
			(dist, negCityCount, negEnemyTileCount, negArmySum, x, y) = currentPriorityObject
		dist += 1
		if nextTile.isCity:
			negCityCount -= 1
		if nextTile.player != searchingPlayer and nextTile.player != -1:
			negEnemyTileCount -= 1
		if nextTile.player == searchingPlayer:
			negArmySum -= nextTile.army - 1
		else:
			negArmySum += nextTile.army + 1
		return (dist, negCityCount, negEnemyTileCount, negArmySum, nextTile.x, nextTile.y)
	'''	
	# make sure to initialize the initial base values and account for first priorityObject being None. Or initialize all your start values in the dict.
	def default_priority_func(nextTile, currentPriorityObject):
		(dist, negCityCount, negEnemyTileCount, negArmySum, x, y, goalIncrement) = currentPriorityObject
		dist += 1
		if nextTile.isCity:
			negCityCount -= 1
		if nextTile.player != searchingPlayer and (nextTile.player != -1 or (preferNeutral and nextTile.isCity == False)):
			negEnemyTileCount -= 1
			
		if (negativeTiles == None or next not in negativeTiles):
			if nextTile.player == searchingPlayer:
				negArmySum -= nextTile.army
			else:
				negArmySum += nextTile.army
		# always leaving 1 army behind. + because this is negative.
		negArmySum += 1
		# -= because we passed it in positive for our general and negative for enemy gen / cities
		negArmySum -= goalIncrement
		return (dist, negCityCount, negEnemyTileCount, negArmySum, nextTile.x, nextTile.y, goalIncrement)

	if searchingPlayer == -2:
		searchingPlayer = map.player_index
	if (priorityFunc == None):
		priorityFunc = default_priority_func
	frontier = PriorityQueue()
	visited = [[{} for x in range(map.rows)] for y in range(map.cols)]
	globalVisitedSet = set()
	if isinstance(startTiles, dict):
		for tile in startTiles.keys():
			(startPriorityObject, distance) = startTiles[tile]

			startVal = startPriorityObject
			frontier.put((startVal, distance, tile, None))
	else:
		for tile in startTiles:
			if priorityFunc != default_priority_func:
				raise AssertionError("yo you need to do the dictionary start if you're gonna pass a nonstandard priority func.")
			if tile.mountain:
				#logging.info("BFS DEST SKIPPING MOUNTAIN {},{}".format(goal.x, goal.y))
				continue
			dist = 0
			negCityCount = negEnemyTileCount = negArmySum = x = y = goalIncrement = 0
			
			if not ignoreStartTile and tile.isCity:
				negCityCount = -1
			if not ignoreStartTile and tile.player != searchingPlayer and tile.player != -1:
				negEnemyTileCount = -1
			if not ignoreStartTile and tile.player == searchingPlayer:
				negArmySum = 1 - tile.army
			else:
				negArmySum = tile.army + 1
			if not ignoreStartTile:
				if tile.player != -1 and tile.isCity or tile.isGeneral:
					goalIncrement = 0.5
					if tile.player != searchingPlayer:
						goalIncrement *= -1			

			startVal = (dist, negCityCount, negEnemyTileCount, negArmySum, tile.x, tile.y, goalIncrement)
			frontier.put((startVal, dist, tile, None))
	start = time.time()
	iter = 0
	foundGoal = False
	foundDist = 1000
	endNode = None
	depthEvaluated = 0
	foundVal = None
	while not frontier.empty():
		iter += 1
		if (iter % 1000 == 0 and time.time() - start > maxTime):
			logging.info("BFS-FIND BREAKING")
			break
			
		(prioVals, dist, current, parent) = frontier.get()
		if dist not in visited[current.x][current.y] or visited[current.x][current.y][dist][0] > prioVals:
			visited[current.x][current.y][dist] = (prioVals, parent)
		#TODO no globalVisitedSet
		if current in globalVisitedSet or (skipTiles != None and current in skipTiles):
			continue
		globalVisitedSet.add(current)
		if goalFunc(current, prioVals):
			foundGoal = True
			foundDist = dist
			foundVal = prioVals
			endNode = current
		if dist > depthEvaluated:
			depthEvaluated = dist
			if foundGoal:
				break
		if (dist <= maxDepth and not foundGoal):
			for next in current.moveable: #new spots to try
				if (next.mountain 
						or (noNeutralCities and next.player == -1 and next.isCity) 
						or (not next.discovered and next.isobstacle())):
					continue
				newDist = dist + 1
				nextVal = priorityFunc(next, prioVals)
				if (skipFunc != None and skipFunc(next, nextVal)):
					continue
				frontier.put((nextVal, newDist, next, current))

	logging.info("BFS-FIND ITERATIONS {}, DURATION: {:.2f}, DEPTH: {}".format(iter, time.time() - start, depthEvaluated))
	if foundDist >= 1000:
		return None
		
	tile = endNode
	dist = foundDist
	tileList = []
	# logging.info(json.dumps(visited))
	# logging.info("PPRINT FULL")
	# logging.info(pformat(visited))

	while (tile != None):
		# logging.info("ARMY {} NODE {},{}  DIST {}".format(army, node.x, node.y, dist))
		tileList.append(tile)

		# logging.info(pformat(visited[node.x][node.y]))
		(prioVal, tile) = visited[tile.x][tile.y][dist]
		dist -= 1
	pathObject = Path()
	for tile in reversed(tileList):
		if tile != None:
			# logging.info("curArmy {} NODE {},{}".format(curArmy, curNode.x, curNode.y))
			pathObject.add_next(tile)

	# while (node != None):
	# 	army, node = visited[node.x][node.y][dist]
	# 	if (node != None):
	# 		dist -= 1
	# 		path = PathNode(node, path, army, dist, -1, None)
	pathObject.calculate_value(searchingPlayer)
	logging.info("DYNAMIC BFS FOUND PATH LENGTH {} VALUE {}\n   {}".format(pathObject.length, pathObject.value, pathObject.toString()))
	return pathObject



def breadth_first_find_queue(map, startTiles, goalFunc, maxTime = 0.1, maxDepth = 20, 
							 noNeutralCities = False, 
							 negativeTiles = None, 
							 skipTiles = None, 
							 searchingPlayer = -2,
							 ignoreStartTile = False):
	'''
	goalFunc is goalFunc(current, army, dist)
	'''
	if searchingPlayer == -2:
		searchingPlayer = map.player_index
	frontier = deque()
	visited = [[{} for x in range(map.rows)] for y in range(map.cols)]
	globalVisitedSet = set()
	if isinstance(startTiles, dict):
		for tile in startTiles.keys():
			(startDist, startArmy) = startTiles[tile]			
			if tile.mountain:
				#logging.info("BFS DEST SKIPPING MOUNTAIN {},{}".format(goal.x, goal.y))
				continue
			tileInc = 0
			if (tile.isCity or tile.isGeneral):
				goalInc = -0.5
			startArmy = tile.army - 1
			if tile.player != searchingPlayer:
				startArmy = 0 - tile.army - 1
				goalInc = -1 * goalInc
			if ignoreStartTile:
				startArmy = 0
			visited[tile.x][tile.y][startDist] = (startArmy, None)
			frontier.appendleft((tile, startDist, startArmy, goalInc))
	else:
		for tile in startTiles:
			if tile.mountain:
				#logging.info("BFS DEST SKIPPING MOUNTAIN {},{}".format(goal.x, goal.y))
				continue
			goalInc = 0
			startArmy = tile.army - 1
			if tile.player != searchingPlayer:
				startArmy = 0 - tile.army - 1
			visited[tile.x][tile.y][0] = (startArmy, None)
			if (tile.isCity or tile.isGeneral):
				goalInc = 0.5
			if ignoreStartTile:
				startArmy = 0
			frontier.appendleft((tile, 0, startArmy, goalInc))
	start = time.time()
	iter = 0
	foundGoal = False
	foundArmy = -100000
	foundDist = 1000
	endNode = None
	depthEvaluated = 0
	while len(frontier) > 0:
		iter += 1
		if (iter % 1000 == 0 and time.time() - start > maxTime):
			logging.info("BFS-FIND BREAKING")
			break
			
		(current, dist, army, goalInc) = frontier.pop()
		if current in globalVisitedSet or (skipTiles != None and current in skipTiles):
			continue
		globalVisitedSet.add(current)
		if goalFunc(current, army, dist) and (dist < foundDist or (dist == foundDist and army > foundArmy)):
			foundGoal = True
			foundDist = dist
			foundArmy = army
			endNode = current
		if dist > depthEvaluated:
			depthEvaluated = dist
			if foundGoal:
				break
		if (dist <= maxDepth and not foundGoal):
			for next in current.moveable: #new spots to try
					
				if (next.mountain or (noNeutralCities and next.player == -1 and next.isCity) or (not next.discovered and next.isobstacle())):
					continue
				inc = 0 if not ((next.isCity and next.player != -1) or next.isGeneral) else dist / 2
				#new_cost = cost_so_far[current] + graph.cost(current, next)
				nextArmy = army - 1
				if (negativeTiles == None or next not in negativeTiles):
					if (searchingPlayer == next.player):
						nextArmy += next.army + inc
					else:
						nextArmy -= (next.army + inc)
				newDist = dist + 1
				if newDist not in visited[next.x][next.y] or visited[next.x][next.y][newDist][0] < nextArmy:
					visited[next.x][next.y][newDist] = (nextArmy, current)
				frontier.appendleft((next, newDist, nextArmy, goalInc))

	logging.info("BFS-FIND-QUEUE ITERATIONS {}, DURATION: {:.2f}, DEPTH: {}".format(iter, time.time() - start, depthEvaluated))
	if foundDist >= 1000:
		return None
		
	node = endNode
	dist = foundDist
	nodes = []
	army = foundArmy
	# logging.info(json.dumps(visited))
	# logging.info("PPRINT FULL")
	# logging.info(pformat(visited))

	while (node != None):
		# logging.info("ARMY {} NODE {},{}  DIST {}".format(army, node.x, node.y, dist))
		nodes.append((army, node))

		# logging.info(pformat(visited[node.x][node.y]))
		(army, node) = visited[node.x][node.y][dist]
		dist -= 1
	nodes.reverse()
	(startArmy, startNode) = nodes[0]
	pathObject = Path(foundArmy)
	pathObject.add_next(startNode)
	pathStart = PathNode(startNode, None, foundArmy, foundDist, -1, None)
	path = pathStart
	dist = foundDist
	for i, armyNode in enumerate(nodes[1:]):
		(curArmy, curNode) = armyNode
		if (curNode != None):
			# logging.info("curArmy {} NODE {},{}".format(curArmy, curNode.x, curNode.y))
			path = PathNode(curNode, path, curArmy, dist, -1, None) 
			pathObject.add_start(curNode)
			dist -= 1

	# while (node != None):
	# 	army, node = visited[node.x][node.y][dist]
	# 	if (node != None):
	# 		dist -= 1
	# 		path = PathNode(node, path, army, dist, -1, None) 

	logging.info("BFS-FIND-QUEUE found path OF LENGTH {} VALUE {}\n{}".format(pathObject.length, pathObject.value, pathObject.toString()))
	return pathObject






def breadth_first_foreach(map, startTiles, maxDepth, foreachFunc, negativeFunc = None, skipFunc = None, skipTiles = None, searchingPlayer = -2, noLog = False):
	if searchingPlayer == -2:
		searchingPlayer = map.player_index
	frontier = deque()
	globalVisited = [[False for x in range(map.rows)] for y in range(map.cols)]
	if skipTiles != None:
		for tile in skipTiles:
			globalVisited[tile.x][tile.y] = True

	for tile in startTiles:
		if tile.mountain:
			#logging.info("BFS DEST SKIPPING MOUNTAIN {},{}".format(goal.x, goal.y))
			continue
		frontier.appendleft((tile, 0))
	start = time.time()
	iter = 0
	depthEvaluated = 0
	while len(frontier) > 0:
		iter += 1
			
		(current, dist) = frontier.pop()
		if globalVisited[current.x][current.y]:
			continue
		globalVisited[current.x][current.y] = True
		if (negativeFunc == None or not negativeFunc(current)):
			foreachFunc(current)

		if dist > depthEvaluated:
			depthEvaluated = dist
		if (dist <= maxDepth):
			for next in current.moveable: #new spots to try					
				if (next.mountain or next.isobstacle() or (skipFunc != None and skipFunc(next))):
					continue
					
				newDist = dist + 1
				frontier.appendleft((next, newDist))
	if not noLog:
		logging.info("Completed breadth_first_foreach. startTiles[0] {},{}: ITERATIONS {}, DURATION {:.2f}, DEPTH {}".format(startTiles[0].x, startTiles[0].y, iter, time.time() - start, depthEvaluated))



def build_distance_map(map, startTiles):
	distanceMap = [[INF for x in range(map.rows)] for y in range(map.cols)]
		
	def bfs_dist_mapper(tile, army, dist):
		if dist < distanceMap[tile.x][tile.y]:
			distanceMap[tile.x][tile.y] = dist
		return False
			
	breadth_first_find_queue(map, startTiles, bfs_dist_mapper, 0.1, 250, noNeutralCities=True)
	return distanceMap


# Stolen from https://www.geeksforgeeks.org/0-1-knapsack-problem-dp-10/
# Python3 code for Dynamic Programming 
# based solution for 0-1 Knapsack problem 

# Prints the items which are put in a  
# knapsack of capacity W 
def solve_knapsack(items, capacity, weights, values):
	timeStart = time.time()
	n = len(items)
	K = [[0 for w in range(capacity + 1)] 
			for i in range(n + 1)] 
			  
	# Build table K[][] in bottom 
	# up manner 
	for i in range(n + 1): 
		for w in range(capacity + 1): 
			if i == 0 or w == 0: 
				K[i][w] = 0
			elif weights[i - 1] <= w: 
				K[i][w] = max(values[i - 1]  
				  + K[i - 1][w - weights[i - 1]], 
							   K[i - 1][w]) 
			else: 
				K[i][w] = K[i - 1][w]
	# stores the result of Knapsack 
	res = K[n][capacity] 
	logging.info("Value Found {}".format(res))
	includedItems = []
	w = capacity 
	for i in range(n, 0, -1): 
		if res <= 0: 
			break
		# either the result comes from the 
		# top (K[i-1][w]) or from (val[i-1] 
		# + K[i-1] [w-wt[i-1]]) as in Knapsack 
		# table. If it comes from the latter 
		# one/ it means the item is included. 
		if res == K[i - 1][w]: 
			continue
		else: 
			# This item is included. 
			logging.info("item at index {} with value {} and weight {} was included... adding it to output".format(i - 1, values[i-1], weights[i-1]))
			includedItems.append(items[i-1])
			  
			# Since this weight is included 
			# its value is deducted 
			res = res - values[i - 1] 
			w = w - weights[i - 1]
	logging.info("knapsack completed on {} items for capacity {} finding value {} in Duration {:.2f}".format(n, capacity, K[n][capacity], time.time() - timeStart))
	return includedItems