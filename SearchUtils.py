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
from DataModels import PathNode
from Path import Path, PathMove

def dest_breadth_first_target(map, goalList, targetArmy = 1, maxTime = 0.1, maxDepth = 20, negativeTiles = None, searchingPlayer = -2, dontEvacCities = False, dupeThreshold = 6, noNeutralCities = True, skipTiles = None, ignoreGoalArmy = False):
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

	logging.info("BFS-FIND ITERATIONS {}, DURATION: {}, DEPTH: {}".format(iter, time.time() - start, depthEvaluated))
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

	logging.info("BFS-FIND ITERATIONS {}, DURATION: {}, DEPTH: {}".format(iter, time.time() - start, depthEvaluated))
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




class Counter(object):
	def __init__(self, value):
		self.value = value

	def add(self, value):
		self.value = self.value + value


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

	logging.info("BFS-FIND-QUEUE ITERATIONS {}, DURATION: {}, DEPTH: {}".format(iter, time.time() - start, depthEvaluated))
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
		logging.info("Completed breadth_first_foreach. startTiles[0] {},{}: ITERATIONS {}, DURATION {}, DEPTH {}".format(startTiles[0].x, startTiles[0].y, iter, time.time() - start, depthEvaluated))




