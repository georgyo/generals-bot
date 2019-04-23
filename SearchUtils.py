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
from DataModels import PathNode, stringPath


def dest_breadth_first_target(map, goalList, targetArmy = 1, maxTime = 0.1, maxDepth = 20, negativeTiles = None, searchingPlayer = -2, dontEvacCities = False, dupeThreshold = 6, noNeutralCities = True, skipTiles = None):
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
					
				if (next.mountain or (noNeutralCities and next.player == -1 and next.isCity) or (not next.discovered and next.isobstacle())):
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
		return (None, None)
		
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
	pathStart = PathNode(startNode, None, foundArmy, foundDist, -1, None)
	path = pathStart
	dist = foundDist
	for i, armyNode in enumerate(nodes[1:]):
		(curArmy, curNode) = armyNode
		if (curNode != None):
			# logging.info("curArmy {} NODE {},{}".format(curArmy, curNode.x, curNode.y))
			path = PathNode(curNode, path, curArmy, dist, -1, None) 
			dist -= 1
	if (path.tile.army <= 1):
		path = path.parent
	# while (node != None):
	# 	army, node = visited[node.x][node.y][dist]
	# 	if (node != None):
	# 		dist -= 1
	# 		path = PathNode(node, path, army, dist, -1, None) 

	logging.info("DEST BFS FOUND KILLPATH OF LENGTH {} VALUE {}\n{}".format(pathStart.turn, pathStart.value, stringPath(path)))
	return (pathStart, path)



def _shortestPathHeur(goal, cur):
	return abs(goal.x - cur.x) + abs(goal.y - cur.y)




def a_star_kill(map, startTiles, goal, maxTime = 0.1, maxDepth = 20, restrictionEvalFuncs = None):

			
	frontier = PriorityQueue()
	came_from = {}
	cost_so_far = {}
	if isinstance(startTiles, dict):
		for start in startTiles.keys():
			startDist = startTiles[start]			
			logging.info("a* enqueued start tile {},{}".format(start.x, start.y))
			startArmy = start.army
			#if (start.player == map.player_index and start.isGeneral and map.turn > GENERAL_HALF_TURN):
			#	startArmy = start.army / 2
			cost_so_far[start] = (startDist, 0 - startArmy)	
			frontier.put((cost_so_far[start], start))
			came_from[start] = None
	else:
		for start in startTiles:
			logging.info("a* enqueued start tile {},{}".format(start.x, start.y))
			startArmy = start.army
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
		return (None, None)
	pathStart = PathNode(goal, None, foundArmy, foundDist, -1, None)
	path = pathStart
	node = goal
	dist = foundDist
	while (came_from[node] != None):
		#logging.info("Node {},{}".format(node.x, node.y))
		node = came_from[node]
		dist -= 1
		path = PathNode(node, path, foundArmy, dist, -1, None) 
	logging.info("A* FOUND KILLPATH OF LENGTH {} VALUE {}\n{}".format(pathStart.turn, pathStart.value, stringPath(path)))
	return (pathStart, path)




#def breadth_first_find(map, startTiles, goalFunc, maxTime = 0.1, maxDepth = 20, noNeutralCities = False, negativeTiles = None, skipTiles = None, searchingPlayer = -2):
#	if searchingPlayer == -2:
#		searchingPlayer = startTiles[0].player
#	frontier = PriorityQueue()
#	visited = [[{} for x in range(map.rows)] for y in range(map.cols)]
#	globalVisitedSet = set()
#	if isinstance(startTiles, dict):
#		for tile in startTiles.keys():
#			(startDist, startArmy) = startTiles[tile]
#			if tile.mountain:
#				#logging.info("BFS DEST SKIPPING MOUNTAIN {},{}".format(goal.x, goal.y))
#				continue
#			goalInc = 0
#			if (tile.isCity or tile.isGeneral) and tile.player != -1:
#				goalInc = -0.5
#			startArmy = tile.army - 1
#			if tile.player != searchingPlayer:
#				startArmy = 0 - tile.army - 1
#				goalInc *= -1
#			visited[tile.x][tile.y][startDist] = (startArmy, None)
#			startVal = (startDist, 0 - startArmy)
#			frontier.put((startVal, tile, startDist, startArmy, goalInc))
#	else:
#		for tile in startTiles:
#			if tile.mountain:
#				#logging.info("BFS DEST SKIPPING MOUNTAIN {},{}".format(goal.x, goal.y))
#				continue
#			goalInc = 0
#			startArmy = tile.army - 1
#			if (tile.isCity or tile.isGeneral) and tile.player != -1:
#				goalInc = -0.5
#			if tile.player != searchingPlayer:
#				startArmy = 0 - tile.army - 1
#				goalInc *= -1
#			visited[tile.x][tile.y][0] = (startArmy, None)
#			startVal = (0, 0 - startArmy)
#			frontier.put((startVal, tile, 0, startArmy, goalInc))
#	start = time.time()
#	iter = 0
#	foundGoal = False
#	foundArmy = -100000
#	foundDist = 1000
#	endNode = None
#	depthEvaluated = 0
#	while not frontier.empty():
#		iter += 1
#		if (iter % 100 == 0 and time.time() - start > maxTime):
#			logging.info("BFS-FIND BREAKING")
#			break
			
#		(prioVals, current, dist, army, goalInc) = frontier.get()
#		if current in globalVisitedSet or (skipTiles != None and current in skipTiles):
#			continue
#		globalVisitedSet.add(current)
#		if goalFunc(current, army, dist) and (dist < foundDist or (dist == foundDist and army > foundArmy)):
#			foundGoal = True
#			foundDist = dist
#			foundArmy = army
#			endNode = current
#		if dist > depthEvaluated:
#			depthEvaluated = dist
#			if foundGoal:
#				break
#		if (dist <= maxDepth and not foundGoal):
#			for next in current.moveable: #new spots to try
					
#				if (next.mountain or (noNeutralCities and next.player == -1 and next.isCity) or (not next.discovered and next.isobstacle())):
#					continue
#				inc = 0 if not ((next.isCity and next.player != -1) or next.isGeneral) else dist / 2
#				#new_cost = cost_so_far[current] + graph.cost(current, next)
#				nextArmy = army - 1
#				if (negativeTiles == None or next not in negativeTiles):
#					if (searchingPlayer == next.player):
#						nextArmy += next.army + inc
#					else:
#						nextArmy -= (next.army + inc)
#				newDist = dist + 1
#				if newDist not in visited[next.x][next.y] or visited[next.x][next.y][newDist][0] < nextArmy:
#					visited[next.x][next.y][newDist] = (nextArmy, current)
#				frontier.put(((newDist, 0 - nextArmy), next, newDist, nextArmy, goalInc))

#	logging.info("BFS-FIND ITERATIONS {}, DURATION: {}, DEPTH: {}".format(iter, time.time() - start, depthEvaluated))
#	if foundDist >= 1000:
#		return (None, None)
		
#	node = endNode
#	dist = foundDist
#	nodes = []
#	army = foundArmy
#	# logging.info(json.dumps(visited))
#	# logging.info("PPRINT FULL")
#	# logging.info(pformat(visited))

#	while (node != None):
#		# logging.info("ARMY {} NODE {},{}  DIST {}".format(army, node.x, node.y, dist))
#		nodes.append((army, node))

#		# logging.info(pformat(visited[node.x][node.y]))
#		(army, node) = visited[node.x][node.y][dist]
#		dist -= 1
#	nodes.reverse()
#	(startArmy, startNode) = nodes[0]
#	pathStart = PathNode(startNode, None, foundArmy, foundDist, -1, None)
#	path = pathStart
#	dist = foundDist
#	for i, armyNode in enumerate(nodes[1:]):
#		(curArmy, curNode) = armyNode
#		if (curNode != None):
#			# logging.info("curArmy {} NODE {},{}".format(curArmy, curNode.x, curNode.y))
#			path = PathNode(curNode, path, curArmy, dist, -1, None) 
#			dist -= 1

#	# while (node != None):
#	# 	army, node = visited[node.x][node.y][dist]
#	# 	if (node != None):
#	# 		dist -= 1
#	# 		path = PathNode(node, path, army, dist, -1, None) 

#	logging.info("BFS-FIND found path OF LENGTH {} VALUE {}\n{}".format(pathStart.turn, pathStart.value, stringPath(path)))
#	return (pathStart, path)

def default_sort_func(current, army, dist, enemyTileCount, cityCount, armySum):
	#return (dist, 0 - army, 0 - enemyTileCount, current.x, current.y)
	return (dist, 0 - cityCount, 0 - enemyTileCount, 0 - armySum, current.x, current.y)

def breadth_first_find(map, startTiles, goalFunc, maxTime = 0.1, maxDepth = 20, noNeutralCities = False, negativeTiles = None, skipTiles = None, searchingPlayer = -2, sortFunc = None):
	if searchingPlayer == -2:
		searchingPlayer = startTiles[0].player
	if (sortFunc == None):
		sortFunc = default_sort_func
	frontier = PriorityQueue()
	visited = [[{} for x in range(map.rows)] for y in range(map.cols)]
	globalVisitedSet = set()
	if isinstance(startTiles, dict):
		for tile in startTiles.keys():
			(startDist, startArmy) = startTiles[tile]
			if tile.mountain:
				#logging.info("BFS DEST SKIPPING MOUNTAIN {},{}".format(goal.x, goal.y))
				continue
			goalInc = 0
			if (tile.isCity or tile.isGeneral) and tile.player != -1:
				goalInc = -0.5
			startArmy = tile.army - 1
			if tile.player != searchingPlayer:
				startArmy = 0 - tile.army - 1
				goalInc *= -1
			startVal = sortFunc(tile, startArmy, startDist, 0, 0, tile.army)
			visited[tile.x][tile.y][startDist] = (startVal, None)
			frontier.put((startVal, tile, startDist, startArmy, goalInc, 0, 0, tile.army))
	else:
		for tile in startTiles:
			if tile.mountain:
				#logging.info("BFS DEST SKIPPING MOUNTAIN {},{}".format(goal.x, goal.y))
				continue
			goalInc = 0
			startArmy = tile.army - 1
			if (tile.isCity or tile.isGeneral) and tile.player != -1:
				goalInc = -0.5
			if tile.player != searchingPlayer:
				startArmy = 0 - tile.army - 1
				goalInc *= -1
			startVal = sortFunc(tile, startArmy, 0, 0, 0, tile.army)
			visited[tile.x][tile.y][0] = (startVal, None)
			frontier.put((startVal, tile, 0, startArmy, goalInc, 0, 0, tile.army))
	start = time.time()
	iter = 0
	foundGoal = False
	foundArmy = -100000
	foundDist = 1000
	endNode = None
	depthEvaluated = 0
	while not frontier.empty():
		iter += 1
		if (iter % 100 == 0 and time.time() - start > maxTime):
			logging.info("BFS-FIND BREAKING")
			break
			
		(prioVals, current, dist, army, goalInc, enemyTileCount, cityCount, armySum) = frontier.get()
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
				nextCityCount = cityCount
				nextEnemyTileCount = enemyTileCount
				nextArmySum = armySum + next.army
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
				if (next.player != -1 and next.player != searchingPlayer):
					nextEnemyTileCount += 1
				if (next.isCity):
					nextCityCount += 1
				nextVal = sortFunc(next, nextArmy, newDist, nextEnemyTileCount, nextCityCount, nextArmySum)
				if newDist not in visited[next.x][next.y] or visited[next.x][next.y][newDist][0] > nextVal:
					visited[next.x][next.y][newDist] = (nextVal, current)
				frontier.put((nextVal, next, newDist, nextArmy, goalInc, nextEnemyTileCount, nextCityCount, nextArmySum))

	logging.info("BFS-FIND ITERATIONS {}, DURATION: {}, DEPTH: {}".format(iter, time.time() - start, depthEvaluated))
	if foundDist >= 1000:
		return (None, None)
		
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
	pathStart = PathNode(startNode, None, foundArmy, foundDist, -1, None)
	path = pathStart
	dist = foundDist
	for i, armyNode in enumerate(nodes[1:]):
		(curArmy, curNode) = armyNode
		if (curNode != None):
			# logging.info("curArmy {} NODE {},{}".format(curArmy, curNode.x, curNode.y))
			path = PathNode(curNode, path, curArmy, dist, -1, None) 
			dist -= 1

	# while (node != None):
	# 	army, node = visited[node.x][node.y][dist]
	# 	if (node != None):
	# 		dist -= 1
	# 		path = PathNode(node, path, army, dist, -1, None) 

	logging.info("BFS-FIND found path OF LENGTH {} VALUE {}\n{}".format(pathStart.turn, pathStart.value, stringPath(path)))
	return (pathStart, path)






def breadth_first_find_queue(map, startTiles, goalFunc, maxTime = 0.1, maxDepth = 20, noNeutralCities = False, negativeTiles = None, skipTiles = None, searchingPlayer = -2):
	if searchingPlayer == -2:
		searchingPlayer = startTiles[0].player
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
		if (iter % 100 == 0 and time.time() - start > maxTime):
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
		return (None, None)
		
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
	pathStart = PathNode(startNode, None, foundArmy, foundDist, -1, None)
	path = pathStart
	dist = foundDist
	for i, armyNode in enumerate(nodes[1:]):
		(curArmy, curNode) = armyNode
		if (curNode != None):
			# logging.info("curArmy {} NODE {},{}".format(curArmy, curNode.x, curNode.y))
			path = PathNode(curNode, path, curArmy, dist, -1, None) 
			dist -= 1

	# while (node != None):
	# 	army, node = visited[node.x][node.y][dist]
	# 	if (node != None):
	# 		dist -= 1
	# 		path = PathNode(node, path, army, dist, -1, None) 

	logging.info("BFS-FIND-QUEUE found path OF LENGTH {} VALUE {}\n{}".format(pathStart.turn, pathStart.value, stringPath(path)))
	return (pathStart, path)



