'''
	Generals.io Automated Client - https://github.com/harrischristiansen/generals-bot
	Client Adopted from @toshima Generals Python Client - https://github.com/toshima/generalsio
'''				
import os, errno
import random
import sys
import traceback
import logging
import json
import threading
import time
from websocket import create_connection, WebSocketConnectionClosedException

from . import map

_ENDPOINT = "ws://botws.generals.io/socket.io/?EIO=3&transport=websocket"
_ENDPOINT_PUBLIC = "ws://ws.generals.io/socket.io/?EIO=3&transport=websocket"


# _BOT_KEY = None
#_BOT_KEY = "eklipzai"
#_BOT_KEY = "ekbot42"

class Generals(object):
	def __init__(self, userid, username, mode="1v1", gameid=None,
				 force_start=False, public_server=False):
		self.bot_key = "sd09fjd203i0ejwi"
		self._lock = threading.RLock()
		self.lastCommunicationTime = time.time()
		self.cursewords = { 'pussy', 'fuck', 'fk ', ' fk', 'cunt', 'bitch', 'ass', 'nigger', 'of shit', 'dick', 'cock', 'kill yourself', ' kys', 'kys ', ' fag', 'fag ', 'faggot', 'stupid' }
		_spawn(self._start_killswitch_timer)
		logging.debug("Creating connection")
		# try:
		self._ws = create_connection(_ENDPOINT if not public_server else _ENDPOINT_PUBLIC)
			
		# except:
		# 	#self._ws = create_connection(_ENDPOINT if not public_server else _ENDPOINT_PUBLIC)
		# 	pass
		logging.debug("Connection created.")
		self._gameid = None
		self.lastChatCommand = ""
		self.earlyLogs = []
		self.logFile = None
		self.chatLogFile = None
		self.username = username
		self.mode = mode
		self.writingFile = False
		self._start_data = {}


		if not public_server and "[Bot]" not in username:
			username = "[Bot] " + username
		if not public_server:
			self.bot_key = None



		self._send(["stars_and_rank", userid, self.bot_key])

		self._send(["set_username", userid, username, self.bot_key])
		
		if (username == None):
			raise ValueError("username empty")
		if (userid == None):
			raise ValueError("userid empty")
		logging.debug("Joining game, userid: " + userid)

		if mode == "private":
			force_start = True
			self._gameid = gameid # Set Game ID
			if gameid is None:
				raise ValueError("Gameid must be provided for private games")
			logging.debug("CUSTOM GAME JOIN {}".format(gameid))
			self._send(["join_private", gameid, userid, self.bot_key])
		elif mode == "1v1":
			self._send(["join_1v1", userid, self.bot_key])
		elif mode == "team":
			self._send(["join_team", userid, self.bot_key])
		elif mode == "ffa":
			self._send(["play", userid, self.bot_key])
		else:
			raise ValueError("Invalid mode")
				
		if (force_start):
			_spawn(self._send_forcestart)
		logging.debug("Starting heartbeat thread")
		_spawn(self._start_sending_heartbeat)

		self._seen_update = False
		self._move_id = 1
		self._stars = []
		self._map = []
		self._cities = []

	def send_chat(self, msg):
		if not self._seen_update:
			raise ValueError("Cannot chat before game starts")

		if len(msg) < 2:
			return

		self._send(["chat_message", self._start_data['chat_room'], msg, None, ""])

	def move(self, y1, x1, y2, x2, move_half=False):
		if not self._seen_update:
			raise ValueError("Cannot move before first map seen")

		cols = self._map.cols
		a = y1 * cols + x1
		b = y2 * cols + x2
		self._send(["attack", a, b, move_half, self._move_id])
		self._move_id += 1

	def get_updates(self):
		while True:
			try:
				msg = self._ws.recv()
				self.lastCommunicationTime = time.time()
			except WebSocketConnectionClosedException:
				break

			if not msg.strip():
				break

			# ignore heartbeats and connection acks
			if msg in {"3", "40"}:
				continue

			# remove numeric prefix
			while msg and msg[0].isdigit():
				msg = msg[1:]

			try:
				msg = json.loads(msg)
			except:
				exc_type, exc_value, exc_traceback = sys.exc_info()
				lines = traceback.format_exception(exc_type, exc_value, exc_traceback)
				logging.info(''.join('!! ' + line for line in lines))  # Log it or whatever here
				
			if not isinstance(msg, list):
				continue

			
			if msg[0] == "game_start":
				logging.info("Game info: {}".format(msg[1]))
				self._start_data = msg[1]
				print("logging????")
				# for handler in logging.root.handlers[:]:
				#     logging.root.removeHandler(handler)
				# logging.basicConfig(format='%(levelname)s:%(message)s', filename='H:\\GeneralsLogs\\' + self._start_data['replay_id'] + '.log', level=logging.DEBUG)
				self.logFile = "H:\\GeneralsLogs\\" + self.username + "-" + self.mode + "-" + self._start_data['replay_id'] + ".txt" 
				self.chatLogFile = "H:\\GeneralsLogs\\_chat\\" + self.username + "-" + self.mode + "-" + self._start_data['replay_id'] + ".txt" 

				os.makedirs("H:\\GeneralsLogs\\_chat", exist_ok=True)
				try:
					with open(self.logFile, "a+") as myfile:
						for log in self.earlyLogs:
							myfile.write(log)
						self.earlyLogs = None
				except:
					logging.info("!!!!!!!!!!\n!!!!!!!!!!!!!\n!!!!!!!!!!!!\n!!!!!!!!!!!!!!!!\ncouldn't write EARLY LOGS to file")					
			elif msg[0] == "game_update":
				yield self._make_update(msg[1])
			elif msg[0] in ["game_won", "game_lost"]:
				yield self._make_result(msg[0], msg[1])
				break
			elif msg[0] == "chat_message":
				chat_msg = msg[2]
				if "username" in chat_msg:
					logging.info("~~~\n~~~\nFrom %s: %s\n~~~\n~~~" % (chat_msg["username"], chat_msg["text"]))
					message = chat_msg["text"]
					name = chat_msg["username"]
					if name == "jkhvgulyft":
						for i in range(12):
							self.send_chat("jkhvgulyft doesn't deserve a voice")
					#elif name == "how fucking dare u":						
						#elif random.choice(range(5)) == 0:
						#	self.send_chat("hey how fucking dare u, are you remembering to play nice with the other children?")
					elif ("human" in message.lower() or " bot" in message.lower()):
						swore = False
						for curseword in self.cursewords:
							if curseword in message:
								swore = True
						if swore:
							self.send_chat("are you mad because you are struggling against a bot, or because you're going through your tough teenage years? Maybe try yoga or meditation bud")
					elif (message.lower().startswith("gg")):
							self.send_chat("Good game!")
					if self.writingFile or (not "[Bot]" in chat_msg["username"]):
						self.writingFile = True
						try:
							with open(self.chatLogFile, "a+") as myfile:
								myfile.write("\nFrom %s: %s" % (chat_msg["username"], chat_msg["text"]))
						except:
							logging.info("!!!!!!!!!!\n!!!!!!!!!!!!!\n!!!!!!!!!!!!\n!!!!!!!!!!!!!!!!\ncouldn't write chat message to file")

					if (chat_msg["text"].startswith("-")):
						self.lastChatCommand = chat_msg["text"]
				elif(" captured " in chat_msg["text"]):
					self._map.handle_player_capture(chat_msg["text"])
				else:
					logging.info("Message: %s" % chat_msg["text"])
					if self.writingFile or (not self.chatLogFile == None and not " surrendered" in chat_msg["text"] and not " left" in chat_msg["text"] and not " quit" in chat_msg["text"] and not " wins!" in chat_msg["text"]):
						self.writingFile = True
						try:
							with open(self.chatLogFile, "a+") as myfile:
								myfile.write("\nUnknown message: %s" % chat_msg["text"])
						except:
							logging.info("!!!!!!!!!!\n!!!!!!!!!!!!!\n!!!!!!!!!!!!\n!!!!!!!!!!!!!!!!\ncouldn't write unknown message to file")
			elif msg[0] == "error_user_id":
				logging.info("error_user_id, Already in game???")
				raise ValueError("Already in game")
			elif msg[0] == "server_down":
				logging.info("server_down, Server is down???")
				raise ValueError("Server is down")
			elif msg[0] == "server_restart":
				logging.info("server_restart, Server is restarting???")
				raise ValueError("Server is restarting")
			elif msg[0] == "error_set_username":
				logging.info("error_set_username, ???")
				None
			else:
				logging.info("Unknown message type: {}".format(msg))

	def close(self):
		with self._lock:
			self._ws.close()
		if (self.logFile == None):
			self.earlyLogs.append("\nClosed WebSocket")
		else:
			with open(self.logFile, "a+") as myfile:
				myfile.write("\nClosed WebSocket")

	def _make_update(self, data):
		if not self._seen_update:
			self._seen_update = True
			self._map = map.Map(self._start_data, data)
			return self._map

		return self._map.update(data)

	def _make_result(self, update, data):
		result = self._map.updateResult(update)
		self._terminate()
		return result

	def _start_killswitch_timer(self):
		while time.time() - self.lastCommunicationTime < 60:
			time.sleep(10)
		os._exit(2) # End Program


	def _terminate(self):		
		logging.info("\n\n        IN TERMINATE {}   \n\n".format(self._start_data['replay_id']))
		with self._lock:
			#self._send(["leave_game"])
			#time.sleep(1)
			self.close()

	def _send_forcestart(self):
		time.sleep(3)
		while 'replay_id' not in self._start_data:
			self._send(["set_force_start", self._gameid, True])
			logging.info("Sent force_start")
			time.sleep(10)

	def _start_sending_heartbeat(self):
		while True:
			try:
				with self._lock:
					self._ws.send("2")
				
				if (self.logFile == None):
					self.earlyLogs.append("\n2")
				else:
					with open(self.logFile, "a+") as myfile:
						myfile.write("\n2")
			except WebSocketConnectionClosedException:
				break
			time.sleep(10)

	def _send(self, msg):
		try:
			toSend = "42" + json.dumps(msg)
			with self._lock:
				self._ws.send(toSend)
			
			if (self.logFile == None):
				self.earlyLogs.append("\n" + toSend)
			else:
				with open(self.logFile, "a+") as myfile:
					myfile.write("\n" + toSend)
		except WebSocketConnectionClosedException:
			pass


def _spawn(f):
	t = threading.Thread(target=f)
	t.daemon = True
	t.start()
