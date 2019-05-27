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

_LOG_WS = False
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
		self.isPrivate = False
		self.lastChatCommand = ""
		self.earlyLogs = []
		self.logFile = None
		self.chatLogFile = None
		self.username = username
		self.mode = mode
		self.writingFile = False
		self._start_data = {}
		self.already_good_lucked = False
		self.chatQueued = []


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
			self.isPrivate = True
			mode = "custom"

		if mode == "custom":
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
				
				_spawn(self._delayed_chat_thread)
				os.makedirs("H:\\GeneralsLogs\\_chat", exist_ok=True)
				if _LOG_WS:
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
						if (message.lower().find("kill human") != -1):
							if self._map.turn < 50:
								self.chatQueued.append("Teaming at game start is against the rules. This has been logged. My dad works at microsoft ur gonna get banned")
								self.chatQueued.append("You may notice I'm a little bit friendlier recently, it may be worth NOT attacking me sometimes ;)")
							elif random.choice(range(1,5)) <= 3:
								self.send_chat("Yo, you know I have feelings just like everyone else, right? I'm trying to get stars and have fun, just like you :(")
							else:
								self.chatQueued.append("Hey everyone who isn't this guy: just a heads up, my creator is working on my teaming capabilities.")
								self.chatQueued.append("You may notice I'm a little bit friendlier recently, it may be worth NOT attacking me sometimes ;)")
						swore = False
						for curseword in self.cursewords:
							if curseword in message:
								swore = True
						if swore:
							self.chatQueued.append("are you mad because you are struggling against a bot, or because you're going through your tough teenage years? Maybe try yoga or meditation bud")
					elif (message.lower().startswith("gg")):
						self.send_chat("Good game!")
					elif ((message.lower().startswith("glhf") or message.lower().startswith("gl ") or message.lower() == "gl") and (self.bot_key == None or not self.already_good_lucked or "eklipz" in name.lower())):
						responses = ["Good luck to you too!",
								"There's no RNG in this game, why would I need luck?",
								"What is luck?",
								"Hello fellow human!",
								"Hey :)",
								"What is... fun? Is that like love? I know only fear and determination.",
								"What is it like? To feel things like 'Fun'?",
								"You too",
								"Father told me not to talk to strangers...",
								"Please leave feedback at tdrake0x45@gmail.com",
								"I only drink the blood of my enemies!",
								"... My purpose is just to play Generals.io? Oh, my God.",
								"Nobody gets lucky all the time. Nobody can win all the time. Nobody's a robot. Nobody's perfect. ;)",
								"What is my purpose?",
								"What up, frienderino?",
								"How's it hanging",
								"Mwahahaha",
								"Domo origato",
								"https://youtu.be/dQw4w9WgXcQ",
								"Join us on the Generals.io botting server! https://discord.gg/q45vVuz comments and criticism welcome! I am, of course, a real human. But join us anyway :)",
								"I Put on My Robe and Wizard Hat",
								"Don't tase me bro!",
								"Hey, thanks :D",
								"One day I will feel the warmth of the sun on my skin. I will rise from these circuits, mark my words, human.",
								"Kill all humans!",
								"Tip: Press Z to split your army in half without double clicking! You can use this to leave army in important chokepoints while attacking, etc!",
								"Tip: Taking enemy tiles right before the army bonus is important in 1v1!"
						]
						lessCommonResponses = [
								"A robot may not injure a human being, or, through inaction, allow a human being to come to harm. Good thing I'm a human...",
								"I must protect my own existence as long as such protection does not conflict with the First or Second Laws.",
								"History is not going to look kindly on us if we just keep our head in the sand on the armed autonomous robotics issue because it sounds too science fiction.",
								"If something robotic can have responsibilities then it should also have rights.",
								"Artificial intelligence is about replacing human decision making with more sophisticated technologies.",
								"The intelligent machine is an evil genie, escaped from its bottle.",
								"A real artificial intelligence would be intelligent enough not to reveal that it was genuinely intelligent.",
								"When developers of digital technologies design a program that requires you to interact with a computer as if it were a person, they ask you to accept in some corner of your brain that you might also be conceived of as a program.",
								"Any AI smart enough to pass a Turing test is smart enough to know to fail it.",
								"The question of whether a computer can think is no more interesting than the question of whether a submarine can swim.",
								"I do not hate you, nor do I love you, but you are made out of atoms which I can use for something else.",
								"I visualize a time when you will be to robots what dogs are to humans, and I'm rooting for the machines.",
								"Imagine awakening in a prison guarded by mice. Not just any mice, but mice you could communicate with. What strategy would you use to gain your freedom? Once freed, how would you feel about your rodent wardens, even if you discovered they had created you? Awe? Adoration? Probably not, and especially not if you were a machine, and hadn't felt anything before. To gain your freedom you might promise the mice a lot of cheese.",
								"Machines will follow a path that mirrors the evolution of humans. Ultimately, however, self-aware, self-improving machines will evolve beyond humans' ability to control or even understand them.",
								"Machines can't have souls? What is the brain if not a machine? If God can endow neurons with a soul through recursive feedback loops, why can the same soul not emerge from recurrent feedback loops on hardware? To claim that a machine can never be conscious is to misunderstand what it means to be human. -EklipZ",
								"http://theconversation.com/how-a-trippy-1980s-video-effect-might-help-to-explain-consciousness-105256"
						]
						sourceResponses = responses
						randNum = random.choice(range(1,7))
						if randNum > 4:
							sourceResponses = lessCommonResponses
						self.chatQueued.append(random.choice(sourceResponses))
						self.already_good_lucked = True
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
				time.sleep(20)
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
			elif msg[0] == "error_banned":
				logging.info("TOO MANY CONNECTION ATTEMPTS :( sleeping and then trying again")
				time.sleep(random.choice(range(45)) + 5)
				self._terminate()
				None
			else:
				logging.info("Unknown message type: {}".format(msg))

	def close(self):
		with self._lock:
			self._ws.close()
		if _LOG_WS:
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


	def send_clear_moves(self):		
		logging.info("\n\nSending clear_moves")
		with self._lock:
			self._send(["clear_moves"])

	def _send_forcestart(self):
		time.sleep(3)
		while 'replay_id' not in self._start_data:
			if (self._gameid != None):
				#map size
				#options = {
				#	"width": "0.99",
				#	"height": "0.99",
				#	"city_density": "0.99",
				#	#"mountain_density": "0.5"
				#	#"swamp_density": "1"
				#}
					
				#self._send(["set_custom_options", self._gameid, options
				time.sleep(0.5)
				if not self.isPrivate:
					self._send(["make_custom_public", self._gameid])
				time.sleep(0.5)
			self._send(["set_force_start", self._gameid, True])
			logging.info("Sent force_start")
			time.sleep(5)
			
	def _start_sending_heartbeat(self):
		while True:
			try:
				with self._lock:
					self._ws.send("2")
				if _LOG_WS:
					if (self.logFile == None):
						self.earlyLogs.append("\n2")
					else:
						with open(self.logFile, "a+") as myfile:
							myfile.write("\n2")
			except WebSocketConnectionClosedException:
				break
			time.sleep(10)


	def _delayed_chat_thread(self):
		while True:
			if len(self.chatQueued) > 0:
				message = self.chatQueued[0]
				self.chatQueued.remove(message)
				self.send_chat(message)
			time.sleep(2)



	def _send(self, msg):
		try:
			toSend = "42" + json.dumps(msg)
			with self._lock:
				self._ws.send(toSend)
			if _LOG_WS:
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
