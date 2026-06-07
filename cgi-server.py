#!/usr/bin/env python3

import os
import sys
import traceback
import webbrowser
from html import escape
from http.server import CGIHTTPRequestHandler
from http.server import HTTPServer
from http.server import SimpleHTTPRequestHandler

try:
	import config
except ImportError:
	config = None

def get_conf_key(key, default):
    return os.getenv(key) or (getattr(config, key, None) if config else None) or default

base = os.path.dirname(os.path.abspath(__file__))
# dir containing .mdx/.mdd dictionary files (env var to override, then config.py, then default to "dictionaries" subdir)
dict_dir = get_conf_key("DICT_DIR", os.path.join(base, "dictionaries"))

# dir used to temporarily extract .mdd resources
static_dir = get_conf_key("MDICT_TEMP_ASSETS_DIR", os.path.join(base, ".mdict_temp_assets"))

server_port = int(get_conf_key("SERVER_PORT", 8808))
server_bind_ip = get_conf_key("SERVER_IP", "127.0.0.1")

class DebugRequestHandler(CGIHTTPRequestHandler):
	# Configurable static root (env var to override)
	def do_GET(self) -> None:
		path = self.path.split("?", 1)[0].rstrip("/")

		if path.lower().endswith(".py"):
			super().do_GET()
		else:
			# Static asset from custom root
			self.serve_static()

	def translate_path(self, path):
		"""Default behaviour for CGI script resolution; reroot into static_dir only while
		serving a static asset.
		"""
		if not getattr(self, "_serving_static", False):
			return super().translate_path(path)
		rel = path.split("?", 1)[0].split("#", 1)[0]
		for prefix in self.cgi_directories:  # e.g. "/cgi-bin"
			if rel == prefix or rel.startswith(prefix + "/"):
				rel = rel[len(prefix):]
				break
		original_dir = self.directory
		try:
			self.directory = static_dir
			return SimpleHTTPRequestHandler.translate_path(self, rel)
		finally:
			self.directory = original_dir

	def serve_static(self):
		"""Static serving from static_dir, bypassing CGIHTTPRequestHandler.send_head's
		is_cgi() check (which would otherwise try to *execute* an asset sitting directly
		under /cgi-bin, e.g. /cgi-bin/style.css). The flag makes translate_path reroot
		into static_dir for the duration."""
		self._serving_static = True
		try:
			f = SimpleHTTPRequestHandler.send_head(self)
			if f:
				try:
					self.copyfile(f, self.wfile)
				finally:
					f.close()
		finally:
			self._serving_static = False

	def do_POST(self) -> None:
		super().do_POST()


	def run_cgi(self):
		os.environ["DICT_DIR"] = dict_dir
		os.environ["MDICT_TEMP_ASSETS_DIR"] = static_dir
		super().run_cgi()


if __name__ == '__main__':
	print(f"DICT_DIR: {dict_dir}")
	print(f"MDICT_TEMP_ASSETS_DIR: {static_dir}")
	server_address = (server_bind_ip, server_port)
	webbrowser.open(f'http://{server_bind_ip}:{server_port}/cgi-bin/mdict_cgi.py')
	server = HTTPServer(server_address, DebugRequestHandler)
	print(f'Starting CGI server on http://{server_bind_ip}:{server_port}/cgi-bin/mdict_cgi.py')
	server.serve_forever()
