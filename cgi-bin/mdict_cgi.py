#!/opt/homebrew/bin/python3
import logging
import os
import posixpath
import re
import subprocess
import sys
import unicodedata

# zlib compression is used for engine version >=2.0
import zlib
from io import BytesIO
from os import extsep
from os.path import dirname, isfile, join, splitext
from pathlib import Path
from struct import Struct, pack, unpack
from urllib.parse import parse_qs, quote

from pureSalsa20 import Salsa20
from ripemd128 import ripemd128

# LZO compression is used for engine version < 2.0
try:
	import lzo
except ImportError:
	lzo = None

# xxhash is used for engine version >= 3.0
try:
	import xxhash
except ImportError:
	xxhash = None

__all__ = ["MDD", "MDX"]

log = logging.getLogger(__name__)

DICT_DIR = os.getenv("DICT_DIR") or "dictionaries"

if not Path(DICT_DIR).expanduser().exists():
	print("Content-type: text/html\n")
	print(f"""<h3 style='color:red'>Dictionary directory {DICT_DIR} does not exist!</h3>
    		\n<p>Please modify the default path in <code>config.py<code> or set the environment variable <tt>DICT_DIR</tt> 
      to a valid directory path containing your .mdx/.mdd files.</p>
      Or pass the env var from command line:<br>
      <pre>DICT_DIR=/path/to/dict/dir python3 cgi-server.py</pre>
      """)
	exit(1)

# Static-asset root: the web server serves this dir for paths relative to the CGI URL,
# so a relative ref like "img/x.png" in an entry resolves to ASSET_ROOT/img/x.png.
ASSET_ROOT = Path(os.getenv("MDICT_TEMP_ASSETS_DIR") or Path.home() / ".mdict").expanduser()

if not ASSET_ROOT.exists():
	sys.stderr.write(f"Creating temporary asset directory {ASSET_ROOT} for extracted .mdd resources...")
	ASSET_ROOT.mkdir(parents=True, exist_ok=True)

# Resource references to extract from rendered entries (and, transitively, from CSS).]\
_RE_HTML_REF = re.compile(r"""(?:src|href|xlink:href|poster)\s*=\s*["']([^"']+)["']""", re.I)
_RE_CSS_URL = re.compile(r"""url\(\s*["']?([^"')]+?)["']?\s*\)""", re.I)
_RE_CSS_IMPORT = re.compile(r"""@import\s+(?:url\()?\s*["']([^"']+)["']""", re.I)
# A ref is non-local if it has a scheme (http:, data:, sound:, ...), is protocol-relative
# (//), or a pure fragment (#). A server-absolute "/foo" IS treated as local: fixDefi
# rewrites it to relative, and extract_assets normalizes the leading slash away.
_RE_NONLOCAL = re.compile(r"[a-zA-Z][\w+.\-]*:|//|#")
# server-absolute resource ref: src/href="/foo" (but not protocol-relative "//host")
_RE_ABS_REF = re.compile(r"""((?:src|href)=)(["'])/(?!/)""", re.I)

# Audio: play in-page instead of navigating to the browser's HTML5 player.
_AUDIO_ONCLICK = "new Audio(this.href).play(); return false;"
_RE_AUDIO_TAG = re.compile(r"<audio\b[^>]*>(.*?)</audio>", re.I | re.S)
_RE_AUDIO_SRC = re.compile(r"""\bsrc\s*=\s*["']([^"']+)["']""", re.I)
# opening <a ... href="sound://X" ...> tag (inner text + </a> left untouched)
_RE_SOUND_ANCHOR = re.compile(r"""<a\b([^>]*?)href=(["'])sound://([^"']*)\2([^>]*)>""", re.I)


# start inline of mdict_utils/base/lzo.py


class FlexBuffer():

	def __init__(self):

		self.blockSize = None
		self.c = None
		self.l = None
		self.buf = None

	def require(self, n):

		r = self.c - self.l + n
		if r > 0:
			self.l += self.blockSize * ((r + self.blockSize - 1) // self.blockSize)
			# tmp = bytearray(self.l)
			# for i in len(self.buf):
			#    tmp[i] = self.buf[i]
			# self.buf = tmp
			self.buf.extend(bytearray(self.l - len(self.buf)))
		self.c = self.c + n
		return self.buf

	def alloc(self, initSize, blockSize):

		if blockSize:
			sz = blockSize
		else:
			sz = 4096
		self.blockSize = self.roundUp(sz)
		self.c = 0
		self.l = self.roundUp(initSize) | 0
		self.l += self.blockSize - (self.l % self.blockSize)
		self.buf = bytearray(self.l)
		return self.buf

	def roundUp(self, n):

		r = n % 4
		if r == 0:
			return n
		else:
			return n + 4 - r

	def reset(self):

		self.c = 0
		self.l = len(self.buf)

	def pack(self, size):

		return self.buf[0:size]


def _decompress(inBuf, outBuf):
	c_top_loop = 1
	c_first_literal_run = 2
	c_match = 3
	c_copy_match = 4
	c_match_done = 5
	c_match_next = 6

	out = outBuf.buf
	op = 0
	ip = 0
	t = inBuf[ip]
	state = c_top_loop
	m_pos = 0
	ip_end = len(inBuf)

	if t > 17:
		ip = ip + 1
		t = t - 17
		if t < 4:
			state = c_match_next
		else:
			out = outBuf.require(t)
			while True:
				out[op] = inBuf[ip]
				op = op + 1
				ip = ip + 1
				t = t - 1
				if not t > 0: break
			state = c_first_literal_run

	while True:
		if_block = False

		##
		if state == c_top_loop:
			t = inBuf[ip]
			ip = ip + 1
			if t >= 16:
				state = c_match
				continue
			if t == 0:
				while inBuf[ip] == 0:
					t = t + 255
					ip = ip + 1
				t = t + 15 + inBuf[ip]
				ip = ip + 1

			t = t + 3
			out = outBuf.require(t)
			while True:
				out[op] = inBuf[ip]
				op = op + 1
				ip = ip + 1
				t = t - 1
				if not t > 0: break
			# emulate c switch
			state = c_first_literal_run

		##
		if state == c_first_literal_run:
			t = inBuf[ip]
			ip = ip + 1
			if t >= 16:
				state = c_match
				continue
			m_pos = op - 0x801 - (t >> 2) - (inBuf[ip] << 2)
			ip = ip + 1
			out = outBuf.require(3)
			out[op] = out[m_pos]
			op = op + 1
			m_pos = m_pos + 1
			out[op] = out[m_pos]
			op = op + 1
			m_pos = m_pos + 1
			out[op] = out[m_pos]
			op = op + 1

			state = c_match_done
			continue

		##
		if state == c_match:
			if t >= 64:
				m_pos = op - 1 - ((t >> 2) & 7) - (inBuf[ip] << 3)
				ip = ip + 1
				t = (t >> 5) - 1
				state = c_copy_match
				continue
			elif t >= 32:
				t = t & 31
				if t == 0:
					while inBuf[ip] == 0:
						t = t + 255
						ip = ip + 1
					t = t + 31 + inBuf[ip]
					ip = ip + 1
				m_pos = op - 1 - ((inBuf[ip] + (inBuf[ip + 1] << 8)) >> 2)
				ip = ip + 2
			elif t >= 16:
				m_pos = op - ((t & 8) << 11)
				t = t & 7
				if t == 0:
					while inBuf[ip] == 0:
						t = t + 255
						ip = ip + 1
					t = t + 7 + inBuf[ip]
					ip = ip + 1
				m_pos = m_pos - ((inBuf[ip] + (inBuf[ip + 1] << 8)) >> 2)
				ip = ip + 2
				if m_pos == op:
					break
				m_pos = m_pos - 0x4000
			else:
				m_pos = op - 1 - (t >> 2) - (inBuf[ip] << 2);
				ip = ip + 1
				out = outBuf.require(2)
				out[op] = out[m_pos]
				op = op + 1
				m_pos = m_pos + 1
				out[op] = out[m_pos]
				op = op + 1
				state = c_match_done
				continue

			if t >= 6 and (op - m_pos) >= 4:
				if_block = True
				t += 2
				out = outBuf.require(t)
				while True:
					out[op] = out[m_pos]
					op += 1
					m_pos += 1
					t -= 1
					if not t > 0: break
			# emulate c switch
			state = c_copy_match

		##
		if state == c_copy_match:
			if not if_block:
				t += 2
				out = outBuf.require(t)
				while True:
					out[op] = out[m_pos]
					op += 1
					m_pos += 1
					t -= 1
					if not t > 0: break
			# emulating c switch
			state = c_match_done

		##
		if state == c_match_done:
			t = inBuf[ip - 2] & 3
			if t == 0:
				state = c_top_loop
				continue
			# emulate c switch
			state = c_match_next

		##
		if state == c_match_next:
			out = outBuf.require(1)
			out[op] = inBuf[ip]
			op += 1
			ip += 1
			if t > 1:
				out = outBuf.require(1)
				out[op] = inBuf[ip]
				op += 1
				ip += 1
				if t > 2:
					out = outBuf.require(1)
					out[op] = inBuf[ip]
					op += 1
					ip += 1
			t = inBuf[ip]
			ip += 1
			state = c_match
			continue

	return bytes(outBuf.pack(op))


def decompress(input, initSize=16000, blockSize=8192):
	output = FlexBuffer()
	output.alloc(initSize, blockSize)
	return _decompress(bytearray(input), output)


# ======== end inline of mdict_utils/base/lzo.py


def _lzo_decompress(data, size):
	"""Decompress an LZO block: C python-lzo if usable, else the inlined pure-Python port.

	Falls back on *any* C-path failure (missing/incompatible build), so a broken
	`lzo` install can never take the script down.
	"""
	if lzo is not None:
		try:
			# headerless input, known output length -- python-lzo's documented overload
			return lzo.decompress(data, False, size)
		except Exception:  # noqa: BLE001 - intentionally fall back to the pure-Python port
			sys.stderr.write("Warning: lzo module not available, using !!!SLOW!!! pure-Python implementation\n")
	return decompress(data, initSize=size, blockSize=min(size, 1 << 20))


def _fold(s):
	"""Casefold + strip combining marks, for accent/case-insensitive matching."""
	return "".join(
		c for c in unicodedata.normalize("NFD", s.casefold()) if not unicodedata.combining(c)
	)


def _unescape_entities(text):
	"""Unescape offending tags < > " &."""
	text = text.replace(b"&lt;", b"<")
	text = text.replace(b"&gt;", b">")
	text = text.replace(b"&quot;", b'"')
	text = text.replace(b"&amp;", b"&")
	return text  # noqa: RET504


def _fast_decrypt(data, key):
	"""XOR decryption."""
	b = bytearray(data)
	key = bytearray(key)
	previous = 0x36
	for i, bi in enumerate(b):
		t = (bi >> 4 | bi << 4) & 0xFF
		t = t ^ previous ^ (i & 0xFF) ^ key[i % len(key)]
		previous = bi
		b[i] = t
	return bytes(b)


#
def _salsa_decrypt(ciphertext, encrypt_key):
	"""salsa20 (8 rounds) decryption."""
	s20 = Salsa20(key=encrypt_key, IV=b"\x00" * 8, rounds=8)
	return s20.encryptBytes(ciphertext)


def _decrypt_regcode_by_userid(reg_code: bytes, userid: bytes) -> bytes:
	userid_digest = ripemd128(userid)
	s20 = Salsa20(key=userid_digest, IV=b"\x00" * 8, rounds=8)
	return s20.encryptBytes(reg_code)


class MDict:
	"""
	Base class which reads in header and key block.
	It has no public methods and serves only as code sharing base class.
	"""

	def __init__(
			self,
			fname: str,
			encoding: str = "",
			passcode: "tuple[bytes, bytes] | None" = None,
	) -> None:
		self._fname = fname
		self._encoding = encoding.upper()
		self._encrypted_key = None
		self._passcode = passcode

		self.header = self._read_header()

		# decrypt regcode to get the encrypted key
		if passcode is not None:
			regcode, userid = passcode
			if isinstance(userid, str):
				userid = userid.encode("utf8")
			self._encrypted_key = _decrypt_regcode_by_userid(regcode, userid)
		# MDict 3.0 encryption key derives from UUID if present
		if self._version >= 3.0:
			uuid = self.header.get(b"UUID")
			if uuid:
				if xxhash is None:
					raise RuntimeError(
						"xxhash module is needed to read MDict 3.0 format"
						"\n"
						"Run `pip3 install xxhash` to install",
					)
				mid = (len(uuid) + 1) // 2
				self._encrypted_key = xxhash.xxh64_digest(
					uuid[:mid],
				) + xxhash.xxh64_digest(uuid[mid:])

		self._key_list = self._read_keys()

	def __repr__(self):
		return (
			f"MDict({self._fname!r}, "
			f"encoding={self._encoding!r}, "
			f"passcode={self._passcode})"
		)

	@property
	def filename(self):
		return self._fname

	def __len__(self):
		return self._num_entries

	def __iter__(self):
		return self.keys()

	def keys(self):
		"""Return an iterator over dictionary keys."""
		return (key_value for key_id, key_value in self._key_list)

	def _read_number(self, f):
		return unpack(self._number_format, f.read(self._number_width))[0]

	@staticmethod
	def _read_int32(f):
		return unpack(">I", f.read(4))[0]

	@staticmethod
	def _parse_header(header):
		"""Extract attributes from <Dict attr="value" ... >."""
		return {
			key: _unescape_entities(value)
			for key, value in re.findall(rb'(\w+)="(.*?)"', header, re.DOTALL)
		}

	def _decode_block(self, block, decompressed_size):
		# block info: compression, encryption
		info = unpack("<L", block[:4])[0]
		compression_method = info & 0xF
		encryption_method = (info >> 4) & 0xF
		encryption_size = (info >> 8) & 0xFF

		# adler checksum of the block data used as the encryption key if none given
		adler32 = unpack(">I", block[4:8])[0]
		encrypted_key = self._encrypted_key
		if encrypted_key is None:
			encrypted_key = ripemd128(block[4:8])

		# block data
		data = block[8:]

		# decrypt
		if encryption_method == 0:
			decrypted_block = data
		elif encryption_method == 1:
			decrypted_block = (
					_fast_decrypt(data[:encryption_size], encrypted_key)
					+ data[encryption_size:]
			)
		elif encryption_method == 2:
			decrypted_block = (
					_salsa_decrypt(data[:encryption_size], encrypted_key)
					+ data[encryption_size:]
			)
		else:
			raise ValueError(f"encryption method {encryption_method} not supported")

		# check adler checksum over decrypted data
		if self._version >= 3:
			if adler32 != (zlib.adler32(decrypted_block) & 0xFFFFFFFF):
				raise ValueError("decrypted block checksum mismatch")

		# decompress
		if compression_method == 0:
			decompressed_block = decrypted_block
		elif compression_method == 1:
			decompressed_block = _lzo_decompress(decrypted_block, decompressed_size)
		elif compression_method == 2:
			decompressed_block = zlib.decompress(decrypted_block)
		else:
			raise ValueError(f"compression method {compression_method} not supported")

		# check adler checksum over decompressed data
		if self._version < 3:
			if adler32 != (zlib.adler32(decompressed_block) & 0xFFFFFFFF):
				raise ValueError("decompressed block checksum mismatch")

		return decompressed_block

	def _decode_key_block_info(self, key_block_info_compressed):
		if self._version >= 2:
			# zlib compression
			assert key_block_info_compressed[:4] == b"\x02\x00\x00\x00"
			# decrypt if needed
			if self._encrypt & 0x02:
				key = ripemd128(key_block_info_compressed[4:8] + pack(b"<L", 0x3695))
				key_block_info_compressed = key_block_info_compressed[
					                            :8
				                            ] + _fast_decrypt(key_block_info_compressed[8:], key)
			# decompress
			key_block_info = zlib.decompress(key_block_info_compressed[8:])
			# adler checksum
			adler32 = unpack(">I", key_block_info_compressed[4:8])[0]
			assert adler32 == zlib.adler32(key_block_info) & 0xFFFFFFFF
		else:
			# no compression
			key_block_info = key_block_info_compressed
		# decode
		key_block_info_list = []
		num_entries = 0
		i = 0
		if self._version >= 2:
			byte_format = ">H"
			byte_width = 2
			text_term = 1
		else:
			byte_format = ">B"
			byte_width = 1
			text_term = 0

		while i < len(key_block_info):
			# number of entries in current key block
			num_entries += unpack(
				self._number_format,
				key_block_info[i: i + self._number_width],
			)[0]
			i += self._number_width
			# text head size
			text_head_size = unpack(byte_format, key_block_info[i: i + byte_width])[0]
			i += byte_width
			# text head
			if self._encoding != "UTF-16":
				i += text_head_size + text_term
			else:
				i += (text_head_size + text_term) * 2
			# text tail size
			text_tail_size = unpack(byte_format, key_block_info[i: i + byte_width])[0]
			i += byte_width
			# text tail
			if self._encoding != "UTF-16":
				i += text_tail_size + text_term
			else:
				i += (text_tail_size + text_term) * 2
			# key block compressed size
			key_block_compressed_size = unpack(
				self._number_format,
				key_block_info[i: i + self._number_width],
			)[0]
			i += self._number_width
			# key block decompressed size
			key_block_decompressed_size = unpack(
				self._number_format,
				key_block_info[i: i + self._number_width],
			)[0]
			i += self._number_width
			key_block_info_list.append((key_block_compressed_size, key_block_decompressed_size))

		# assert num_entries == self._num_entries

		return key_block_info_list

	def _decode_key_block(self, key_block_compressed, key_block_info_list):
		key_list = []
		i = 0
		for compressed_size, decompressed_size in key_block_info_list:
			key_block = self._decode_block(
				key_block_compressed[i: i + compressed_size],
				decompressed_size,
			)
			# extract one single key block into a key list
			key_list += self._split_key_block(key_block)
			i += compressed_size
		return key_list

	def _split_key_block(self, key_block):
		# hoist invariants out of the hot loop; scan for the NUL terminator with
		# bytes.find (C-speed) instead of a per-byte Python comparison
		key_list = []
		n = len(key_block)
		nw = self._number_width
		unpack_id = Struct(self._number_format).unpack_from
		utf16 = self._encoding == "UTF-16"
		delimiter = b"\x00\x00" if utf16 else b"\x00"
		width = 2 if utf16 else 1
		i = 0
		while i < n:
			key_id = unpack_id(key_block, i)[0]
			text_start = i + nw
			end = key_block.find(delimiter, text_start)
			if utf16:
				# the NUL pair must sit on a 2-byte code-unit boundary
				while end != -1 and (end - text_start) % 2:
					end = key_block.find(delimiter, end + 1)
			if end == -1:
				end = n
			key_text = key_block[text_start:end].decode(self._encoding, errors="ignore").strip()
			key_list.append((key_id, key_text))
			i = end + width
		return key_list

	def _read_header(self):
		with open(self._fname, "rb") as f:
			# number of bytes of header text
			header_bytes_size = unpack(">I", f.read(4))[0]
			header_bytes = f.read(header_bytes_size)
			# 4 bytes: adler32 checksum of header, in little endian
			adler32 = unpack("<I", f.read(4))[0]
			assert adler32 == zlib.adler32(header_bytes) & 0xFFFFFFFF
			# mark down key block offset
			self._key_block_offset = f.tell()

		# header text in utf-16 encoding ending with '\x00\x00'
		if header_bytes[-2:] == b"\x00\x00":
			header_text = header_bytes[:-2].decode("utf-16").encode("utf-8")
		else:
			header_text = header_bytes[:-1]
		header_tag = self._parse_header(header_text)

		if not self._encoding:
			encoding = header_tag.get(b"Encoding", b"utf-8")
			if sys.hexversion >= 0x03000000:
				encoding = encoding.decode("utf-8")
			# GB18030 > GBK > GB2312
			if encoding in {"GBK", "GB2312"}:
				encoding = "GB18030"
			self._encoding = encoding

		# encryption flag
		# 0x00 - no encryption, "Allow export to text" is checked in MdxBuilder 3.
		# 0x01 - encrypt record block, "Encryption Key" is given in MdxBuilder 3.
		# 0x02 - encrypt key info block,
		#        "Allow export to text" is unchecked in MdxBuilder 3.
		if b"Encrypted" not in header_tag or header_tag[b"Encrypted"] == b"No":
			self._encrypt = 0
		elif header_tag[b"Encrypted"] == b"Yes":
			self._encrypt = 1
		else:
			self._encrypt = int(header_tag[b"Encrypted"])

		# stylesheet attribute if present takes form of:
		#   style_number # 1-255
		#   style_begin  # or ''
		#   style_end	 # or ''
		# store stylesheet in dict in the form of
		# {'number' : ('style_begin', 'style_end')}
		self._stylesheet = {}
		if header_tag.get(b"StyleSheet"):
			lines = header_tag[b"StyleSheet"].decode("utf-8", errors="ignore").splitlines()
			self._stylesheet = {
				lines[i]: (lines[i + 1], lines[i + 2]) for i in range(0, len(lines), 3)
			}

		# before version 2.0, number is 4 bytes integer
		# version 2.0 and above uses 8 bytes
		self._version = float(header_tag[b"GeneratedByEngineVersion"])
		if self._version < 2.0:
			self._number_width = 4
			self._number_format = ">I"
		else:
			self._number_width = 8
			self._number_format = ">Q"
			# version 3.0 uses UTF-8 only
			if self._version >= 3:
				self._encoding = "UTF-8"

		return header_tag

	def _read_keys(self):
		if self._version >= 3:
			return self._read_keys_v3()

		# if no regcode is given, try brute-force (only for engine <= 2)
		if (self._encrypt & 0x01) and self._encrypted_key is None:
			log.warning("Trying brute-force on encrypted key blocks")
			return self._read_keys_brutal()

		return self._read_keys_v1v2()

	def _read_keys_v3(self):
		with open(self._fname, "rb") as f:
			f.seek(self._key_block_offset)

			# find all blocks offset
			while True:
				block_type = self._read_int32(f)
				block_size = self._read_number(f)
				block_offset = f.tell()
				if block_type == 0x01000000:  # record data
					self._record_block_offset = block_offset
				elif block_type == 0x02000000:  # record index
					self._record_index_offset = block_offset
				elif block_type == 0x03000000:  # key data
					self._key_data_offset = block_offset
				elif block_type == 0x04000000:  # key index
					self._key_index_offset = block_offset
				else:
					raise RuntimeError(f"Unknown block type {block_type}")
				f.seek(block_size, 1)
				# test the end of file
				if f.read(4):
					f.seek(-4, 1)
				else:
					break

			# read key data
			f.seek(self._key_data_offset)
			number = self._read_int32(f)
			self._read_number(f)  # total_size
			key_list = []
			for _ in range(number):
				decompressed_size = self._read_int32(f)
				compressed_size = self._read_int32(f)
				block_data = f.read(compressed_size)
				decompressed_block_data = self._decode_block(block_data, decompressed_size)
				key_list.extend(self._split_key_block(decompressed_block_data))

		self._num_entries = len(key_list)
		return key_list

	def _read_keys_v1v2(self):
		with open(self._fname, "rb") as f:
			f.seek(self._key_block_offset)

			# the following numbers could be encrypted
			num_bytes = 8 * 5 if self._version >= 2.0 else 4 * 4
			block = f.read(num_bytes)
			if self._encrypt & 1:
				block = _salsa_decrypt(block, self._encrypted_key)

			# decode this block
			sf = BytesIO(block)
			num_key_blocks = self._read_number(sf)
			self._num_entries = self._read_number(sf)
			if self._version >= 2.0:
				self._read_number(sf)  # key_block_info_decomp_size
			key_block_info_size = self._read_number(sf)
			key_block_size = self._read_number(sf)

			# 4 bytes: adler checksum of previous 5 numbers
			if self._version >= 2.0:
				adler32 = unpack(">I", f.read(4))[0]
				assert adler32 == (zlib.adler32(block) & 0xFFFFFFFF)

			# key block info gives each key block's compressed/decompressed size
			key_block_info = f.read(key_block_info_size)
			key_block_info_list = self._decode_key_block_info(key_block_info)
			assert num_key_blocks == len(key_block_info_list)

			# read & extract key block
			key_block_compressed = f.read(key_block_size)
			key_list = self._decode_key_block(key_block_compressed, key_block_info_list)

			self._record_block_offset = f.tell()
		return key_list

	def _read_keys_brutal(self):
		with open(self._fname, "rb") as f:
			f.seek(self._key_block_offset)

			# the following numbers could be encrypted, disregard them!
			if self._version >= 2.0:
				num_bytes = 8 * 5 + 4
				key_block_type = b"\x02\x00\x00\x00"
			else:
				num_bytes = 4 * 4
				key_block_type = b"\x01\x00\x00\x00"

			f.read(num_bytes)  # block

			# key block info
			# 4 bytes '\x02\x00\x00\x00'
			# 4 bytes adler32 checksum
			# unknown number of bytes follows until '\x02\x00\x00\x00'
			# which marks the beginning of key block
			key_block_info = f.read(8)
			if self._version >= 2.0:
				assert key_block_info[:4] == b"\x02\x00\x00\x00"
			while True:
				fpos = f.tell()
				t = f.read(1024)
				index = t.find(key_block_type)
				if index != -1:
					key_block_info += t[:index]
					f.seek(fpos + index)
					break
				key_block_info += t

			key_block_info_list = self._decode_key_block_info(key_block_info)
			key_block_size = sum(list(zip(*key_block_info_list, strict=False))[0])

			# read & extract key block
			key_block_compressed = f.read(key_block_size)
			key_list = self._decode_key_block(key_block_compressed, key_block_info_list)

			self._record_block_offset = f.tell()

		self._num_entries = len(key_list)
		return key_list

	def items(self):
		"""Generator yielding (key/filename, content) tuples for every entry."""
		return self._read_records()

	def lookup(self, word):
		"""Records whose headword matches `word`: exact first, else accent/case-insensitive.

		Returns a list of (headword, raw_record_bytes). A linear scan is used on purpose:
		the key list is sorted by the dictionary's own collation (e.g. 'a-' before 'a'),
		not Python order, so bisect/binary-search would silently miss or misreturn entries.
		"""
		kl = self._key_list
		n = len(kl)

		def collect(match):
			out = []
			for x, (offset, headword) in enumerate(kl):
				if match(headword):
					length = kl[x + 1][0] - offset if x + 1 < n else -1
					out.append((headword, self.get_record(offset, length)))
			return out

		return collect(word.__eq__) or collect(lambda hw, k=_fold(word): _fold(hw) == k)

	def lookup_prefix(self, word, limit):
		"""(headword, raw_record) for entries matching `word`: ALL exact matches, or — if
		there are none — the first `limit` prefix (startswith) matches. Falls back to an
		accent/case-insensitive pass only when the raw pass finds nothing.

		Linear scan on purpose: the key list is in the dictionary's own collation (e.g.
		'a-' before 'a'), not Python order, so a bisect prefix-range would be unsound.
		"""
		kl = self._key_list
		n = len(kl)

		def scan(fold):
			key = _fold(word) if fold else word
			exact, prefix = [], []
			for x in range(n):
				hw = _fold(kl[x][1]) if fold else kl[x][1]
				if hw == key:
					exact.append(x)
				elif len(prefix) < limit and hw.startswith(key):
					prefix.append(x)
			return exact or prefix

		out = []
		for x in (scan(False) or scan(True))[:limit]:
			offset = kl[x][0]
			length = kl[x + 1][0] - offset if x + 1 < n else -1
			out.append((kl[x][1], self.get_record(offset, length)))
		return out

	def get_record(self, offset, length):
		"""Raw record bytes for the entry at `offset` (length<0 means to end of block)."""
		if self._version >= 3:
			return self.get_record_v3(offset, length)
		return self.get_record_v1v2(offset, length)

	def get_record_v3(self, offset, length):
		with open(self._fname, "rb") as f:
			f.seek(self._record_block_offset)
			num_record_blocks = self._read_int32(f)
			self._read_number(f)  # num_bytes
			decompressed_offset = 0
			compressed_size = decompressed_size = 0
			for _ in range(num_record_blocks):
				decompressed_size = self._read_int32(f)
				compressed_size = self._read_int32(f)
				if decompressed_offset + decompressed_size > offset:
					break
				decompressed_offset += decompressed_size
				f.seek(compressed_size, 1)
			record_block = self._decode_block(f.read(compressed_size), decompressed_size)

		start = offset - decompressed_offset
		return record_block[start: start + length] if length > 0 else record_block[start:]

	def get_record_v1v2(self, offset, length):
		with open(self._fname, "rb") as f:
			f.seek(self._record_block_offset)
			num_record_blocks = self._read_number(f)
			assert self._read_number(f) == self._num_entries  # num_entries
			record_block_info_size = self._read_number(f)
			self._read_number(f)  # record_block_size

			# walk the record-block-info table to the block containing `offset`
			compressed_offset = f.tell() + record_block_info_size
			decompressed_offset = 0
			compressed_size = decompressed_size = 0
			for _ in range(num_record_blocks):
				compressed_size = self._read_number(f)
				decompressed_size = self._read_number(f)
				if decompressed_offset + decompressed_size > offset:
					break
				decompressed_offset += decompressed_size
				compressed_offset += compressed_size

			f.seek(compressed_offset)
			# _decode_block handles type/encryption/compression/checksums uniformly
			record_block = self._decode_block(f.read(compressed_size), decompressed_size)

		start = offset - decompressed_offset
		return record_block[start: start + length] if length > 0 else record_block[start:]

	def _read_records(self):
		if self._version >= 3:
			yield from self._read_records_v3()
		else:
			yield from self._read_records_v1v2()

	def _read_records_v3(self):
		with open(self._fname, "rb") as f:
			f.seek(self._record_block_offset)
			num_record_blocks = self._read_int32(f)
			self._read_number(f)  # num_bytes
			offset = 0
			i = 0
			for _ in range(num_record_blocks):
				decompressed_size = self._read_int32(f)
				compressed_size = self._read_int32(f)
				record_block = self._decode_block(f.read(compressed_size), decompressed_size)
				# split record block according to the offset info from key block
				while i < len(self._key_list):
					record_start, key_text = self._key_list[i]
					if record_start - offset >= len(record_block):  # past end of block
						break
					record_end = (
						self._key_list[i + 1][0]
						if i < len(self._key_list) - 1
						else len(record_block) + offset
					)
					i += 1
					data = record_block[record_start - offset: record_end - offset]
					yield key_text, self._treat_record_data(data)
				offset += len(record_block)

	def _read_records_v1v2(self):
		with open(self._fname, "rb") as f:
			f.seek(self._record_block_offset)
			num_record_blocks = self._read_number(f)
			assert self._read_number(f) == self._num_entries  # num_entries
			record_block_info_size = self._read_number(f)
			self._read_number(f)  # record_block_size

			# record block info section
			record_block_info_list = []
			size_counter = 0
			for _ in range(num_record_blocks):
				compressed_size = self._read_number(f)
				decompressed_size = self._read_number(f)
				record_block_info_list.append((compressed_size, decompressed_size))
				size_counter += self._number_width * 2
			assert size_counter == record_block_info_size

			# actual record block
			offset = 0
			i = 0
			for compressed_size, decompressed_size in record_block_info_list:
				record_block_compressed = f.read(compressed_size)
				try:
					record_block = self._decode_block(record_block_compressed, decompressed_size)
				except zlib.error:
					log.error("zlib decompress error")
					log.debug(f"record_block_compressed = {record_block_compressed!r}")
					continue
				# split record block according to the offset info from key block
				while i < len(self._key_list):
					record_start, key_text = self._key_list[i]
					if record_start - offset >= len(record_block):  # past end of block
						break
					record_end = (
						self._key_list[i + 1][0]
						if i < len(self._key_list) - 1
						else len(record_block) + offset
					)
					i += 1
					data = record_block[record_start - offset: record_end - offset]
					yield key_text, self._treat_record_data(data)
				offset += len(record_block)

	def _treat_record_data(self, data):  # noqa: PLR6301
		return data


class MDD(MDict):
	"""
	MDict resource file format (*.MDD) reader.
	>>> mdd = MDD("example.mdd")
	>>> len(mdd)
	208
	>>> for filename,content in mdd.items():
	... 	print(filename, content[:10])
	"""

	def __init__(
			self,
			fname: str,
			passcode: "tuple[bytes, bytes] | None" = None,
	) -> None:
		MDict.__init__(self, fname, encoding="UTF-16", passcode=passcode)


class MDX(MDict):
	"""
	MDict dictionary file format (*.MDD) reader.
	>>> mdx = MDX("example.mdx")
	>>> len(mdx)
	42481
	>>> for key,value in mdx.items():
	... 	print(key, value[:10])
	"""

	def __init__(
			self,
			fname: str,
			encoding: str = "",
			substyle: bool = False,
			passcode: "tuple[bytes, bytes] | None" = None,
	) -> None:
		MDict.__init__(self, fname, encoding, passcode)
		self._substyle = substyle

	def _substitute_stylesheet(self, txt):
		# substitute stylesheet definition
		txt_list = re.split(r"`\d+`", txt)
		txt_tag = re.findall(r"`\d+`", txt)
		txt_styled = txt_list[0]
		for j, p in enumerate(txt_list[1:]):
			key = txt_tag[j][1:-1]
			try:
				style = self._stylesheet[key]
			except KeyError:
				log.error(f'invalid stylesheet key "{key}"')
				continue
			if p and p[-1] == "\n":
				txt_styled = txt_styled + style[0] + p.rstrip() + style[1] + "\r\n"
			else:
				txt_styled = txt_styled + style[0] + p + style[1]
		return txt_styled

	def _treat_record_data(self, data):
		# decode, optionally apply the stylesheet (on text, not bytes), re-encode to utf-8
		txt = data.decode(self._encoding, errors="ignore").strip("\x00")
		if self._substyle and self._stylesheet:
			txt = self._substitute_stylesheet(txt)
		return txt.encode("utf-8")


class Reader:
	useByteProgress = False
	_encoding: str = ""
	_substyle: bool = True
	_same_dir_data_files: bool = False
	_audio: bool = True

	def __init__(self, glos) -> None:
		self._glos = glos
		self.clear()
		# capture the target word so it can be url-encoded into a CGI query
		self._re_internal_link = re.compile(r"""href=(["'])(?:entry://|bword://|[dx]:)([^"']*)\1""")

	def clear(self) -> None:
		self._filename = ""
		self._mdx: MDX | None = None
		self._mdd: list[MDD] = []
		self._wordCount = 0
		self._dataEntryCount = 0

		# dict of mainWord -> newline-separated alternatives
		self._linksDict: dict[str, str] = {}

		# lazy {normalized_resource_path: (mdd, offset, length)} across all MDD files
		self._resMap: "dict[str, tuple] | None" = None

	def open(self, filename: str, do_load_links=False) -> None:
		# from readmdict import MDD, MDX

		self._filename = filename
		self._mdx = MDX(filename, self._encoding, self._substyle)

		"""
			multiple MDD files are supported with this naming schema:
				FILE.mdx
				FILE.mdd
				FILE.1.mdd
				FILE.2.mdd
				FILE.3.mdd
		"""

		filenameNoExt, _ext = splitext(self._filename)
		mddBase = filenameNoExt + extsep
		for fname in (f"{mddBase}mdd", f"{mddBase}1.mdd"):
			if isfile(fname):
				self._mdd.append(MDD(fname))
		mddN = 2
		while isfile(f"{mddBase}{mddN}.mdd"):
			self._mdd.append(MDD(f"{mddBase}{mddN}.mdd"))
			mddN += 1

		dataEntryCount = 0
		for mdd in self._mdd:
			dataEntryCount += len(mdd)
		self._dataEntryCount = dataEntryCount
		sys.stderr.write(
			f"Found {len(self._mdd)} mdd files with {dataEntryCount} entries\n"
		)

		# from pprint import pformat
		# log.debug("mdx.header = " + pformat(self._mdx.header))
		# for key, value in self._mdx.header.items():
		# 	key = key.lower()
		# 	self._glos.setInfo(key, value)
		try:
			title = self._mdx.header[b"Title"].decode("utf-8")
		except KeyError:
			pass
		else:
			title = title.strip()
			if title == "Title (No HTML code allowed)":
				# TODO: how to avoid this?
				title = ""
			if title:
				self._glos.setInfo("name", title)
		desc = self._mdx.header.get(b"Description", "").decode()
		if desc:
			self._glos.setInfo("description", desc)

		if do_load_links:
			self.loadLinks()

	def loadLinks(self) -> None:
		mdx = self._mdx
		if mdx is None:
			raise ValueError("mdx is None")

		# print("extracting links...")
		linksDict: dict[str, str] = {}
		word = ""
		wordCount = 0
		for b_word, b_defi in mdx.items():
			word = b_word
			defi = b_defi.decode("utf-8", errors="ignore").strip()
			if defi.startswith("@@@LINK="):
				if not word:
					sys.stderr.write(f"unexpected defi: {defi}\n")
					continue
				mainWord = defi[8:]
				if mainWord in linksDict:
					linksDict[mainWord] += "\n" + word
				else:
					linksDict[mainWord] = word
				continue
			wordCount += 1

		sys.stderr.write(
			f"extracting links done, sizeof(linksDict)={sys.getsizeof(linksDict)}\n",
		)
		sys.stderr.write(f"{wordCount = }")
		self._linksDict = linksDict
		self._wordCount = wordCount
		self._mdx = MDX(self._filename, self._encoding, self._substyle)

	def _internal_link_repl(self, m):
		# entry://word (or d:/x:word) -> CGI query that stays in the current dictionary
		q, word = m.group(1), m.group(2)
		return f"href={q}?path={quote(self._filename)}&amp;q={quote(word)}{q}"

	@staticmethod
	def _audio_tag_repl(m):
		# <audio src="X" ...>inner</audio> -> in-page play link
		srcm = _RE_AUDIO_SRC.search(m.group(0))
		if not srcm:
			return m.group(1)
		src = srcm.group(1)

		if src.lower().startswith("sound://"):
			src = src[len("sound://"):]
		# <audio> inner is fallback markup (<source>/<track> + maybe text); keep only a real label
		label = re.sub(r"<(?:source|track)\b[^>]*>", "", m.group(1)).strip() or "🔊"
		return f'<a onclick="{_AUDIO_ONCLICK}" href="{src}">{label}</a>'

	@staticmethod
	def _audio_anchor_repl(m):
		# <a ...href="sound://X"...> -> sound:// stripped + in-page onclick (added if absent)
		pre, q, path, post = m.group(1), m.group(2), m.group(3), m.group(4)
		onclick = "" if "onclick" in (pre + post).lower() else f'onclick="{_AUDIO_ONCLICK}" '
		return f"<a{pre}{onclick}href={q}{path}{q}{post}>"

	def fixDefi(self, defi: str) -> str:
		defi = self._re_internal_link.sub(self._internal_link_repl, defi)
		# strip file:// so the ref becomes a plain relative path the asset extractor handles
		defi = re.sub(r"""(src|href)=(["'])file://""", r"\1=\2", defi)

		if self._audio:
			defi = _RE_AUDIO_TAG.sub(self._audio_tag_repl, defi)
			defi = _RE_SOUND_ANCHOR.sub(self._audio_anchor_repl, defi)
			# any stray sound:// left in a src/href -> relative path (still extractable)
			defi = re.sub(r"""(src|href)=(["'])sound://""", r"\1=\2", defi)
			# Speex isn't browser-playable: point links at the transcoded sibling that
			# extract_assets produces on demand, e.g. href="x.spx" -> href="x.spx.wav"
			defi = re.sub(r"""((?:src|href)=["'][^"']*?\.spx)(["'])""", r"\1.wav\2", defi, flags=re.I)

		# server-absolute refs (src/href="/foo") -> relative, so they resolve into the static
		# asset folder like every other ref. Done last to also catch anything the steps above
		# emitted with a leading slash. Leaves protocol-relative //host and ?query links alone.
		defi = _RE_ABS_REF.sub(r"\1\2", defi)
		return defi

	def _render(self, raw, _seen):
		"""One raw record -> [HTML defi], following an @@@LINK redirect (exact, cycle-guarded)."""
		defi = self._mdx._treat_record_data(raw).decode("utf-8", errors="ignore").strip()
		if defi.startswith("@@@LINK="):
			target = defi[8:].strip().strip("\x00")
			return self.define(target, _seen) if target and target not in _seen else []
		return [self.fixDefi(defi)]

	def define(self, word, _seen=None):
		"""HTML definitions for the exact headword `word` (+ homographs), following @@@LINK."""
		mdx = self._mdx
		if mdx is None:
			return []
		if _seen is None:
			_seen = set()
		_seen.add(word)
		out = []
		for _headword, raw in mdx.lookup(word):
			out.extend(self._render(raw, _seen))
		return out

	def search(self, word, limit):
		"""HTML definitions for headwords matching `word` (exact, else prefix), capped at `limit`."""
		mdx = self._mdx
		if mdx is None:
			return []
		out = []
		for headword, raw in mdx.lookup_prefix(word, limit):
			out.extend(self._render(raw, {headword}))
			if len(out) >= limit:
				break
		return out[:limit]

	def _resource_index(self):
		"""Lazy {lowercased normalized path: (mdd, offset, length)} over all MDD resources."""
		if self._resMap is None:
			m = {}
			for mdd in self._mdd:
				kl = mdd._key_list
				n = len(kl)
				for i in range(n):
					offset, key = kl[i]
					norm = key.lstrip("\\/").replace("\\", "/").lower()
					if norm not in m:
						length = kl[i + 1][0] - offset if i + 1 < n else -1
						m[norm] = (mdd, offset, length)
			self._resMap = m
		return self._resMap

	@staticmethod
	def _ref_is_local(ref):
		return not _RE_NONLOCAL.match(ref)

	def extract_assets(self, html):
		"""Extract every local resource referenced by `html` (transitively via CSS) to ASSET_ROOT.

		A relative ref ``a/b.png`` is written to ``ASSET_ROOT/a/b.png`` so the browser's own
		relative resolution finds it -- no URL rewriting needed. Existing files are left as-is;
		intermediate dirs are created; nothing is cleaned up.
		"""
		index = self._resource_index()
		if not index:
			return
		seen = set()
		queue = [r for r in _RE_HTML_REF.findall(html) if self._ref_is_local(r)]
		while queue:
			ref = queue.pop()
			norm = posixpath.normpath(ref.split("#", 1)[0].split("?", 1)[0]).lstrip("/")
			if not norm or norm == "." or norm.startswith("..") or norm in seen:
				continue
			seen.add(norm)
			hit = index.get(norm.lower())
			if hit is None:
				# "<name>.spx.wav" has no MDD entry: extract the "<name>.spx" source and
				# transcode it once (Speex is not browser-playable). Cached like everything else.
				if norm.endswith(".spx.wav"):
					self._transcode_spx(norm[:-4], norm, index)
				continue
			mdd, offset, length = hit
			dest = ASSET_ROOT / norm
			data = None
			# regenerate when missing OR empty: never trust a 0-byte cached file
			if not dest.exists() or dest.stat().st_size == 0:
				data = mdd.get_record(offset, length)
				if data:
					dest.parent.mkdir(parents=True, exist_ok=True)
					dest.write_bytes(data)
			# CSS pulls in fonts/sprites/@imports by relative url -- follow them
			if norm.endswith(".css"):
				if data is None:
					data = dest.read_bytes()
				css = data.decode("utf-8", "ignore")
				base = posixpath.dirname(norm)
				for sub in _RE_CSS_URL.findall(css) + _RE_CSS_IMPORT.findall(css):
					if self._ref_is_local(sub):
						queue.append(posixpath.join(base, sub.split("#", 1)[0].split("?", 1)[0]))

	def _transcode_spx(self, src_norm, dest_norm, index):
		"""Extract the Speex resource `src_norm` and transcode it to `dest_norm` (WAV) via
		ffmpeg, once. Browsers can't play Speex; the .wav sibling is what links point at.
		Cached (skipped if present) and fail-soft (a missing/failing ffmpeg just leaves no .wav).
		"""
		hit = index.get(src_norm.lower())
		dest = ASSET_ROOT / dest_norm
		# skip only when a NON-empty transcode already exists (0-byte = retry)
		if hit is None or (dest.exists() and dest.stat().st_size):
			return
		mdd, offset, length = hit
		src = ASSET_ROOT / src_norm
		if not src.exists() or src.stat().st_size == 0:
			data = mdd.get_record(offset, length)
			if not data:
				sys.stderr.write(f"empty source resource {src_norm}, skipping transcode\n")
				return
			src.parent.mkdir(parents=True, exist_ok=True)
			src.write_bytes(data)
		try:
			subprocess.run(
				["/opt/homebrew/bin/speexdec", str(src), str(dest)],
				check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
			)
		except (OSError, subprocess.CalledProcessError) as e:
			# don't leave a 0-byte transcode behind: it would be served empty AND cached
			if dest.exists() and dest.stat().st_size == 0:
				dest.unlink()
			sys.stderr.write(f"spx transcode failed for {src_norm}: {e}\n")

	def __iter__(self):
		if self._mdx is None:
			sys.stderr.write("trying to iterate on a closed MDX file\n")
			return

		glos = self._glos
		linksDict = self._linksDict
		for b_word, b_defi in self._mdx.items():
			word = b_word
			defi = b_defi.decode("utf-8", errors="ignore").strip()
			if defi.startswith("@@@LINK="):
				continue
			defi = self.fixDefi(defi)
			words = word
			altsStr = linksDict.get(word, "")
			if altsStr:
				words = [word] + altsStr.split("\n")
			# sys.stderr.write(f'\n\n\n\nVVVVVVGGGGG:::words type:::{type(words)} defi type::{type(defi)} words={words}   VVVVVVGGGGG defi={defi} ')
			yield glos.newEntry(words, defi)

		self._mdx = None
		del linksDict
		self._linksDict = {}

		if self._same_dir_data_files:
			dirPath = dirname(self._filename)
			for fname in os.listdir(dirPath):
				ext = splitext(fname)[1].lower()
				if ext in {".mdx", ".mdd"}:
					continue
				fpath = join(dirPath, fname)
				if not isfile(fpath):
					continue
				with open(fpath, mode="rb") as _file:
					b_data = _file.read()
				yield glos.newDataEntry(fname, b_data)

		for mdd in self._mdd:
			try:
				for b_fname, b_data in mdd.items():
					fname = str(b_fname)
					fname = fname.replace("\\", os.sep).lstrip(os.sep)
					yield glos.newDataEntry(fname, b_data)
			except Exception:  # noqa: PERF203
				sys.stderr.write(f"Error reading {mdd.filename}\n")
		self._mdd = []

	def __len__(self) -> int:
		return self._wordCount + self._dataEntryCount

	def close(self) -> None:
		self.clear()


class Dictionary:
	def __init__(self):
		self.entries = {}
		self.info = {}

	def getInfo(self, key: str) -> str:
		return self.info.get(key)

	def setInfo(self, key: str, value: str) -> None:
		self.info[key] = value

	def newEntry(self, word: str, defi: str):
		if isinstance(word, list):
			word = "<br>@=+=+=+=+=+=+=+=+=+@<br>".join(word)
		self.entries[word] = defi
		return {"word": word, "defi": defi}


def main():
	print("Content-type: text/html\n")

	html = (Path(__file__).parent / "mdict_cgi.html").read_text(encoding="utf8")

	MAX_ITEMS_DEFAULT = 42

	params = parse_qs(os.getenv("QUERY_STRING", ""))
	q: str = params.get("q", [None])[0]
	max: int = int(params.get("max", ["0"])[0]) or MAX_ITEMS_DEFAULT
	path = params.get("path", [None])[0]

	reader = None

	dict_dir_path = Path(DICT_DIR).expanduser()
	path_in = (dict_dir_path / path).resolve()

	if path_in.exists():
		mdict_data = Dictionary()
		reader = Reader(glos=mdict_data)
		reader.open(str(path_in.absolute()))
		dict_name = mdict_data.info.get("name") or path_in.stem
		html = html.replace("$$${{{DICT_NAME}}}", dict_name)


	f: Path
	options = "\n".join(
		f'<option{" selected" if f == path_in else ""} value="{f.relative_to(dict_dir_path)}">{f.name}</option>'
		for f in sorted(dict_dir_path.expanduser().resolve().rglob("*.mdx"),
		                key=lambda p: p.name.lower())
	)
	#
	html = html.replace("$$${{{DICT_OPTIONS}}}", options)
	print(html)

	# NB: `if reader:` would be falsy for dicts with no entries counted yet, because
	# Reader.__len__ returns wordCount+dataEntryCount (0 when there are no .mdd files and
	# loadLinks() wasn't called). Test identity, not truthiness.
	if reader is not None:
		if q:
			for defi in reader.search(q, max):
				try:
					reader.extract_assets(defi)
				except OSError as e:
					sys.stderr.write(f"asset extraction failed: {e}\n")
				print(defi)
		else:
			print("""<pre>""")
			print("\n".join(kword for _, kword in reader._mdx._key_list[:max]))
			print("""</pre>""")
	print("""</div>
</div>
</body>
</html>""")


main()
