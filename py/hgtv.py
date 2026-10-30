# -*- coding: utf-8 -*-
"""
HGTV / 红果短剧 TVBox 源（单文件版）
=================================================
浏览·分类·详情·搜索：官网 SSR
播放：fqnovel 播放模型接口；加密档由本机代理做 CENC-AES-CTR 实时解密

TVBox 配置：
  "type": 3,
  "api": "hgtv.py 的路径"
"""

import base64
import bisect
import hashlib
import json
import os
import random
import re
import socket
import struct
import sys
import threading
import time
from urllib.parse import quote, urlparse, parse_qs, unquote

try:
    from urllib.request import Request as _Request, urlopen as _urlopen
except ImportError:
    from urllib2 import Request as _Request, urlopen as _urlopen

try:
    import requests as _requests
except Exception:
    _requests = None

########## 1. AES（纯 Python 实现，无第三方依赖） ##########

"""纯 Python AES（CTR 加密 / CBC 解密），无第三方依赖"""

_SBOX = [
0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16]
_INV = [0] * 256
for _i, _v in enumerate(_SBOX):
    _INV[_v] = _i
_RCON = [0x01,0x02,0x04,0x08,0x10,0x20,0x40,0x80,0x1b,0x36,0x6c,0xd8,0xab,0x4d]

def _xt(a):
    return ((a << 1) ^ 0x1b) & 0xff if a & 0x80 else (a << 1)

# T 表：Te0..Te3
Te0 = [0]*256; Te1 = [0]*256; Te2 = [0]*256; Te3 = [0]*256
for _i in range(256):
    s = _SBOX[_i]; s2 = _xt(s); s3 = s2 ^ s
    Te0[_i] = (s2 << 24) | (s << 16) | (s << 8) | s3
    Te1[_i] = (s3 << 24) | (s2 << 16) | (s << 8) | s
    Te2[_i] = (s << 24) | (s3 << 16) | (s2 << 8) | s
    Te3[_i] = (s << 24) | (s << 16) | (s3 << 8) | s2
# 解密用 Td 表
Td0 = [0]*256; Td1 = [0]*256; Td2 = [0]*256; Td3 = [0]*256
def _gm(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a = _xt(a); b >>= 1
    return r
for _i in range(256):
    s = _INV[_i]
    s9, s11, s13, s14 = _gm(s,9), _gm(s,11), _gm(s,13), _gm(s,14)
    Td0[_i] = (s14 << 24) | (s9 << 16) | (s13 << 8) | s11
    Td1[_i] = (s11 << 24) | (s14 << 16) | (s9 << 8) | s13
    Td2[_i] = (s13 << 24) | (s11 << 16) | (s14 << 8) | s9
    Td3[_i] = (s9 << 24) | (s13 << 16) | (s11 << 8) | s14

class AES(object):
    __slots__ = ("rk", "nr", "dk")

    def __init__(self, key):
        nk = len(key) // 4
        self.nr = nk + 6
        w = [list(key[4*i:4*i+4]) for i in range(nk)]
        for i in range(nk, 4 * (self.nr + 1)):
            t = list(w[i-1])
            if i % nk == 0:
                t = t[1:] + t[:1]
                t = [_SBOX[b] for b in t]
                t[0] ^= _RCON[i//nk - 1]
            elif nk > 6 and i % nk == 4:
                t = [_SBOX[b] for b in t]
            w.append([w[i-nk][j] ^ t[j] for j in range(4)])
        self.rk = [0] * (4 * (self.nr + 1))
        for i, wi in enumerate(w):
            self.rk[i] = (wi[0] << 24) | (wi[1] << 16) | (wi[2] << 8) | wi[3]
        # 解密轮密钥（逆序 + InvMixColumns）
        dk = list(self.rk)
        for r in range(1, self.nr):
            for c in range(4):
                v = self.rk[r*4 + c]
                dk[r*4 + c] = (Td0[_SBOX[(v >> 24) & 0xff]] ^ Td1[_SBOX[(v >> 16) & 0xff]] ^
                               Td2[_SBOX[(v >> 8) & 0xff]] ^ Td3[_SBOX[v & 0xff]])
        dk2 = [0] * len(dk)
        for r in range(self.nr + 1):
            for c in range(4):
                dk2[r*4 + c] = dk[(self.nr - r) * 4 + c]
        self.dk = dk2

    def encrypt_block(self, s0, s1, s2, s3):
        rk = self.rk; nr = self.nr
        s0 ^= rk[0]; s1 ^= rk[1]; s2 ^= rk[2]; s3 ^= rk[3]
        k = 4
        for _ in range(1, nr):
            t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >> 8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[k]
            t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >> 8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[k+1]
            t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >> 8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[k+2]
            t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >> 8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[k+3]
            s0, s1, s2, s3 = t0, t1, t2, t3
            k += 4
        o0 = ((_SBOX[s0 >> 24] << 24) | (_SBOX[(s1 >> 16) & 0xff] << 16) | (_SBOX[(s2 >> 8) & 0xff] << 8) | _SBOX[s3 & 0xff]) ^ rk[k]
        o1 = ((_SBOX[s1 >> 24] << 24) | (_SBOX[(s2 >> 16) & 0xff] << 16) | (_SBOX[(s3 >> 8) & 0xff] << 8) | _SBOX[s0 & 0xff]) ^ rk[k+1]
        o2 = ((_SBOX[s2 >> 24] << 24) | (_SBOX[(s3 >> 16) & 0xff] << 16) | (_SBOX[(s0 >> 8) & 0xff] << 8) | _SBOX[s1 & 0xff]) ^ rk[k+2]
        o3 = ((_SBOX[s3 >> 24] << 24) | (_SBOX[(s0 >> 16) & 0xff] << 16) | (_SBOX[(s1 >> 8) & 0xff] << 8) | _SBOX[s2 & 0xff]) ^ rk[k+3]
        return o0, o1, o2, o3

    def decrypt_block(self, s0, s1, s2, s3):
        dk = self.dk; nr = self.nr
        s0 ^= dk[0]; s1 ^= dk[1]; s2 ^= dk[2]; s3 ^= dk[3]
        k = 4
        for _ in range(1, nr):
            t0 = Td0[s0 >> 24] ^ Td1[(s3 >> 16) & 0xff] ^ Td2[(s2 >> 8) & 0xff] ^ Td3[s1 & 0xff] ^ dk[k]
            t1 = Td0[s1 >> 24] ^ Td1[(s0 >> 16) & 0xff] ^ Td2[(s3 >> 8) & 0xff] ^ Td3[s2 & 0xff] ^ dk[k+1]
            t2 = Td0[s2 >> 24] ^ Td1[(s1 >> 16) & 0xff] ^ Td2[(s0 >> 8) & 0xff] ^ Td3[s3 & 0xff] ^ dk[k+2]
            t3 = Td0[s3 >> 24] ^ Td1[(s2 >> 16) & 0xff] ^ Td2[(s1 >> 8) & 0xff] ^ Td3[s0 & 0xff] ^ dk[k+3]
            s0, s1, s2, s3 = t0, t1, t2, t3
            k += 4
        o0 = ((_INV[s0 >> 24] << 24) | (_INV[(s3 >> 16) & 0xff] << 16) | (_INV[(s2 >> 8) & 0xff] << 8) | _INV[s1 & 0xff]) ^ dk[k]
        o1 = ((_INV[s1 >> 24] << 24) | (_INV[(s0 >> 16) & 0xff] << 16) | (_INV[(s3 >> 8) & 0xff] << 8) | _INV[s2 & 0xff]) ^ dk[k+1]
        o2 = ((_INV[s2 >> 24] << 24) | (_INV[(s1 >> 16) & 0xff] << 16) | (_INV[(s0 >> 8) & 0xff] << 8) | _INV[s3 & 0xff]) ^ dk[k+2]
        o3 = ((_INV[s3 >> 24] << 24) | (_INV[(s2 >> 16) & 0xff] << 16) | (_INV[(s1 >> 8) & 0xff] << 8) | _INV[s0 & 0xff]) ^ dk[k+3]
        return o0, o1, o2, o3

def ctr_xor(key, nonce, data):
    a = AES(key)
    n = len(data)
    out = bytearray(n)
    c0 = int.from_bytes(nonce[0:4], "big")
    c1 = int.from_bytes(nonce[4:8], "big")
    c2 = int.from_bytes(nonce[8:12], "big")
    c3 = int.from_bytes(nonce[12:16], "big")
    enc = a.encrypt_block
    blocks = n // 16
    for i in range(blocks):
        o0, o1, o2, o3 = enc(c0, c1, c2, c3)
        ks = o0.to_bytes(4, "big") + o1.to_bytes(4, "big") + o2.to_bytes(4, "big") + o3.to_bytes(4, "big")
        off = i * 16
        d = data[off:off+16]
        out[off] = d[0] ^ ks[0]; out[off+1] = d[1] ^ ks[1]
        out[off+2] = d[2] ^ ks[2]; out[off+3] = d[3] ^ ks[3]
        out[off+4] = d[4] ^ ks[4]; out[off+5] = d[5] ^ ks[5]
        out[off+6] = d[6] ^ ks[6]; out[off+7] = d[7] ^ ks[7]
        out[off+8] = d[8] ^ ks[8]; out[off+9] = d[9] ^ ks[9]
        out[off+10] = d[10] ^ ks[10]; out[off+11] = d[11] ^ ks[11]
        out[off+12] = d[12] ^ ks[12]; out[off+13] = d[13] ^ ks[13]
        out[off+14] = d[14] ^ ks[14]; out[off+15] = d[15] ^ ks[15]
        # counter++
        c3 = (c3 + 1) & 0xffffffff
        if c3 == 0:
            c2 = (c2 + 1) & 0xffffffff
            if c2 == 0:
                c1 = (c1 + 1) & 0xffffffff
                if c1 == 0:
                    c0 = (c0 + 1) & 0xffffffff
    rem = n - blocks * 16
    if rem:
        o0, o1, o2, o3 = enc(c0, c1, c2, c3)
        ks = o0.to_bytes(4, "big") + o1.to_bytes(4, "big") + o2.to_bytes(4, "big") + o3.to_bytes(4, "big")
        off = blocks * 16
        for i in range(rem):
            out[off+i] = data[off+i] ^ ks[i]
    return bytes(out)

def cbc_decrypt(key, iv, data):
    a = AES(key)
    out = bytearray()
    prev = int.from_bytes(iv, "big")
    for off in range(0, len(data) - 15, 16):
        blk = int.from_bytes(data[off:off+16], "big")
        o0, o1, o2, o3 = a.decrypt_block((blk >> 96) & 0xffffffff, (blk >> 64) & 0xffffffff,
                                         (blk >> 32) & 0xffffffff, blk & 0xffffffff)
        dec = (o0 << 96) | (o1 << 64) | (o2 << 32) | o3
        dec ^= prev
        out += dec.to_bytes(16, "big")
        prev = blk
    return bytes(out)

########## 2. 解密与 MP4/CENC 解析 ##########

"""红果片源：地址解密 + 内容密钥还原 + CENC 样本解密"""

import base64, hashlib, struct

# try C 加速
_FAST = None
try:
    from Crypto.Cipher import AES as _CAES
    _FAST = "pycryptodome"
except Exception:
    try:
        from cryptography.hazmat.primitives.ciphers import Cipher as _Cipher, algorithms as _alg, modes as _modes
        _FAST = "cryptography"
    except Exception:
        _FAST = None

SALT = bytes.fromhex("4dd4c2e6b83162090e52b3c7a6733ba41cb2462b829ab58a196b39db57177524f49baf7f08e8d68d26a72e37c1a95a2f1f05a51892aef2949732b62a38aadd58")

def b64d(s):
    s = (s or "").strip()
    s += "=" * (-len(s) % 4)
    return base64.b64decode(s)

def aes_cbc_dec(key, iv, data):
    if _FAST == "pycryptodome":
        return _CAES.new(key, _CAES.MODE_CBC, iv).decrypt(data)
    if _FAST == "cryptography":
        c = _Cipher(_alg.AES(key), _modes.CBC(iv)).decryptor()
        return c.update(data) + c.finalize()
    return cbc_decrypt(key, iv, data)

def aes_ctr_xor(key, nonce, data):
    if _FAST == "pycryptodome":
        return _CAES.new(key, _CAES.MODE_CTR, nonce=b"", initial_value=nonce).decrypt(data)
    if _FAST == "cryptography":
        c = _Cipher(_alg.AES(key), _modes.CTR(nonce)).decryptor()
        return c.update(data) + c.finalize()
    return ctr_xor(key, nonce, data)

def decrypt_main_url(main_url, key_seed):
    """main_url：明文直链 或 0xA8 01 00 头 + AES-128-CBC 密文"""
    raw = b64d(main_url)
    if not raw:
        raise ValueError("empty main_url")
    if raw[0:1] != b"\xa8":
        # 明文
        return raw.decode("utf-8", "ignore")
    if len(raw) < 20 or raw[1] != 1 or raw[2] != 0:
        raise ValueError("播放地址格式异常")
    seed = b64d(key_seed)
    h = hashlib.sha512(hashlib.sha512(seed).digest() + SALT).digest()
    key, iv = h[:16], h[16:32]
    n = (len(raw) - 4) // 16 * 16 + 4
    plain = aes_cbc_dec(key, iv, raw[4:n])
    if plain:
        p = plain[-1]
        if 1 <= p <= 16 and p <= len(plain):
            plain = plain[:-p]
    while plain and plain[-1] == 0:
        plain = plain[:-1]
    return plain.decode("utf-8", "ignore")

def decrypt_content_key(spade_a):
    """spade_a -> 16 字节内容密钥"""
    raw = b64d(spade_a)
    if len(raw) < 3:
        raise ValueError("内容密钥格式异常")
    n = len(raw)
    x = raw[0] ^ raw[1] ^ raw[2]
    end = min(n - x + 0x2F, n - 1)
    if end < 0x21:
        raise ValueError("内容密钥长度异常")
    body = bytearray(raw[1:end + 1])
    ve, vo = 0xF6, 0x55
    for i in range(len(body)):
        b = body[i]
        if i & 1:
            prev = vo
            vo = b
        else:
            prev = ve
            ve = b
        body[i] = ((b ^ prev) + (-0x15 - bin(i).count("1"))) & 0xFF
    hexs = bytes(body[1:0x21])
    key = bytes.fromhex(hexs.decode("ascii"))
    if len(key) != 16:
        raise ValueError("内容密钥长度不为 16")
    return key

# ---------------- MP4 / CENC ----------------

def _boxes(d, start, end):
    i = start
    while i + 8 <= end:
        size = struct.unpack(">I", d[i:i + 4])[0]
        typ = d[i + 4:i + 8]
        hdr = 8
        if size == 1:
            if i + 16 > end:
                return
            size = struct.unpack(">Q", d[i + 8:i + 16])[0]
            hdr = 16
        elif size == 0:
            size = end - i
        if size < hdr or i + size > end:
            return
        yield typ, i, i + hdr, i + size
        i += size

def _child(d, s, e, name):
    for typ, _bs, cs, be in _boxes(d, s, e):
        if typ == name:
            return cs, be
    return None

def _path(d, s, e, names):
    cur = (s, e)
    for nm in names:
        r = _child(d, cur[0], cur[1], nm)
        if not r:
            return None
        cur = r
    return cur

def _u32(d, p):
    return struct.unpack(">I", d[p:p + 4])[0]

_SAMPLE_BOXES = (b"encv", b"enca", b"encs", b"enct", b"senc", b"saiz", b"saio",
                 b"sinf", b"sgpd", b"sbgp", b"saif", b"sdtp")
_REPLACE = {b"encv": b"hvc1", b"enca": b"mp4a", b"senc": b"free", b"saiz": b"free",
            b"saio": b"free", b"sinf": b"free", b"sgpd": b"free", b"sbgp": b"free",
            b"saif": b"free", b"sdtp": b"free", b"encs": b"mp4a", b"enct": b"mp4a"}

def collect_patches(d, start, end, out):
    """递归收集需要改盒类型的位置（只走 moov 内）"""
    for typ, bs, cs, be in _boxes(d, start, end):
        if typ in _REPLACE:
            out.append((bs + 4, _REPLACE[typ]))
        if typ in (b"moov", b"trak", b"mdia", b"minf", b"stbl", b"edts", b"dinf",
                   b"udta", b"mvex", b"stsd"):
            if typ == b"stsd":
                # sample entry 有自己的头部（video 78 / audio 28），先取第一个 entry
                _walk_stsd(d, cs, be, out)
            else:
                collect_patches(d, cs, be, out)

def _walk_stsd(d, s, e, out):
    # stsd payload 前 8 字节是 FullBox(version/flags) 和 entry_count，
    # 真正的 SampleEntry 列表从 s + 8 开始。
    if s + 8 > e:
        return
    for typ, bs, cs, be in _boxes(d, s + 8, e):
        if typ in _REPLACE:
            out.append((bs + 4, _REPLACE[typ]))
            # entry 子盒偏移：VideoSampleEntry 78，AudioSampleEntry 28
            skip = 78 if typ in (b"encv", b"hvc1", b"avc1") else 28
            if cs + skip < be:
                collect_patches(d, cs + skip, be, out)
        elif typ in (b"hvc1", b"hvc2", b"hev1", b"avc1", b"mp4a", b"ac-3", b"ec-3"):
            skip = 78 if typ.startswith((b"hvc", b"hev", b"avc")) else 28
            if cs + skip < be:
                collect_patches(d, cs + skip, be, out)

def parse_track(d, tstart, tend):
    r = _path(d, tstart, tend, [b"mdia", b"minf", b"stbl"])
    if not r:
        return None
    sc, se = r
    info = {"sizes": [], "chunks": [], "stsc": [], "ivs": [], "subs": [],
            "type": None, "count": 0, "encrypted": False}
    for typ, bs, cs, be in _boxes(d, sc, se):
        if typ == b"stsd":
            info["type"] = d[cs + 12:cs + 16].decode("latin1", "replace")
            info["encrypted"] = info["type"] in ("encv", "enca", "encs", "enct")
        elif typ == b"stsz":
            dsz = _u32(d, cs + 4)
            cnt = _u32(d, cs + 8)
            info["count"] = cnt
            if dsz:
                info["sizes"] = [dsz] * cnt
            else:
                info["sizes"] = list(struct.unpack(">%dI" % cnt, d[cs + 12:cs + 12 + 4 * cnt]))
        elif typ == b"stco":
            cnt = _u32(d, cs + 4)
            info["chunks"] = list(struct.unpack(">%dI" % cnt, d[cs + 8:cs + 8 + 4 * cnt]))
        elif typ == b"co64":
            cnt = _u32(d, cs + 4)
            info["chunks"] = list(struct.unpack(">%dQ" % cnt, d[cs + 8:cs + 8 + 8 * cnt]))
        elif typ == b"stsc":
            cnt = _u32(d, cs + 4)
            info["stsc"] = [struct.unpack(">III", d[cs + 8 + i * 12:cs + 8 + i * 12 + 12]) for i in range(cnt)]
        elif typ == b"senc":
            flags = int.from_bytes(d[cs + 1:cs + 4], "big")
            p = cs + 4
            cnt = _u32(d, p)
            p += 4
            ivs, subs = [], []
            for _ in range(cnt):
                ivs.append(bytes(d[p:p + 8]))
                p += 8
                if flags & 2:
                    nsub = struct.unpack(">H", d[p:p + 2])[0]
                    p += 2
                    ent = []
                    for _ in range(nsub):
                        ent.append((struct.unpack(">H", d[p:p + 2])[0], _u32(d, p + 2)))
                        p += 6
                    subs.append(ent)
                else:
                    subs.append(None)
            info["ivs"], info["subs"] = ivs, subs
    sizes, chunks, stsc = info["sizes"], info["chunks"], info["stsc"]
    offsets = []
    if stsc and chunks and sizes:
        si = 0
        k = 0
        for ci, coff in enumerate(chunks):
            while k + 1 < len(stsc) and ci + 1 >= stsc[k + 1][0]:
                k += 1
            pos = coff
            for _ in range(stsc[k][1]):
                if si >= len(sizes):
                    break
                offsets.append(pos)
                pos += sizes[si]
                si += 1
    info["offsets"] = offsets
    return info

def parse_moov(d):
    """返回 (tracks, patches, moov_end)"""
    mv = _child(d, 0, len(d), b"moov")
    if not mv:
        raise ValueError("no moov")
    ms, me = mv
    tracks = []
    for typ, bs, cs, be in _boxes(d, ms, me):
        if typ == b"trak":
            t = parse_track(d, cs, be)
            if t and t["offsets"]:
                tracks.append(t)
    patches = []
    collect_patches(d, ms, me, patches)
    return tracks, patches, me

def decrypt_moov_bytes(buf, base_off, patches):
    """对缓冲区里覆盖到的 patch 位置做盒类型替换"""
    if not patches:
        return buf
    b = bytearray(buf)
    lo, hi = base_off, base_off + len(buf)
    for pos, newt in patches:
        if lo <= pos and pos + 4 <= hi:
            b[pos - lo:pos - lo + 4] = newt
    return bytes(b)

########## 3. 站点接口 ##########

"""红果站点接口（官网 SSR + fqnovel 播放接口）"""

import json, re, time, random, base64

SITE = "https://hongguoduanju.com"
UA_WEB = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
          "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36")
UA_APP = ("com.phoenix.read/73532 (Linux; U; Android 13; zh_CN; 22081212C; "
          "Build/TKQ1.220829.002; Cronet/TTNetVersion:5f296c8c 2023-03-29)")

HOSTS = ["api5-normal-sinfonlineb.fqnovel.com", "api5-normal-lq.fqnovel.com",
         "api5-normal-sinfonlinea.fqnovel.com", "api5-normal-hl.fqnovel.com",
         "api5-normal-lf.fqnovel.com", "api5-normal-sinfonlinec.fqnovel.com"]

_CARD_RE = re.compile(r'<a[^>]*href="/detail\?series_id=(\d+)"[^>]*>(.*?)</a>', re.S)
_TITLE_RE = re.compile(r'<p[^>]*class="[^"]*(?:pc-title|m-title)[^"]*"[^>]*>(.*?)</p>', re.S)
_IMG_RE = re.compile(r'<img[^>]*src="([^"]+)"', re.S)
_EP_RE = re.compile(r'<p[^>]*class="[^"]*(?:pc-episode|m-episode)[^"]*"[^>]*>(.*?)</p>', re.S)

# 封面：卡片里同时存在"懒加载占位图"和"真封面"两个 img，必须跳过占位图
_IMG_TAG_RE = re.compile(r'<img\b[^>]*>', re.S)
_SRC_ATTR_RE = re.compile(r'\bsrc\s*=\s*"([^"]*)"', re.S)
_SRCSET_ATTR_RE = re.compile(r'\bsrc[Ss]et\s*=\s*"([^"]*)"', re.S)
_BG_URL_RE = re.compile(r'background-image\s*:\s*url\(\s*["\']?([^"\')]+)', re.S)
_PIC_BAD = ("empty_play", "empty_pic", "empty-img", "/loading/", "load_fail",
            "placeholder", "default_pic", "no-pic", "no_pic", "blank.png")


def _pic_ok(u):
    if not u:
        return False
    u = u.strip()
    if not u or u.startswith("data:") or u.startswith("blob:"):
        return False
    low = u.lower()
    for b in _PIC_BAD:
        if b in low:
            return False
    return low.startswith("http://") or low.startswith("https://") or low.startswith("//")


def _pick_pic(inner):
    """从卡片 HTML 里挑出真封面地址（跳过懒加载占位灰图）"""
    # 1) img 标签：跳过带 empty 类名 / 占位地址的
    for tag in _IMG_TAG_RE.findall(inner):
        low = tag.lower()
        if "empty" in low or ("class=" in low and "loading" in low and "pc-img" not in low):
            # 类名明确是占位图，除非它的 src 看着像正经封面
            m = _SRC_ATTR_RE.search(tag)
            if not (m and _pic_ok(m.group(1)) and "empty" not in m.group(1).lower()):
                continue
        m = _SRC_ATTR_RE.search(tag)
        if m and _pic_ok(m.group(1)):
            return _abs_pic(m.group(1))
    # 2) picture > source srcSet
    for ss in _SRCSET_ATTR_RE.findall(inner):
        for part in ss.split(","):
            u = part.strip().split(" ")[0]
            if _pic_ok(u):
                return _abs_pic(u)
    # 3) 背景图兜底
    for u in _BG_URL_RE.findall(inner):
        if _pic_ok(u):
            return _abs_pic(u)
    # 4) 任意 src 兜底（含占位图也认，总比空着强）
    m = _IMG_RE.search(inner)
    return _abs_pic(m.group(1)) if m else ""


def _abs_pic(u):
    u = (u or "").strip().replace("&amp;", "&").replace("&#x2F;", "/")
    if u.startswith("//"):
        u = "https:" + u
    return u

class Http(object):
    def __init__(self):
        self.s = None
        self.booted = 0

    def session(self):
        if self.s is None:
            try:
                import requests
                self.s = requests.Session()
                self.s.headers.update({"User-Agent": UA_WEB,
                                       "Accept-Language": "zh-CN,zh;q=0.9",
                                       "Accept": "text/html,application/xhtml+xml,*/*"})
            except Exception:
                self.s = False
        return self.s

    def _urllib(self, url, headers=None, data=None, timeout=20):
        try:
            from urllib.request import Request, urlopen
        except Exception:
            from urllib2 import Request, urlopen
        h = {"User-Agent": UA_WEB}
        if headers:
            h.update(headers)
        req = Request(url, data=data, headers=h)
        resp = urlopen(req, timeout=timeout)
        return resp.read()

    def get(self, url, headers=None, timeout=20):
        s = self.session()
        if s:
            r = s.get(url, headers=headers, timeout=timeout)
            return r.text
        raw = self._urllib(url, headers, None, timeout)
        return raw.decode("utf-8", "ignore")

    def get_bytes(self, url, headers=None, timeout=30, rng=None):
        s = self.session()
        h = dict(headers or {})
        if rng:
            h["Range"] = "bytes=%d-%d" % rng
        if s:
            r = s.get(url, headers=h, timeout=timeout)
            return r.content
        return self._urllib(url, h, None, timeout)

    def post_json(self, url, payload, headers=None, timeout=20):
        body = json.dumps(payload).encode("utf-8")
        s = self.session()
        h = {"User-Agent": UA_APP, "Content-Type": "application/json; charset=utf-8",
             "Accept": "application/json"}
        if headers:
            h.update(headers)
        if s:
            r = s.post(url, data=body, headers=h, timeout=timeout)
            return r.text
        raw = self._urllib(url, h, body, timeout)
        return raw.decode("utf-8", "ignore")

    def boot(self):
        """访问首页拿 ttwid，搜索接口需要"""
        if self.booted and time.time() - self.booted < 3600:
            return
        try:
            self.get(SITE + "/")
            self.booted = time.time()
        except Exception:
            pass

H = Http()

def _clean(t):
    t = re.sub(r"<[^>]+>", "", t or "")
    return t.replace("&amp;", "&").replace("&quot;", '"').replace("&#x27;", "'").strip()

def _parse_cards(html):
    out = []
    seen = set()
    for m in _CARD_RE.finditer(html):
        sid, inner = m.group(1), m.group(2)
        if sid in seen:
            continue
        seen.add(sid)
        tm = _TITLE_RE.search(inner)
        im_pic = _pick_pic(inner)
        em = _EP_RE.search(inner)
        name = _clean(tm.group(1)) if tm else ""
        if not name:
            am = re.search(r'aria-label="(?:查看)?([^"]+)"', m.group(0))
            if am:
                name = _clean(am.group(1))
        if not name:
            continue
        out.append({
            "vod_id": sid,
            "vod_name": name,
            "vod_pic": im_pic,
            "vod_remarks": _clean(em.group(1)) if em else "",
        })
    return out

def categories():
    """从 /category 页解析分类树（主分类 + 子标签）"""
    html = H.get(SITE + "/category")
    cats = []
    seen = set()

    def add(href, name):
        tid = href.replace("/category/", "").strip("/")
        if not tid or tid in seen or not name:
            return
        # 漫画走 /comic/xxx 的图片阅读页，TVBox 播不了，直接不放进分类树
        if tid.split("/")[0] == "comic":
            return
        seen.add(tid)
        cats.append({"type_id": tid, "type_name": _clean(name)})

    for m in re.finditer(r'href="(/category/[a-z0-9\-]+)"[^>]*class="pc-content-type[^"]*"[^>]*>\s*<span[^>]*>([^<]+)</span>', html):
        add(m.group(1), m.group(2))
    for m in re.finditer(r'href="(/category/[a-z0-9\-/]+)"[^>]*class="pc-tag[^"]*"[^>]*>([^<]{1,10})<', html):
        add(m.group(1), m.group(2))
    for m in re.finditer(r'href="(/category/[a-z0-9\-/]+)"[^>]*>([^<]{1,10})<', html):
        add(m.group(1), m.group(2))
    return cats

def home_list():
    return _parse_cards(H.get(SITE + "/"))

def category_list(tid, page):
    url = "%s/category/%s?page=%d" % (SITE, tid.strip("/"), max(1, int(page)))
    return _parse_cards(H.get(url))

def search_list(key, page):
    H.boot()
    url = "%s/api/search/result?query=%s&page=%d" % (SITE, quote(key), max(1, int(page)))
    txt = H.get(url, headers={"Accept": "application/json", "Referer": SITE + "/"})
    try:
        j = json.loads(txt)
    except Exception:
        return []
    items = j.get("searchList") or []
    out = []
    for it in items:
        vd = it.get("video_data") or {}
        sid = vd.get("series_id") or it.get("keyword")
        if not sid or not str(sid).isdigit():
            continue
        name = it.get("name") or vd.get("series_name") or ""
        cover = vd.get("series_cover") or ""
        cnt = vd.get("episode_cnt") or 0
        out.append({
            "vod_id": str(sid),
            "vod_name": _clean(name),
            "vod_pic": cover.replace("\\u002F", "/"),
            "vod_remarks": ("全%s集" % cnt) if cnt else "",
        })
    return out

def detail(sid):
    html = H.get("%s/detail?series_id=%s" % (SITE, sid))
    data = {"vod_id": str(sid), "vod_name": "", "vod_pic": "", "vod_content": "",
            "vod_remarks": "", "vids": []}
    m = re.search(r'"seriesDetail":\{(.*?)\}\s*,\s*"', html, re.S)
    blob = m.group(1) if m else html
    def _field(k):
        mm = re.search(r'"%s":"(.*?)"' % k, blob, re.S)
        return mm.group(1) if mm else ""
    name = _field("series_name")
    cover = _field("series_cover").replace("\\u002F", "/")
    if (not cover) or (not _pic_ok(cover)):
        # 详情字段缺失或被塞了占位图时，从 meta / 页面里找真封面
        mo = re.search(r'<meta[^>]+property="og:image"[^>]+content="([^"]+)"', html)
        if mo and _pic_ok(mo.group(1)):
            cover = mo.group(1)
        else:
            cover = _pick_pic(html) or cover
    intro = _field("series_intro").replace("\\u002F", "/").replace("\\n", "\n")
    cnt = _field("episode_cnt")
    vl = re.search(r'"vid_list":\[(.*?)\]', html, re.S)
    vids = re.findall(r'"(\d{8,})"', vl.group(1)) if vl else []
    if not name:
        m2 = re.search(r'"series_name":"(.*?)"', html, re.S)
        name = m2.group(1) if m2 else ("剧集 %s" % sid)
    data["vod_name"] = name
    data["vod_pic"] = cover
    data["vod_content"] = intro
    data["vod_remarks"] = ("全%s集" % cnt) if cnt else ("%d集" % len(vids))
    data["vids"] = vids
    return data

_VM_CACHE = {}
_VM_TTL = 900
_GOOD_HOST = []          # 记住能出数据的 host，下次优先打

def _hosts_order():
    return list(_GOOD_HOST) + [h for h in HOSTS if h not in _GOOD_HOST]

def video_model(vid, timeout=10, max_hosts=0, budget=7.0):
    """播放模型：多 host + 多轮重试（接口约三成概率回空/报错），带缓存。

    成功结果按 vid 缓存，详情页探测过的集，点播放时零请求直接出地址。
    """
    vid = str(vid)
    now = time.time()
    hit = _VM_CACHE.get(vid)
    if hit and now - hit[0] < _VM_TTL:
        return hit[1]
    body = {"biz_param": {"detail_page_version": 0, "device_level": 4,
                          "disable_digg_stat": False, "need_all_video_definition": True,
                          "need_mp4_align": False, "use_os_player": False,
                          "use_server_dns": False, "video_platform": 1024},
            "mixed_video_id_map": {"1004": [str(vid)]}}
    hosts = _hosts_order()[:max_hosts or None]
    last = None
    started = time.time()
    tries = 0
    for rnd in range(3):
        if not hosts:
            break
        for host in hosts:
            if tries >= 7 or time.time() - started > budget:
                break
            tries += 1
            dev = "".join([str(random.randint(0, 9)) for _ in range(18)])
            qs = "?aid=8662&device_platform=android&device_id=%s" % dev
            try:
                txt = H.post_json("https://%s/novel/player/multi_video_model/v1/%s"
                                  % (host, qs), body, timeout=timeout)
                if not (txt or "").strip():
                    last = "empty body"
                else:
                    j = json.loads(txt)
                    d = (j.get("data") or {}).get(str(vid))
                    if j.get("code") not in (0, None):
                        last = "code=%s" % j.get("code")
                    elif not d:
                        last = "empty data"
                    else:
                        vm = d.get("video_model")
                        vm = json.loads(vm) if isinstance(vm, str) else vm
                        if not vm or not vm.get("video_list"):
                            last = "no video_list"
                        else:
                            if host not in _GOOD_HOST:
                                _GOOD_HOST.insert(0, host)
                                del _GOOD_HOST[3:]
                            _VM_CACHE[vid] = (now, vm)
                            if len(_VM_CACHE) > 60:
                                for k in sorted(_VM_CACHE, key=lambda x: _VM_CACHE[x][0])[:30]:
                                    _VM_CACHE.pop(k, None)
                            return vm
            except Exception as e:
                last = str(e)
            time.sleep(0.15 + random.random() * 0.15)
        time.sleep(0.35)
    raise IOError("播放接口暂不可用: %s" % (last or "unknown"))


DEF_RANK = {"2160p": 0, "1440p": 1, "1080p": 2, "720p": 3, "540p": 4,
            "480p": 5, "360p": 6, "240p": 7}


def _norm_definition(value):
    """兼容接口把清晰度放在 definition 或 video_list 的 key 中的情况。"""
    if value is None:
        return ""
    if isinstance(value, (int, float)):
        value = str(int(value)) if float(value).is_integer() else str(value)
    d = str(value).strip().lower()
    d = d.replace(" ", "").replace("_", "").replace("-", "")
    if not d:
        return ""
    # 常见接口会返回 1080、1080P、video_1080p、4k、fhd 等不同写法。
    for n in ("2160", "1440", "1080", "720", "540", "480", "360", "240"):
        if re.search(r"(?<!\d)%s(?:p)?(?!\d)" % n, d):
            return n + "p"
    if d in ("4k", "uhd"):
        return "2160p"
    if d in ("fhd", "fullhd", "fullhighdefinition"):
        return "1080p"
    if d in ("hd", "highdefinition"):
        return "720p"
    return d


def _def_label(d):
    d = _norm_definition(d)
    if d.endswith("p") and d[:-1].isdigit():
        return d[:-1] + "P"
    return (d or "自动").upper()


def pick_defs(vm, key_seed):
    """拆分播放档位；definition 缺失时从 video_list 的 key 推断。"""
    if not isinstance(vm, dict):
        return []
    video_list = vm.get("video_list") or {}
    if not isinstance(video_list, dict):
        return []
    out, seen = [], set()
    for k, v in video_list.items():
        if not isinstance(v, dict) or not v.get("main_url"):
            continue
        try:
            url = decrypt_main_url(v.get("main_url"), key_seed or "")
        except Exception:
            continue
        if not isinstance(url, str) or not url.startswith(("http://", "https://")):
            continue
        enc, key = False, None
        if v.get("encrypt") and v.get("spade_a"):
            try:
                key = decrypt_content_key(v["spade_a"])
                enc = bool(key)
            except Exception:
                key = None
        d = _norm_definition(v.get("definition")) or _norm_definition(k)
        # 无法识别档位时仍保留线路，但不让多个空标签互相覆盖。
        identity = d or str(k)
        if identity in seen:
            continue
        seen.add(identity)
        out.append({"def": d, "label": _def_label(d), "url": url, "key": key,
                    "enc": enc, "rank": DEF_RANK.get(d, 9),
                    "order": 0 if not enc else 1})
    out.sort(key=lambda x: (x["rank"], x["order"]))
    return out

def vid_defs(vid):
    """vid -> 档位列表（带缓存）"""
    vm = video_model(vid)
    return pick_defs(vm, vm.get("key_seed") or "")

########## 4. 本地解密代理 ##########

"""本地 CENC 解密代理：把加密 mp4 实时解成明文流，支持 Range / seek"""

import os, re, socket, threading, time, base64, hashlib

UA = ("Mozilla/5.0 (Linux; Android 13; zh_CN) AppleWebKit/537.36 (KHTML, like Gecko) "
      "Chrome/120.0 Mobile Safari/537.36")

_BLOCK = 262144              # 单块 256KB：首字节更快，seek 粒度更细
_CACHE_MAX = 10 * 1024 * 1024
_CDN_S = None


def _cdn_session():
    """CDN 专用连接池（keep-alive 复用，省掉每次 Range 的握手）"""
    global _CDN_S
    if _CDN_S is None:
        try:
            import requests
            s = requests.Session()
            ad = requests.adapters.HTTPAdapter(pool_connections=8, pool_maxsize=24)
            s.mount("https://", ad)
            s.mount("http://", ad)
            _CDN_S = s
        except Exception:
            _CDN_S = False
    return _CDN_S


def _fetch_ex(url, a, b, timeout=25):
    """取区间，返回 (data, total_size_or_None)"""
    headers = {"User-Agent": UA, "Range": "bytes=%d-%d" % (a, b),
               "Accept-Encoding": "identity"}
    s = _cdn_session()
    if s:
        r = s.get(url, headers=headers, timeout=timeout)
        code = r.status_code
        if code not in (200, 206):
            raise IOError("HTTP %d" % code)
        body = r.content
        total = None
        cr = r.headers.get("Content-Range") or ""
        m = re.search(r"bytes\s+(\d+)-(\d+)/(\d+)", cr)
        if m:
            if int(m.group(1)) != a:
                raise IOError("range start mismatch")
            total = int(m.group(3))
            expected = min(b, total - 1) - a + 1
            if expected < 0 or len(body) != expected:
                raise IOError("range length mismatch")
        elif code == 200:
            total = len(body)
            if a > 0:
                body = body[a:a + (b - a + 1)]
            else:
                body = body[:b + 1]
        else:
            raise IOError("missing Content-Range")
        try:
            r.close()
        except Exception:
            pass
        return body, total
    from urllib.request import Request, urlopen
    req = Request(url, headers=headers)
    r = urlopen(req, timeout=timeout)
    body = r.read()
    total = None
    cr = r.headers.get("Content-Range") or ""
    m = re.search(r"bytes\s+(\d+)-(\d+)/(\d+)", cr)
    if m:
        if int(m.group(1)) != a:
            raise IOError("range start mismatch")
        total = int(m.group(3))
        expected = min(b, total - 1) - a + 1
        if expected < 0 or len(body) != expected:
            raise IOError("range length mismatch")
    elif r.status == 200:
        total = len(body)
        body = body[a:a + (b - a + 1)]
    else:
        raise IOError("missing Content-Range")
    return body, total


def _fetch(url, a, b, timeout=25):
    """取区间（含两端），失败重试"""
    err = None
    for i in range(3):
        try:
            return _fetch_ex(url, a, b, timeout)[0]
        except Exception as e:
            err = e
            if i < 2:
                time.sleep(0.15 * (i + 1))
    raise IOError("取流失败: %s" % (err,))


def _content_length(url):
    try:
        _d, total = _fetch_ex(url, 0, 0, timeout=15)
        if total:
            return total
    except Exception:
        pass
    try:
        import requests
        r = requests.head(url, headers={"User-Agent": UA}, timeout=15, allow_redirects=True)
        cl = r.headers.get("Content-Length")
        return int(cl) if cl else None
    except Exception:
        return None


def _parse_moov_any(d, size=None, url=None):
    """解析 moov，moov 不在缓冲区开头时按字节扫描兜底"""
    try:
        t, p, me = parse_moov(d)
        if t:
            return t, p, me
    except Exception:
        pass
    idx = d.find(b"moov")
    while idx >= 4:
        st = idx - 4
        try:
            t, p, me = parse_moov(d[st:])
            if t:
                return t, [(x + st, y) for x, y in p], me + st
        except Exception:
            pass
        idx = d.find(b"moov", idx + 4)
    # moov 在文件尾部时再拉一段
    if url and size and size > len(d):
        ta = max(0, size - 2 * 1024 * 1024)
        tail = _fetch(url, ta, size - 1)
        idx = tail.find(b"moov")
        while idx >= 4:
            st = idx - 4
            try:
                t, p, me = parse_moov(tail[st:])
                if t:
                    return t, [(x + ta + st, y) for x, y in p], me + ta + st
            except Exception:
                pass
            idx = tail.find(b"moov", idx + 4)
    raise ValueError("no moov")


class Session(object):
    """一个视频文件的解密会话：解析样本表、预取首块、按区间输出明文"""

    def __init__(self, url, key):
        self.url = url
        self.key = key
        self.ts = time.time()
        self.blk = {}
        self.blk_bytes = 0
        self.lk = threading.Lock()
        self.samples = []
        head, size = _fetch_ex(url, 0, 1048575)
        self.size = size
        if not self.size:
            self.size = _content_length(url)
        tracks, patches, moov_end = _parse_moov_any(head, self.size, url)
        if moov_end > len(head):
            try:
                more = _fetch(url, 0, moov_end - 1)
                tracks, patches, moov_end = _parse_moov_any(more, self.size, url)
                head = more
            except Exception:
                pass
        self.tracks = tracks
        self.patches = patches
        self.moov_end = moov_end
        samples = []
        for t in tracks:
            if not t.get("encrypted"):
                continue
            sizes = t.get("sizes") or []
            for i, off in enumerate(t.get("offsets") or []):
                if i >= len(t["ivs"]) or i >= len(sizes):
                    break
                samples.append((off, sizes[i], t["ivs"][i]))
        samples.sort()
        self.samples = samples
        self.starts = [s[0] for s in samples]
        # 预热：第一块先解出来，首播请求直接命中内存
        if self.samples:
            try:
                self._block_at(0)
            except Exception:
                pass

    # ---- 样本区 ----
    def index_of(self, pos):
        import bisect
        i = bisect.bisect_right(self.starts, pos) - 1
        if i < 0:
            return -1
        off, size, _iv = self.samples[i]
        return i if pos < off + size else -1

    def next_start(self, pos):
        import bisect
        i = bisect.bisect_right(self.starts, pos)
        return self.starts[i] if i < len(self.starts) else None

    def _cache_put(self, k, lo, data):
        with self.lk:
            old = self.blk.get(k)
            if old is not None:
                self.blk_bytes -= len(old[1])
            self.blk[k] = (lo, data)
            self.blk_bytes += len(data)
            while self.blk_bytes > _CACHE_MAX and len(self.blk) > 1:
                old = sorted(self.blk.items(), key=lambda kv: kv[1][0])[0][0]
                if old == k:
                    break
                _o, d = self.blk.pop(old)
                self.blk_bytes -= len(d)

    def _block_at(self, i):
        """按原文件偏移解密样本；样本之间的间隙必须原样保留。"""
        with self.lk:
            v = self.blk.get(i)
            if v is not None:
                return v
        n = len(self.samples)
        j = i
        total = 0
        lo = self.samples[i][0]
        # 同一块限制总样本量和原文件跨度，避免跨越很大的音视频交错区间。
        while j < n and total < _BLOCK:
            off, size, _iv = self.samples[j]
            if j > i and off + size - lo > _BLOCK * 4:
                break
            total += size
            j += 1
        if j == i:
            j = i + 1
        last_off, last_size, _iv = self.samples[j - 1]
        hi = last_off + last_size - 1
        raw = _fetch(self.url, lo, hi)
        if len(raw) != hi - lo + 1:
            raise IOError("样本区间长度不完整")
        # 不能把不同 sample 拼接：MP4 的 chunk/sample 在文件中可能交错，
        # 拼接会改变原始 byte offset，Range/seek 读取就会错位。
        buf = bytearray(raw)
        for k in range(i, j):
            off, size, iv = self.samples[k]
            start = off - lo
            end = start + size
            if start < 0 or end > len(buf):
                raise IOError("样本偏移超出取流范围")
            chunk = bytes(buf[start:end])
            plain = aes_ctr_xor(self.key, iv + b"\x00" * 8, chunk)
            if len(plain) != size:
                raise IOError("样本解密长度异常")
            buf[start:end] = plain
        data = bytes(buf)
        self._cache_put(i, lo, data)
        return lo, data

    def _raw_at(self, pos, end):
        """非样本区（moov / 索引头等）：直接透传并按需改盒类型"""
        k = ("r", pos, end)
        with self.lk:
            v = self.blk.get(k)
            if v is not None:
                return v[1]
        data = _fetch(self.url, pos, end)
        data = decrypt_moov_bytes(data, pos, self.patches)
        self._cache_put(k, pos, data)
        return data

    def stream(self, a, b, write):
        if not self.samples:
            pos = a
            while pos <= b:
                end = min(b, pos + _BLOCK - 1)
                write(_fetch(self.url, pos, end))
                pos = end + 1
            return
        pos = a
        guard = 0
        while pos <= b:
            guard += 1
            if guard > 200000:
                break
            i = self.index_of(pos)
            if i < 0:
                nxt = self.next_start(pos)
                end = min(b, (nxt - 1) if nxt else b)
                if end < pos:
                    break
                while pos <= end:
                    e2 = min(end, pos + _BLOCK - 1)
                    write(self._raw_at(pos, e2))
                    pos = e2 + 1
                continue
            lo, data = self._block_at(i)
            s0 = max(pos, lo)
            s1 = min(b, lo + len(data) - 1)
            if s1 < s0:
                pos = lo + len(data)
                continue
            write(data[s0 - lo:s1 - lo + 1])
            pos = s1 + 1


class Proxy(object):
    def __init__(self):
        self.port = 0
        self.sessions = {}
        self.locks = {}
        self.guard = threading.Lock()
        self.started = False
        self.srv = None

    def session(self, url, key):
        """同一 URL+密钥只建一次，避免错误复用另一档的解密会话。"""
        cache_key = (url, bytes(key or b""))
        with self.guard:
            s = self.sessions.get(cache_key)
            if s is not None and s.size:
                s.ts = time.time()
                return s
            lk = self.locks.get(cache_key)
            if lk is None:
                lk = threading.Lock()
                self.locks[cache_key] = lk
        with lk:
            with self.guard:
                s = self.sessions.get(cache_key)
                if s is not None and s.size:
                    s.ts = time.time()
                    return s
            s = Session(url, key)
            s.ts = time.time()
            with self.guard:
                self.sessions[cache_key] = s
                if len(self.sessions) > 20:
                    old = sorted(self.sessions.items(), key=lambda kv: kv[1].ts)[:10]
                    for k, _v in old:
                        self.sessions.pop(k, None)
                        # 锁对象可能仍被等待线程持有，不能在这里删除。
            return s

    def prepare(self, video_url, key):
        """提前把会话建好（首播零等待的关键）"""
        try:
            self.start()
            self.session(video_url, key)
            return True
        except Exception:
            return False

    def start(self):
        if self.started:
            return self.port
        from socketserver import ThreadingMixIn, TCPServer
        from http.server import BaseHTTPRequestHandler

        outer = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"
            timeout = 60

            def setup(self):
                BaseHTTPRequestHandler.setup(self)
                try:
                    self.connection.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
                except Exception:
                    pass

            def log_message(self, *a):
                pass

            def do_HEAD(self):
                self._serve(head=True)

            def do_GET(self):
                self._serve(head=False)

            def _serve(self, head=False):
                try:
                    q = parse_qs(urlparse(self.path).query)
                    if "u" not in q:
                        self.send_error(400)
                        return
                    u = q["u"][0]
                    u = base64.urlsafe_b64decode(u + "=" * (-len(u) % 4)).decode("utf-8")
                    key = bytes.fromhex(q.get("k", [""])[0])
                    sess = outer.session(u, key)
                    size = int(sess.size or 0)
                    if size <= 0:
                        self.send_error(502)
                        return
                    a, b, partial = 0, size - 1, False
                    rng = (self.headers.get("Range") or "").strip()
                    if rng:
                        m = re.match(r"bytes\s*=\s*(\d*)-(\d*)", rng, re.I)
                        if m:
                            partial = True
                            if m.group(1):
                                a = int(m.group(1))
                                b = int(m.group(2)) if m.group(2) else size - 1
                            elif m.group(2):
                                n = int(m.group(2))
                                a = max(0, size - n)
                                b = size - 1
                            else:
                                a, b = 0, size - 1
                    if a >= size:
                        self.send_response(416)
                        self.send_header("Content-Range", "bytes */%d" % size)
                        self.send_header("Content-Length", "0")
                        self.end_headers()
                        return
                    b = min(b, size - 1)
                    if b < a:
                        b = size - 1
                    self.send_response(206 if partial else 200)
                    self.send_header("Content-Type", "video/mp4")
                    self.send_header("Accept-Ranges", "bytes")
                    self.send_header("Content-Length", str(b - a + 1))
                    if partial:
                        self.send_header("Content-Range", "bytes %d-%d/%d" % (a, b, size))
                    self.send_header("Cache-Control", "no-store")
                    self.send_header("Connection", "close")
                    self.end_headers()
                    self.close_connection = True
                    if head:
                        return
                    sess.stream(a, b, self.wfile.write)
                    try:
                        self.wfile.flush()
                    except Exception:
                        pass
                except (BrokenPipeError, ConnectionResetError):
                    pass
                except Exception:
                    try:
                        self.send_error(502)
                    except Exception:
                        pass

        class Srv(ThreadingMixIn, TCPServer):
            allow_reuse_address = True
            daemon_threads = True
            request_queue_size = 64

        for p in range(9980, 10060):
            try:
                srv = Srv(("127.0.0.1", p), Handler)
            except OSError:
                continue
            self.port = p
            self.srv = srv
            self.started = True
            t = threading.Thread(target=srv.serve_forever)
            t.daemon = True
            t.start()
            return self.port
        return 0

    def url_for(self, video_url, key):
        self.start()
        if not self.port:
            raise IOError("本地解密代理启动失败")
        # 必须先成功建立并解析会话；不能把尚未就绪的代理地址交给播放器。
        self.session(video_url, key)
        u = base64.urlsafe_b64encode(video_url.encode("utf-8")).decode("ascii").rstrip("=")
        return "http://127.0.0.1:%d/v?u=%s&k=%s&t=%d" % (self.port, u, key.hex(), int(time.time()))

PROXY = Proxy()

########## 5. TVBox 入口 ##########

VOD_PIC = "https://p6-novel.byteimg.com/novel-pic/"

# 接口通常返回这四档；探测失败时按这个顺序出线路，点哪条都行（不存在的高档会就近回落）
STD_DEFS = ["2160p", "1440p", "1080p", "720p", "540p", "480p", "360p"]


class Spider(object):

    def init(self, extend=""):
        self.extend = extend or ""
        self.inited = True
        # 加载源时就把代理端口拉起来，别等第一次播放
        try:
            PROXY.start()
        except Exception:
            pass
        return None

    # ---------- 首页 ----------
    def homeContent(self, filter):
        result = {}
        try:
            cls = categories()
        except Exception:
            cls = [{"type_id": "real-drama", "type_name": "真人剧"}]
        result["class"] = cls
        result["filters"] = {}
        return result

    def homeVideoContent(self):
        vods = []
        try:
            vods = _parse_cards(H.get(SITE + "/rank/hot-drama"))
        except Exception:
            pass
        if not vods:
            try:
                vods = home_list()
            except Exception:
                vods = []
        return {"list": vods}

    # ---------- 分类 ----------
    def categoryContent(self, tid, pg, filter, extend):
        page = int(pg or 1)
        vods = []
        try:
            vods = category_list(tid, page)
        except Exception:
            vods = []
        return {"list": vods, "page": page,
                "pagecount": 999 if len(vods) >= 20 else page,
                "limit": 24, "total": 99999 if len(vods) >= 20 else len(vods)}

    # ---------- 详情 ----------
    def _defs_for(self, vid):
        """探测某一集的清晰度档位（带缓存，失败给默认档）"""
        try:
            items = vid_defs(vid)
            if items:
                return items
        except Exception:
            pass
        return [{"def": d, "label": _def_label(d), "url": "", "key": None,
                 "enc": False, "rank": DEF_RANK.get(d, 9), "order": 1} for d in STD_DEFS]

    def _warm(self, vid, item):
        """后台预热第一集：会话建好、首块解好，用户点播放就是秒开"""
        def run():
            try:
                if item.get("enc") and item.get("key") and item.get("url"):
                    PROXY.prepare(item["url"], item["key"])
            except Exception:
                pass
        t = threading.Thread(target=run)
        t.daemon = True
        t.start()

    def detailContent(self, ids):
        sid = str(ids[0]) if isinstance(ids, (list, tuple)) else str(ids)
        d = detail(sid)
        vids = d.get("vids") or []
        vod = {
            "vod_id": sid,
            "vod_name": d.get("vod_name") or sid,
            "vod_pic": d.get("vod_pic") or "",
            "vod_remarks": d.get("vod_remarks") or "",
            "vod_content": d.get("vod_content") or "",
            "vod_year": "",
            "vod_area": "大陆",
            "type_name": "短剧",
        }
        if not vids:
            vod["vod_play_from"] = "红果"
            vod["vod_play_url"] = ""
            return {"list": [vod]}
        # 探测档位（只试两个节点、短超时，别把详情页拖住）
        defs = []
        try:
            vm = video_model(vids[0], timeout=4, max_hosts=2, budget=4.0)
            defs = pick_defs(vm, vm.get("key_seed") or "")
        except Exception:
            defs = []
        if not defs:
            defs = self._defs_for(vids[0])
        multi = len(defs) > 1
        froms, urls = [], []
        for it in defs:
            label = ("红果" + it["label"]) if multi else "红果"
            tag = it["def"] if multi else ""
            eps = []
            for n in range(len(vids)):
                eps.append("第%d集$%s%s" % (n + 1, vids[n], ("|" + tag) if tag else ""))
            froms.append(label)
            urls.append("#".join(eps))
        vod["vod_play_from"] = "$$$".join(froms)
        vod["vod_play_url"] = "$$$".join(urls)
        # 默认线路（最高档）先热起来
        self._warm(vids[0], defs[0])
        return {"list": [vod]}

    # ---------- 搜索 ----------
    def searchContent(self, key, quick, pg="1"):
        page = int(pg or 1)
        try:
            vods = search_list(key, page)
        except Exception:
            vods = []
        return {"list": vods, "page": page, "pagecount": 99 if vods else page,
                "limit": 24, "total": 9999}

    # ---------- 播放 ----------
    def playerContent(self, flag, id, vipFlags):
        result = {"parse": 0, "playUrl": "", "url": "", "header": {"User-Agent": UA_WEB}}
        raw = str(id or "").strip()
        vid, tag = raw, ""
        for sep in ("|", "@"):
            if sep in raw:
                vid, tag = raw.split(sep, 1)
                break
        vid, tag = vid.strip(), tag.strip().lower()
        if not vid.isdigit():
            return result
        items = []
        try:
            items = vid_defs(vid)
        except Exception:
            items = []
        if not items:
            return result
        if tag:
            cand = [x for x in items if x["def"] == tag]
            if not cand:
                # 该档不存在就按清晰度就近回落，别让用户点了个空
                rk = DEF_RANK.get(tag, 9)
                cand = sorted(items, key=lambda x: abs(x["rank"] - rk))[:1] or items
        else:
            cand = items
        target = cand[0]
        url = target["url"]
        if target.get("enc") and target.get("key"):
            try:
                url = PROXY.url_for(target["url"], target["key"])
            except Exception:
                # 加密流不能回退到原始密文 URL，否则播放器只会持续转圈。
                return result
        result["url"] = url
        result["header"] = {"User-Agent": UA_WEB, "Referer": SITE + "/"}
        return result


# ---------------- 命令行自测（不影响 TVBox 加载） ----------------
if __name__ == "__main__":
    import sys as _sys
    _sp = Spider()
    _sp.init("")
    _cmd = _sys.argv[1] if len(_sys.argv) > 1 else "selftest"
    if _cmd == "selftest":
        print("分类数:", len(_sp.homeContent(False)["class"]))
        print("首页推荐:", len(_sp.homeVideoContent()["list"]))
        print("分类列表:", len(_sp.categoryContent("real-drama/urban", 1, False, {})["list"]))
        _d = _sp.detailContent(["7686713195246930968"])["list"][0]
        print("详情:", _d["vod_name"], "线路:", _d["vod_play_from"])
        print("集数:", [len(x.split("#")) for x in _d["vod_play_url"].split("$$$")])
        print("搜索:", len(_sp.searchContent("逆袭", "", 1)["list"]))
    elif _cmd == "defs" and len(_sys.argv) > 2:
        _d = _sp.detailContent([_sys.argv[2]])["list"][0]
        print("线路:", _d["vod_play_from"])
        print(_d["vod_play_url"].split("$$$")[0].split("#")[0])
    elif _cmd == "play" and len(_sys.argv) > 2:
        _r = _sp.playerContent("", _sys.argv[2], [])
        print("代理地址:", _r["url"])
        print("用播放器打开上面的地址即可（保持本进程运行）")
        while True:
            time.sleep(3600)
