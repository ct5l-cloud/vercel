#!/usr/bin/env node

const http = require('http');
const fs = require('fs');
const net = require('net');
const path = require('path');
const { createHash, createHmac, createCipheriv, createDecipheriv, timingSafeEqual, randomBytes } = require('crypto');
const { Buffer } = require('buffer');
const axios = require('axios');
const { WebSocket, createWebSocketStream } = require('ws');

// ========================== Environment ==========================
const UUID = process.env.UUID || 'd1cf4b9c-3e57-085d-b34a-797fcf601381';
// Default dibuat 'vercel' sesuai request form Web UI
const SUB_PATH = process.env.SUB_PATH || 'vercel';
const NAME = process.env.NAME || 'Vercel-Node';
const PORT = process.env.PORT || 3000;

const SHOW_LOG = !!(process.env.SHOW_LOG);
function log(...args) { if (SHOW_LOG) console.log(...args); }
function logErr(...args) { if (SHOW_LOG) console.error(...args); }

const WS_PATHS = {
  vless:  '/vless',
  trojan: '/trojan',
  vmess:  '/vmess',
};

let uuidClean = UUID.replace(/-/g, ""), ISP = '';
const DNS_SERVERS = ['8.8.4.4', '1.1.1.1'];
const BLOCKED_DOMAINS = [
  'speedtest.net', 'fast.com', 'speedtest.cn', 'speed.cloudflare.com', 'speedof.me',
  'testmy.net', 'bandwidth.place', 'speed.io', 'librespeed.org', 'speedcheck.org'
];
const IPV4_REGEX = /^(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)$/;

function getEndpointInfo(req) {
  const rawHost = (req.headers['x-forwarded-host'] || req.headers.host || 'localhost').split(',')[0].trim();
  const protoHeader = (req.headers['x-forwarded-proto'] || '').split(',')[0].trim().toLowerCase();
  const isTLS = protoHeader === 'https' || req.socket.encrypted === true;

  let hostname = rawHost, portFromHeader;
  const colonIdx = rawHost.lastIndexOf(':');
  if (colonIdx > -1 && /^\d+$/.test(rawHost.slice(colonIdx + 1))) {
    hostname = rawHost.slice(0, colonIdx);
    portFromHeader = parseInt(rawHost.slice(colonIdx + 1), 10);
  }
  if (hostname.startsWith('[') && hostname.endsWith(']')) hostname = hostname.slice(1, -1);
  const port = portFromHeader || (isTLS ? 443 : (parseInt(PORT, 10) || 80));
  return { domain: hostname || 'localhost', port, tls: isTLS ? 'tls' : 'none' };
}

function isBlockedDomain(host) {
  if (!host) return false;
  const hostLower = host.toLowerCase();
  return BLOCKED_DOMAINS.some(b => hostLower === b || hostLower.endsWith('.' + b));
}

async function getisp() {
  try {
    const res = await axios.get('https://api.ip.sb/geoip', { headers: { 'User-Agent': 'Mozilla/5.0', timeout: 3000 }});
    ISP = `${res.data.country_code}-${res.data.isp}`.replace(/ /g, '_');
  } catch (e) {
    try {
      const res2 = await axios.get('http://ip-api.com/json', { headers: { 'User-Agent': 'Mozilla/5.0', timeout: 3000 }});
      ISP = `${res2.data.countryCode}-${res2.data.org}`.replace(/ /g, '_');
    } catch { ISP = 'Unknown'; }
  }
}

function resolveHost(host) {
  return new Promise((resolve, reject) => {
    if (IPV4_REGEX.test(host)) { resolve(host); return; }
    let attempts = 0;
    function tryNextDNS() {
      if (attempts >= DNS_SERVERS.length) { reject(new Error(`Failed to resolve ${host}`)); return; }
      attempts++;
      const dnsQuery = `https://dns.google/resolve?name=${encodeURIComponent(host)}&type=A`;
      axios.get(dnsQuery, { timeout: 5000, headers: { 'Accept': 'application/dns-json' } })
        .then(r => {
          const d = r.data;
          if (d.Status === 0 && d.Answer) {
            const ip = d.Answer.find(x => x.type === 1);
            if (ip) { resolve(ip.data); return; }
          }
          tryNextDNS();
        })
        .catch(() => { tryNextDNS(); });
    }
    tryNextDNS();
  });
}

// ==================== Engine Kripto VMess AEAD ====================
const ATYP_IPV4 = 0x01;
const ATYP_DOMAIN = 0x02;
const ATYP_IPV6 = 0x03;
const CMD_TCP = 0x01;
const CMD_MUX = 0x03;

const VMESS_SECURITY_AES128_GCM = 3;
const VMESS_SECURITY_CHACHA20_POLY1305 = 4;
const VMESS_SECURITY_NONE = 5;
const VMESS_SECURITY_ZERO = 6;
const VMESS_OPT_CHUNK_STREAM = 0x01;
const VMESS_OPT_CHUNK_MASKING = 0x04;
const VMESS_OPT_GLOBAL_PADDING = 0x08;
const VMESS_OPT_AUTHENTICATED_LENGTH = 0x10;
const VMESS_CMD_KEY_SALT = 'c48619fe-8f02-49e0-b9e9-edf763e17e21';

function utf8(text) { return new TextEncoder().encode(String(text)); }

const KDF_ROOT = utf8('VMess AEAD KDF');
const KDF_AUTH_ID = utf8('AES Auth ID Encryption');
const KDF_HDR_LEN_KEY = utf8('VMess Header AEAD Key_Length');
const KDF_HDR_LEN_IV = utf8('VMess Header AEAD Nonce_Length');
const KDF_HDR_KEY = utf8('VMess Header AEAD Key');
const KDF_HDR_IV = utf8('VMess Header AEAD Nonce');
const KDF_RESP_LEN_KEY = utf8('AEAD Resp Header Len Key');
const KDF_RESP_LEN_IV = utf8('AEAD Resp Header Len IV');
const KDF_RESP_KEY = utf8('AEAD Resp Header Key');
const KDF_RESP_IV = utf8('AEAD Resp Header IV');
const KDF_AUTH_LEN = utf8('auth_len');

const CRC32_TABLE = (() => {
  const t = new Uint32Array(256);
  for (let i = 0; i < 256; i++) {
    let c = i;
    for (let j = 0; j < 8; j++) { c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1); }
    t[i] = c >>> 0;
  }
  return t;
})();

function toU8Sync(value) {
  if (value instanceof Uint8Array) return value;
  if (value instanceof ArrayBuffer) return new Uint8Array(value);
  if (ArrayBuffer.isView(value)) return new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
  if (Buffer.isBuffer(value)) return new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
  throw new TypeError('expected binary data');
}

function concatBytes(...parts) {
  const list = parts.filter((p) => p && p.byteLength !== 0).map(toU8Sync);
  const total = list.reduce((n, p) => n + p.byteLength, 0);
  const out = new Uint8Array(total);
  let off = 0;
  for (const p of list) { out.set(p, off); off += p.byteLength; }
  return out;
}

function md5(data) { return new Uint8Array(createHash('md5').update(Buffer.from(toU8Sync(data))).digest()); }
function sha256(data) { return new Uint8Array(createHash('sha256').update(Buffer.from(toU8Sync(data))).digest()); }

function crc32(bytes) {
  let c = 0xffffffff;
  for (const b of toU8Sync(bytes)) c = CRC32_TABLE[(c ^ b) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}

function fnv1a32(bytes) {
  let h = 0x811c9dc5;
  for (const b of toU8Sync(bytes)) { h ^= b; h = Math.imul(h, 0x01000193) >>> 0; }
  return h >>> 0;
}

function hmacSha256(key, data) {
  return new Uint8Array(createHmac('sha256', Buffer.from(toU8Sync(key))).update(Buffer.from(toU8Sync(data))).digest());
}

function hmacWithHash(hashFn, key, data) {
  let k = toU8Sync(key);
  if (k.byteLength > 64) k = hashFn(k);
  const kb = new Uint8Array(64);
  kb.set(k);
  const ipad = new Uint8Array(64), opad = new Uint8Array(64);
  for (let i = 0; i < 64; i++) { ipad[i] = kb[i] ^ 0x36; opad[i] = kb[i] ^ 0x5c; }
  return hashFn(concatBytes(opad, hashFn(concatBytes(ipad, data))));
}

function vmessKdf(key, ...pathParts) {
  let hashFn = (data) => hmacSha256(KDF_ROOT, data);
  for (const p of pathParts) {
    const prev = hashFn;
    const path = typeof p === 'string' ? utf8(p) : toU8Sync(p).slice();
    hashFn = (data) => hmacWithHash(prev, path, data);
  }
  return hashFn(toU8Sync(key));
}

function vmessKdf16(key, ...pathParts) { return vmessKdf(key, ...pathParts).slice(0, 16); }
function vmessCmdKey(uuidBytes) { return md5(concatBytes(uuidBytes, utf8(VMESS_CMD_KEY_SALT))); }

function cipherAeadName(security) {
  if (security === VMESS_SECURITY_AES128_GCM) return 'aes-128-gcm';
  if (security === VMESS_SECURITY_CHACHA20_POLY1305) return 'chacha20-poly1305';
  throw new Error(`security ${security} is not AEAD`);
}

function chachaKey(key16) {
  const a = md5(key16), b = md5(a);
  return concatBytes(a, b);
}

function normalizeAeadKey(security, key) {
  const k = toU8Sync(key);
  return security === VMESS_SECURITY_CHACHA20_POLY1305 ? chachaKey(k) : k.slice(0, 16);
}

function aeadSeal(security, key, nonce, plain, aad = null) {
  const name = cipherAeadName(security);
  const cipher = createCipheriv(name, Buffer.from(normalizeAeadKey(security, key)), Buffer.from(toU8Sync(nonce)), { authTagLength: 16 });
  if (aad && toU8Sync(aad).byteLength) cipher.setAAD(Buffer.from(toU8Sync(aad)), { plaintextLength: toU8Sync(plain).byteLength });
  const c = Buffer.concat([cipher.update(Buffer.from(toU8Sync(plain))), cipher.final()]);
  return concatBytes(c, cipher.getAuthTag());
}

function aeadOpen(security, key, nonce, sealed, aad = null) {
  const input = toU8Sync(sealed);
  if (input.byteLength < 16) throw new Error('AEAD ciphertext too short');
  const name = cipherAeadName(security);
  const body = input.subarray(0, input.byteLength - 16);
  const tag = input.subarray(input.byteLength - 16);
  const decipher = createDecipheriv(name, Buffer.from(normalizeAeadKey(security, key)), Buffer.from(toU8Sync(nonce)), { authTagLength: 16 });
  if (aad && toU8Sync(aad).byteLength) decipher.setAAD(Buffer.from(toU8Sync(aad)), { plaintextLength: body.byteLength });
  decipher.setAuthTag(Buffer.from(tag));
  return new Uint8Array(Buffer.concat([decipher.update(Buffer.from(body)), decipher.final()]));
}

function aesEcbDecryptBlock(key, block) {
  const decipher = createDecipheriv('aes-128-cbc', Buffer.from(toU8Sync(key)), Buffer.alloc(16));
  decipher.setAutoPadding(false);
  return new Uint8Array(Buffer.concat([decipher.update(Buffer.from(toU8Sync(block))), decipher.final()]));
}

function uuidToBytes(text) {
  const s = String(text || '').trim().toLowerCase();
  return new Uint8Array(Buffer.from(s.replaceAll('-', ''), 'hex'));
}

function tryParsePortFirstAddress(bytes, cursor, addressType) {
  const b = toU8Sync(bytes);
  if (addressType === ATYP_IPV4) {
    if (b.byteLength < cursor + 4) return null;
    return { address: Array.from(b.subarray(cursor, cursor + 4)).join('.'), next: cursor + 4 };
  }
  if (addressType === ATYP_DOMAIN) {
    if (b.byteLength < cursor + 1) return null;
    const len = b[cursor++];
    if (!len || b.byteLength < cursor + len) return null;
    return { address: new TextDecoder('utf-8', { fatal: true }).decode(b.subarray(cursor, cursor + len)), next: cursor + len };
  }
  if (addressType === ATYP_IPV6) {
    if (b.byteLength < cursor + 16) return null;
    const parts = [];
    for (let i = 0; i < 16; i += 2) parts.push(((b[cursor + i] << 8) | b[cursor + i + 1]).toString(16));
    return { address: parts.join(':'), next: cursor + 16 };
  }
  throw new Error(`invalid address type ${addressType}`);
}

function tryParseVmessHeader(bytes, uuidBytes, nowSec = Math.floor(Date.now() / 1000)) {
  const b = toU8Sync(bytes);
  if (b.byteLength < 16) return null;
  const cmdKey = vmessCmdKey(uuidBytes);
  const authID = b.slice(0, 16);
  let authPlain;
  try {
    authPlain = aesEcbDecryptBlock(vmessKdf16(cmdKey, KDF_AUTH_ID), authID);
  } catch { return null; }

  const dv = new DataView(authPlain.buffer, authPlain.byteOffset, authPlain.byteLength);
  const timestamp = Number(dv.getBigInt64(0, false));
  if (dv.getUint32(12, false) !== crc32(authPlain.subarray(0, 12)) || Math.abs(timestamp - nowSec) > 120) {
    return null;
  }
  if (b.byteLength < 42) return null;

  const encLen = b.subarray(16, 34);
  const connNonce = b.subarray(34, 42);
  let lengthPlain;
  try {
    lengthPlain = aeadOpen(VMESS_SECURITY_AES128_GCM, vmessKdf16(cmdKey, KDF_HDR_LEN_KEY, authID, connNonce), vmessKdf(cmdKey, KDF_HDR_LEN_IV, authID, connNonce).slice(0, 12), encLen, authID);
  } catch { return null; }

  const plainLen = (lengthPlain[0] << 8) | lengthPlain[1];
  const total = 42 + plainLen + 16;
  if (b.byteLength < total) return null;

  let plain;
  try {
    plain = aeadOpen(VMESS_SECURITY_AES128_GCM, vmessKdf16(cmdKey, KDF_HDR_KEY, authID, connNonce), vmessKdf(cmdKey, KDF_HDR_IV, authID, connNonce).slice(0, 12), b.subarray(42, total), authID);
  } catch { return null; }

  const requestBodyIV = plain.slice(1, 17);
  const requestBodyKey = plain.slice(17, 33);
  const responseHeader = plain[33];
  let option = plain[34];
  const wireSecurity = plain[35] & 0x0f;
  const command = plain[37];
  let security = wireSecurity;
  if (security === VMESS_SECURITY_ZERO) {
    security = VMESS_SECURITY_NONE;
    option &= ~(VMESS_OPT_CHUNK_STREAM | VMESS_OPT_CHUNK_MASKING | VMESS_OPT_GLOBAL_PADDING | VMESS_OPT_AUTHENTICATED_LENGTH);
  }

  let p = 38, address = 'v1.mux.cool', port = 0, addressType = ATYP_DOMAIN;
  if (command !== CMD_MUX) {
    port = (plain[p] << 8) | plain[p + 1];
    p += 2;
    addressType = plain[p++];
    const a = tryParsePortFirstAddress(plain, p, addressType);
    if (!a) throw new Error('truncated destination');
    address = a.address;
    p = a.next;
  }

  const checksumPos = plain.byteLength - 4;
  if (fnv1a32(plain.subarray(0, checksumPos)) !== new DataView(plain.buffer, plain.byteOffset + checksumPos, 4).getUint32(0, false)) {
    throw new Error('invalid VMess checksum');
  }

  return {
    command, address, port, addressType, option, security, wireSecurity,
    requestBodyIV, requestBodyKey, responseHeader, headerLength: total, authID,
    responseBodyKey: sha256(requestBodyKey).slice(0, 16),
    responseBodyIV: sha256(requestBodyIV).slice(0, 16),
  };
}

class NonceCounter {
  constructor(iv) {
    this.base = toU8Sync(iv).slice();
    this.count = 0;
  }
  next(size = 12) {
    const out = this.base.slice();
    out[0] = (this.count >>> 8) & 0xff;
    out[1] = this.count & 0xff;
    this.count = (this.count + 1) & 0xffff;
    return out.slice(0, size);
  }
}

// Shake128 XOF
const KECCAK64_MASK = (1n << 64n) - 1n;
const KECCAK_ROTC = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14];
const KECCAK_RC = [
  0x0000000000000001n, 0x0000000000008082n, 0x800000000000808an, 0x8000000080008000n,
  0x000000000000808bn, 0x0000000080000001n, 0x8000000080008081n, 0x8000000000008009n,
  0x000000000000008an, 0x0000000000000088n, 0x0000000080008009n, 0x000000008000000an,
  0x000000008000808bn, 0x800000000000008bn, 0x8000000000008089n, 0x8000000000008003n,
  0x8000000000008002n, 0x8000000000000080n, 0x000000000000800an, 0x800000008000000an,
  0x8000000080008081n, 0x8000000000008080n, 0x0000000080000001n, 0x8000000080008008n
];

function rotl64(value, shift) {
  const n = BigInt(shift & 63);
  return n === 0n ? (value & KECCAK64_MASK) : (((value << n) | (value >> (64n - n))) & KECCAK64_MASK);
}

function keccakF1600(state) {
  const c = new Array(5), d = new Array(5), b = new Array(25);
  for (const rc of KECCAK_RC) {
    for (let x = 0; x < 5; x++) c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
    for (let x = 0; x < 5; x++) d[x] = c[(x + 4) % 5] ^ rotl64(c[(x + 1) % 5], 1);
    for (let y = 0; y < 5; y++) {
      for (let x = 0; x < 5; x++) state[x + 5 * y] = (state[x + 5 * y] ^ d[x]) & KECCAK64_MASK;
    }
    for (let y = 0; y < 5; y++) {
      for (let x = 0; x < 5; x++) {
        const src = x + 5 * y;
        b[y + 5 * ((2 * x + 3 * y) % 5)] = rotl64(state[src], KECCAK_ROTC[src]);
      }
    }
    for (let y = 0; y < 5; y++) {
      const row = 5 * y;
      for (let x = 0; x < 5; x++) state[row + x] = (b[row + x] ^ ((~b[row + ((x + 1) % 5)]) & b[row + ((x + 2) % 5)])) & KECCAK64_MASK;
    }
    state[0] = (state[0] ^ rc) & KECCAK64_MASK;
  }
}

class Shake128Xof {
  constructor(input) {
    this.rate = 168;
    this.state = Array(25).fill(0n);
    this.squeezeOffset = 0;
    this.absorb(toU8Sync(input));
  }
  xorBlock(block) {
    for (let i = 0; i < block.byteLength; i++) {
      this.state[i >>> 3] ^= BigInt(block[i]) << BigInt((i & 7) * 8);
    }
  }
  absorb(input) {
    let offset = 0;
    while (input.byteLength - offset >= this.rate) {
      this.xorBlock(input.subarray(offset, offset + this.rate));
      keccakF1600(this.state);
      offset += this.rate;
    }
    const finalBlock = new Uint8Array(this.rate);
    finalBlock.set(input.subarray(offset));
    finalBlock[input.byteLength - offset] ^= 0x1f;
    finalBlock[this.rate - 1] ^= 0x80;
    this.xorBlock(finalBlock);
    keccakF1600(this.state);
  }
  read(length) {
    const out = new Uint8Array(length);
    for (let i = 0; i < length; i++) {
      if (this.squeezeOffset === this.rate) {
        keccakF1600(this.state);
        this.squeezeOffset = 0;
      }
      const p = this.squeezeOffset++;
      out[i] = Number((this.state[p >>> 3] >> BigInt((p & 7) * 8)) & 0xffn);
    }
    return out;
  }
}

class ShakeSizeParser {
  constructor(seed) { this.shake = new Shake128Xof(seed); }
  nextWord() {
    const b = this.shake.read(2);
    return (b[0] << 8) | b[1];
  }
  decodeSize(bytes) {
    const b = toU8Sync(bytes);
    return (((b[0] << 8) | b[1]) ^ this.nextWord()) & 0xffff;
  }
  encodeSize(size) {
    const v = (size ^ this.nextWord()) & 0xffff;
    return new Uint8Array([v >>> 8, v & 0xff]);
  }
  nextPaddingLen() { return this.nextWord() % 64; }
}

function randomPadding(n) { return n ? new Uint8Array(randomBytes(n)) : new Uint8Array(0); }

// Decoder Chunk VMess dari Client
class VmessBodyDecoder {
  constructor(header) {
    this.header = header;
    this.pending = new Uint8Array(0);
    this.awaiting = null;
    this.done = false;
    this.zeroRaw = header.wireSecurity === VMESS_SECURITY_ZERO || (header.security === VMESS_SECURITY_NONE && !(header.option & VMESS_OPT_CHUNK_STREAM));
    this.sizeShake = (header.option & VMESS_OPT_CHUNK_MASKING) ? new ShakeSizeParser(header.requestBodyIV) : null;
    this.paddingShake = (header.option & VMESS_OPT_GLOBAL_PADDING) ? this.sizeShake : null;
    this.bodyNonce = new NonceCounter(header.requestBodyIV);
    this.lengthNonce = new NonceCounter(header.requestBodyIV);
    this.authLength = !!(header.option & VMESS_OPT_AUTHENTICATED_LENGTH) && [VMESS_SECURITY_AES128_GCM, VMESS_SECURITY_CHACHA20_POLY1305].includes(header.security);
    this.authLengthKey = this.authLength ? vmessKdf16(header.requestBodyKey, KDF_AUTH_LEN) : null;
  }
  push(chunk) {
    if (this.done) return [];
    const c = toU8Sync(chunk);
    if (this.zeroRaw) return c.byteLength ? [c.slice()] : [];
    this.pending = concatBytes(this.pending, c);
    const out = [];
    for (;;) {
      if (!this.awaiting) {
        const sizeBytes = this.authLength ? 18 : 2;
        if (this.pending.byteLength < sizeBytes) break;
        let padding = 0;
        if (this.paddingShake && this.header.security !== VMESS_SECURITY_NONE) {
          padding = this.paddingShake.nextPaddingLen();
        }
        let size;
        const raw = this.pending.slice(0, sizeBytes);
        if (this.authLength) {
          const plain = aeadOpen(this.header.security, this.authLengthKey, this.lengthNonce.next(12), raw);
          size = ((plain[0] << 8) | plain[1]) + 16;
        } else if (this.sizeShake) {
          size = this.sizeShake.decodeSize(raw);
        } else {
          size = (raw[0] << 8) | raw[1];
        }
        this.pending = this.pending.slice(sizeBytes);
        this.awaiting = { size, padding };
      }
      const { size, padding } = this.awaiting;
      if (this.pending.byteLength < size) break;
      const frame = this.pending.slice(0, size);
      this.pending = this.pending.slice(size);
      this.awaiting = null;

      if (this.header.security === VMESS_SECURITY_NONE) {
        if (size === 0) { this.done = true; break; }
        out.push(frame);
        continue;
      }
      if (size === 16 + padding) { this.done = true; break; }
      const sealed = frame.slice(0, size - padding);
      out.push(aeadOpen(this.header.security, this.header.requestBodyKey, this.bodyNonce.next(12), sealed));
    }
    return out;
  }
}

// Encoder Chunk VMess ke arah Client
class VmessBodyEncoder {
  constructor(header) {
    this.header = header;
    this.responseKey = header.responseBodyKey;
    this.responseIV = header.responseBodyIV;
    this.zeroRaw = header.wireSecurity === VMESS_SECURITY_ZERO || (header.security === VMESS_SECURITY_NONE && !(header.option & VMESS_OPT_CHUNK_STREAM));
    this.sizeShake = (header.option & VMESS_OPT_CHUNK_MASKING) ? new ShakeSizeParser(this.responseIV) : null;
    this.paddingShake = (header.option & VMESS_OPT_GLOBAL_PADDING) ? this.sizeShake : null;
    this.bodyNonce = new NonceCounter(this.responseIV);
    this.lengthNonce = new NonceCounter(header.requestBodyIV);
    this.authLength = !!(header.option & VMESS_OPT_AUTHENTICATED_LENGTH) && [VMESS_SECURITY_AES128_GCM, VMESS_SECURITY_CHACHA20_POLY1305].includes(header.security);
    this.authLengthKey = this.authLength ? vmessKdf16(header.requestBodyKey, KDF_AUTH_LEN) : null;
  }
  encode(data) {
    const input = toU8Sync(data);
    if (this.zeroRaw) return input.slice();
    const parts = [];
    for (let off = 0; off < input.byteLength; off += 8192) {
      parts.push(this.encodeUnit(input.slice(off, Math.min(input.byteLength, off + 8192))));
    }
    return concatBytes(...parts);
  }
  encodeUnit(plain) {
    const p = toU8Sync(plain);
    if (this.header.security === VMESS_SECURITY_NONE) {
      const size = p.byteLength;
      const sb = this.sizeShake ? this.sizeShake.encodeSize(size) : new Uint8Array([size >>> 8, size & 0xff]);
      return concatBytes(sb, p);
    }
    const padding = this.paddingShake ? this.paddingShake.nextPaddingLen() : 0;
    const sealed = aeadSeal(this.header.security, this.responseKey, this.bodyNonce.next(12), p);
    const size = sealed.byteLength + padding;
    let sb;
    if (this.authLength) {
      const plainSize = size - 16;
      sb = aeadSeal(this.header.security, this.authLengthKey, this.lengthNonce.next(12), new Uint8Array([plainSize >>> 8, plainSize & 0xff]));
    } else if (this.sizeShake) {
      sb = this.sizeShake.encodeSize(size);
    } else {
      sb = new Uint8Array([size >>> 8, size & 0xff]);
    }
    return concatBytes(sb, sealed, randomPadding(padding));
  }
}

function encodeVmessResponseHeader(header) {
  const plain = new Uint8Array([header.responseHeader, 0x00, 0x00, 0x00]);
  const lenPlain = new Uint8Array([0x00, plain.byteLength]);
  const lenKey = vmessKdf16(header.responseBodyKey, KDF_RESP_LEN_KEY);
  const lenIv = vmessKdf(header.responseBodyIV, KDF_RESP_LEN_IV).slice(0, 12);
  const payloadKey = vmessKdf16(header.responseBodyKey, KDF_RESP_KEY);
  const payloadIv = vmessKdf(header.responseBodyIV, KDF_RESP_IV).slice(0, 12);
  return concatBytes(aeadSeal(VMESS_SECURITY_AES128_GCM, lenKey, lenIv, lenPlain), aeadSeal(VMESS_SECURITY_AES128_GCM, payloadKey, payloadIv, plain));
}

// ==================== VMess Handler Fixed ====================
async function handleVmessConnection(ws, msg) {
  let pendingHeader = toU8Sync(msg);
  let header = tryParseVmessHeader(pendingHeader, uuidToBytes(UUID));

  if (!header) {
    ws.close();
    return false;
  }

  const remainder = pendingHeader.slice(header.headerLength);
  const decoder = new VmessBodyDecoder(header);
  const encoder = new VmessBodyEncoder(header);

  if (isBlockedDomain(header.address)) { ws.close(); return false; }

  // Handshake respons dikirim duluan ke client agar tidak timeout
  if (ws.readyState === WebSocket.OPEN) {
    ws.send(Buffer.from(encodeVmessResponseHeader(header)));
  }

  let targetHost = header.address;
  try { targetHost = await resolveHost(header.address); } catch {}

  const tcpSocket = net.connect({ host: targetHost, port: header.port });
  const pendingQueue = [];

  if (remainder.byteLength > 0) {
    try {
      for (const plain of decoder.push(remainder)) {
        pendingQueue.push(Buffer.from(plain));
      }
    } catch (e) {
      ws.close();
      return false;
    }
  }

  tcpSocket.on('connect', () => {
    while (pendingQueue.length > 0) {
      tcpSocket.write(pendingQueue.shift());
    }
  });

  ws.on('message', (chunk) => {
    try {
      for (const plain of decoder.push(chunk)) {
        if (!tcpSocket.destroyed) {
          if (tcpSocket.connecting) {
            pendingQueue.push(Buffer.from(plain));
          } else {
            tcpSocket.write(Buffer.from(plain));
          }
        }
      }
    } catch (e) {
      logErr('[VMESS DECODE ERROR]', e.message);
      ws.close();
    }
  });

  tcpSocket.on('data', (plain) => {
    if (ws.readyState === WebSocket.OPEN) {
      try {
        const encoded = encoder.encode(plain);
        if (encoded.byteLength) ws.send(Buffer.from(encoded));
      } catch (e) {
        logErr('[VMESS ENCODE ERROR]', e.message);
        tcpSocket.destroy();
      }
    }
  });

  tcpSocket.on('error', () => ws.close());
  tcpSocket.on('close', () => ws.close());
  ws.on('close', () => { if (!tcpSocket.destroyed) tcpSocket.destroy(); });
  ws.on('error', () => { if (!tcpSocket.destroyed) tcpSocket.destroy(); });

  return true;
}

// ==================== VLESS & Trojan Handler ====================
function handleVlsConnection(ws, msg) {
  const [VERSION] = msg;
  const id = msg.slice(1, 17);
  if (!id.every((v, i) => v == parseInt(uuidClean.substr(i * 2, 2), 16))) return false;

  let i = msg.slice(17, 18).readUInt8() + 19;
  const port = msg.slice(i, i += 2).readUInt16BE(0);
  const ATYP = msg.slice(i, i += 1).readUInt8();
  const host = ATYP == 1 ? msg.slice(i, i += 4).join('.') :
    (ATYP == 2 ? new TextDecoder().decode(msg.slice(i + 1, i += 1 + msg.slice(i, i + 1).readUInt8())) :
      (ATYP == 3 ? msg.slice(i, i += 16).reduce((s, b, i, a) => (i % 2 ? s.concat(a.slice(i - 1, i + 1)) : s), []).map(b => b.readUInt16BE(0).toString(16)).join(':') : ''));

  if (isBlockedDomain(host)) { ws.close(); return false; }
  ws.send(new Uint8Array([VERSION, 0]));
  const duplex = createWebSocketStream(ws);
  resolveHost(host)
    .then(ip => {
      net.connect({ host: ip, port }, function () {
        this.write(msg.slice(i));
        duplex.on('error', () => {}).pipe(this).on('error', () => {}).pipe(duplex);
      }).on('error', () => {});
    })
    .catch(() => {
      net.connect({ host, port }, function () {
        this.write(msg.slice(i));
        duplex.on('error', () => {}).pipe(this).on('error', () => {}).pipe(duplex);
      }).on('error', () => {});
    });
  return true;
}

function handleTrojConnection(ws, msg) {
  try {
    if (msg.length < 58) return false;
    const receivedHash = msg.slice(0, 56).toString();
    const hash = createHash('sha224').update(UUID).digest('hex');
    if (hash !== receivedHash) return false;
    let offset = 56;
    if (msg[offset] === 0x0d && msg[offset + 1] === 0x0a) offset += 2;
    const cmd = msg[offset]; if (cmd !== 0x01) return false;
    offset += 1;
    const atyp = msg[offset]; offset += 1;
    let host, port;
    if (atyp === 0x01) { host = msg.slice(offset, offset + 4).join('.'); offset += 4; }
    else if (atyp === 0x03) { const l = msg[offset]; offset += 1; host = msg.slice(offset, offset + l).toString(); offset += l; }
    else if (atyp === 0x04) { host = msg.slice(offset, offset + 16).reduce((s, b, i, a) => (i % 2 ? s.concat(a.slice(i - 1, i + 1)) : s), []).map(b => b.readUInt16BE(0).toString(16)).join(':'); offset += 16; }
    else return false;
    port = msg.readUInt16BE(offset); offset += 2;
    if (offset < msg.length && msg[offset] === 0x0d && msg[offset + 1] === 0x0a) offset += 2;
    if (isBlockedDomain(host)) { ws.close(); return false; }
    const duplex = createWebSocketStream(ws);
    resolveHost(host)
      .then(ip => {
        net.connect({ host: ip, port }, function () {
          if (offset < msg.length) this.write(msg.slice(offset));
          duplex.on('error', () => {}).pipe(this).on('error', () => {}).pipe(duplex);
        }).on('error', () => {});
      })
      .catch(() => {
        net.connect({ host, port }, function () {
          if (offset < msg.length) this.write(msg.slice(offset));
          duplex.on('error', () => {}).pipe(this).on('error', () => {}).pipe(duplex);
        }).on('error', () => {});
      });
    return true;
  } catch { return false; }
}

// ==================== Subscription Builder ====================
async function buildSubscription(req) {
  await getisp();
  const { domain } = getEndpointInfo(req);
  const namePart = NAME ? `${NAME}-${ISP}` : ISP;

  const vlessURI = `vless://${UUID}@${domain}:443?path=%2Fvless&security=tls&encryption=none&host=${domain}&fp=chrome&type=ws&sni=${domain}#${namePart}-VLESS`;
  const trojanURI = `trojan://${UUID}@${domain}:443?path=%2Ftrojan&security=tls&host=${domain}&fp=chrome&type=ws&sni=${domain}#${namePart}-Trojan`;
  
  const vmessConfig = {
    v: '2',
    ps: `${namePart}-VMess`,
    add: domain,
    port: '443',
    id: UUID,
    aid: '0',
    scy: 'auto',
    net: 'ws',
    type: 'none',
    host: domain,
    path: '/vmess',
    tls: 'tls',
    sni: domain,
    alpn: '',
    fp: 'chrome'
  };
  const vmessURI = `vmess://${Buffer.from(JSON.stringify(vmessConfig)).toString('base64')}`;

  return [vlessURI, trojanURI, vmessURI].join('\n');
}

// ==================== HTTP Server & Routing ====================
const httpServer = http.createServer(async (req, res) => {
  const urlPath = req.url.split('?')[0];

  // Routing Subscription: Support /vercel, /sub, dan variabel env
  if (urlPath === `/${SUB_PATH}` || urlPath === '/vercel' || urlPath === '/sub') {
    try {
      const subscription = await buildSubscription(req);
      res.writeHead(200, { 
        'Content-Type': 'text/plain; charset=utf-8',
        'Access-Control-Allow-Origin': '*' 
      });
      res.end(Buffer.from(subscription).toString('base64') + '\n');
    } catch (err) {
      res.writeHead(500, { 'Content-Type': 'text/plain' });
      res.end('Internal Server Error\n');
    }
    return;
  }

  // Routing Tampilan UI HTML
  if (urlPath === '/' || urlPath === '/index.html') {
    const filePath = path.join(__dirname, 'index.html');
    fs.readFile(filePath, 'utf8', (err, content) => {
      if (err) { 
        res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' }); 
        res.end('<h3>Node Proxy UI Running. Subscriptions ready at /vercel</h3>'); 
        return; 
      }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' }); 
      res.end(content);
    });
    return;
  }

  res.writeHead(404, { 'Content-Type': 'text/plain' });
  res.end('Not Found\n');
});

// ==================== WebSocket Dispatcher ====================
const wss = new WebSocket.Server({ server: httpServer });
wss.on('connection', (ws, req) => {
  const pathOnly = (req.url || '').split('?')[0];

  let handler;
  if (pathOnly === WS_PATHS.vless) handler = handleVlsConnection;
  else if (pathOnly === WS_PATHS.trojan) handler = handleTrojConnection;
  else if (pathOnly === WS_PATHS.vmess) handler = handleVmessConnection;
  else { ws.close(); return; }

  ws.once('message', async (msg) => {
    try {
      const ok = await handler(ws, msg);
      if (!ok && ws.readyState === WebSocket.OPEN) ws.close();
    } catch (e) {
      logErr('[DISPATCH ERROR]', e.message);
      if (ws.readyState === WebSocket.OPEN) ws.close();
    }
  }).on('error', () => {});
});

httpServer.listen(PORT, () => {
  console.log(`Server aktif di port ${PORT}`);
  console.log(`Subscription URL : /${SUB_PATH} atau /vercel`);
  console.log(`WS Inbounds      : ${WS_PATHS.vless}, ${WS_PATHS.trojan}, ${WS_PATHS.vmess}`);
});
