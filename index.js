#!/usr/bin/env node

const http = require('http');
const fs = require('fs');
const net = require('net');
const path = require('path');
const crypto = require('crypto');
const { Buffer } = require('buffer');
const axios = require('axios');
const { WebSocket, createWebSocketStream } = require('ws');
const { subtle } = crypto.webcrypto;

// ========================== Environment ==========================
const UUID = process.env.UUID || 'd1cf4b9c-3e57-085d-b34a-797fcf601381';
const SUB_PATH = process.env.SUB_PATH || 'vercel';
const NAME = process.env.NAME || 'Vercel';
const PORT = process.env.PORT || 3000;

const SHOW_LOG = !!(process.env.SHOW_LOG);
function log(...args) { if (SHOW_LOG) console.log(...args); }
function logErr(...args) { if (SHOW_LOG) console.error(...args); }

// ============== Path per protokol ==============
const WS_PATHS = {
  vless:  '/vless',
  trojan: '/trojan',
  ss:     '/ss',
  vmess:  '/vmess',
};

// ==================== Konfigurasi umum ====================
let uuid = UUID.replace(/-/g, ""), ISP = '';
const DNS_SERVERS = ['8.8.4.4', '1.1.1.1'];
const DOH_SERVERS = ['https://1.1.1.1/dns-query', 'https://8.8.8.8/dns-query'];
const BLOCKED_DOMAINS = [
  'speedtest.net', 'fast.com', 'speedtest.cn', 'speed.cloudflare.com', 'speedof.me',
  'testmy.net', 'bandwidth.place', 'speed.io', 'librespeed.org', 'speedcheck.org'
];
const IPV4_REGEX = /^(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)$/;
const DNS_PORT = 53;

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

// ==================== Crypto helpers ====================
const str2arr = (str) => new TextEncoder().encode(str);
const arr2str = (arr) => new TextDecoder().decode(arr);

const concat = (...arrays) => {
  const result = new Uint8Array(arrays.reduce((sum, arr) => sum + arr.length, 0));
  let offset = 0;
  for (const arr of arrays) { result.set(arr, offset); offset += arr.length; }
  return result;
};

const alloc = (size, fill = 0) => {
  const arr = new Uint8Array(size);
  if (fill) arr.fill(fill);
  return arr;
};

function toBuffer(uuidStr) {
  const hex = uuidStr.replace(/-/g, '');
  const arr = new Uint8Array(16);
  for (let i = 0; i < 16; i++) arr[i] = parseInt(hex.substr(i * 2, 2), 16);
  return arr;
}

function sha256(message) {
  const msg = message instanceof Uint8Array ? message : str2arr(message);
  const K = [0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2];
  let H = [0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19];
  const rotr = (x, n) => (x >>> n) | (x << (32 - n));
  const len = msg.length, paddingLen = ((56 - (len + 1) % 64) + 64) % 64;
  const padded = new Uint8Array(len + 1 + paddingLen + 8);
  padded.set(msg); padded[len] = 0x80;
  new DataView(padded.buffer).setUint32(padded.length - 4, len * 8, false);
  const W = new Uint32Array(64);
  for (let i = 0; i < padded.length; i += 64) {
    const block = new DataView(padded.buffer, i, 64);
    for (let t = 0; t < 16; t++) W[t] = block.getUint32(t * 4, false);
    for (let t = 16; t < 64; t++) {
      const s0 = rotr(W[t - 15], 7) ^ rotr(W[t - 15], 18) ^ (W[t - 15] >>> 3);
      const s1 = rotr(W[t - 2], 17) ^ rotr(W[t - 2], 19) ^ (W[t - 2] >>> 10);
      W[t] = (W[t - 16] + s0 + W[t - 7] + s1) >>> 0;
    }
    let [a, b, c, d, e, f, g, h] = H;
    for (let t = 0; t < 64; t++) {
      const S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25), ch = (e & f) ^ (~e & g), T1 = (h + S1 + ch + K[t] + W[t]) >>> 0;
      const S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22), maj = (a & b) ^ (a & c) ^ (b & c), T2 = (S0 + maj) >>> 0;
      h = g; g = f; f = e; e = (d + T1) >>> 0; d = c; c = b; b = a; a = (T1 + T2) >>> 0;
    }
    H[0] = (H[0] + a) >>> 0; H[1] = (H[1] + b) >>> 0; H[2] = (H[2] + c) >>> 0; H[3] = (H[3] + d) >>> 0;
    H[4] = (H[4] + e) >>> 0; H[5] = (H[5] + f) >>> 0; H[6] = (H[6] + g) >>> 0; H[7] = (H[7] + h) >>> 0;
  }
  const result = new Uint8Array(32), rv = new DataView(result.buffer);
  for (let i = 0; i < 8; i++) rv.setUint32(i * 4, H[i], false);
  return result;
}

function md5(data, salt) {
  let msg = data instanceof Uint8Array ? data : str2arr(data);
  if (salt) msg = concat(msg, salt instanceof Uint8Array ? salt : str2arr(salt));
  const K = [0xd76aa478,0xe8c7b756,0x242070db,0xc1bdceee,0xf57c0faf,0x4787c62a,0xa8304613,0xfd469501,0x698098d8,0x8b44f7af,0xffff5bb1,0x895cd7be,0x6b901122,0xfd987193,0xa679438e,0x49b40821,0xf61e2562,0xc040b340,0x265e5a51,0xe9b6c7aa,0xd62f105d,0x02441453,0xd8a1e681,0xe7d3fbc8,0x21e1cde6,0xc33707d6,0xf4d50d87,0x455a14ed,0xa9e3e905,0xfcefa3f8,0x676f02d9,0x8d2a4c8a,0xfffa3942,0x8771f681,0x6d9d6122,0xfde5380c,0xa4beea44,0x4bdecfa9,0xf6bb4b60,0xbebfbc70,0x289b7ec6,0xeaa127fa,0xd4ef3085,0x04881d05,0xd9d4d039,0xe6db99e5,0x1fa27cf8,0xc4ac5665,0xf4292244,0x432aff97,0xab9423a7,0xfc93a039,0x655b59c3,0x8f0ccc92,0xffeff47d,0x85845dd1,0x6fa87e4f,0xfe2ce6e0,0xa3014314,0x4e0811a1,0xf7537e82,0xbd3af235,0x2ad7d2bb,0xeb86d391];
  const S = [7,12,17,22,7,12,17,22,7,12,17,22,7,12,17,22,5,9,14,20,5,9,14,20,5,9,14,20,5,9,14,20,4,11,16,23,4,11,16,23,4,11,16,23,4,11,16,23,6,10,15,21,6,10,15,21,6,10,15,21,6,10,15,21];
  let [a, b, c, d] = [0x67452301,0xefcdab89,0x98badcfe,0x10325476];
  const len = msg.length, paddingLen = ((56 - (len + 1) % 64) + 64) % 64, padded = new Uint8Array(len + 1 + paddingLen + 8);
  padded.set(msg); padded[len] = 0x80;
  const view = new DataView(padded.buffer);
  view.setUint32(padded.length - 8, (len * 8) >>> 0, true);
  view.setUint32(padded.length - 4, Math.floor(len * 8 / 0x100000000) >>> 0, true);
  const rotl = (x, n) => (x << n) | (x >>> (32 - n));
  for (let i = 0; i < padded.length; i += 64) {
    const M = new Uint32Array(16);
    for (let j = 0; j < 16; j++) M[j] = view.getUint32(i + j * 4, true);
    let [A, B, C, D] = [a, b, c, d];
    for (let j = 0; j < 64; j++) {
      let F, g;
      if (j < 16) { F = (B & C) | (~B & D); g = j; }
      else if (j < 32) { F = (D & B) | (~D & C); g = (5 * j + 1) % 16; }
      else if (j < 48) { F = B ^ C ^ D; g = (3 * j + 5) % 16; }
      else { F = C ^ (B | ~D); g = (7 * j) % 16; }
      F = (F + A + K[j] + M[g]) >>> 0; A = D; D = C; C = B; B = (B + rotl(F, S[j])) >>> 0;
    }
    a = (a + A) >>> 0; b = (b + B) >>> 0; c = (c + C) >>> 0; d = (d + D) >>> 0;
  }
  const result = new Uint8Array(16), rv = new DataView(result.buffer);
  rv.setUint32(0, a, true); rv.setUint32(4, b, true); rv.setUint32(8, c, true); rv.setUint32(12, d, true);
  return result;
}

function createRecursiveHash(key, underlyingHashFn) {
  const ipad = alloc(64, 0x36), opad = alloc(64, 0x5c);
  const keyBuf = key instanceof Uint8Array ? key : str2arr(key);
  for (let i = 0; i < keyBuf.length; i++) { ipad[i] ^= keyBuf[i]; opad[i] ^= keyBuf[i]; }
  return (data) => underlyingHashFn(concat(opad, underlyingHashFn(concat(ipad, data))));
}

function kdf(key, pathArr) {
  let fn = sha256;
  fn = createRecursiveHash(str2arr("VMess AEAD KDF"), fn);
  for (const p of pathArr) fn = createRecursiveHash(p, fn);
  return fn(key);
}

async function aesGcmDecrypt(key, iv, data, aad) {
  const cryptoKey = await subtle.importKey('raw', key, { name: 'AES-GCM' }, false, ['decrypt']);
  return new Uint8Array(await subtle.decrypt({ name: 'AES-GCM', iv, additionalData: aad || new Uint8Array(0), tagLength: 128 }, cryptoKey, data));
}

async function aesGcmEncrypt(key, iv, data, aad) {
  const cryptoKey = await subtle.importKey('raw', key, { name: 'AES-GCM' }, false, ['encrypt']);
  return new Uint8Array(await subtle.encrypt({ name: 'AES-GCM', iv, additionalData: aad || new Uint8Array(0), tagLength: 128 }, cryptoKey, data));
}

// ==================== VMess AEAD constants ====================
const KDFSALT_LEN_KEY = str2arr("VMess Header AEAD Key_Length");
const KDFSALT_LEN_IV  = str2arr("VMess Header AEAD Nonce_Length");
const KDFSALT_PAYLOAD_KEY = str2arr("VMess Header AEAD Key");
const KDFSALT_PAYLOAD_IV  = str2arr("VMess Header AEAD Nonce");
const KDFSALT_RESP_LEN_KEY = str2arr("AEAD Resp Header Len Key");
const KDFSALT_RESP_LEN_IV  = str2arr("AEAD Resp Header Len IV");
const KDFSALT_RESP_HDR_KEY = str2arr("AEAD Resp Header Key");
const KDFSALT_RESP_HDR_IV  = str2arr("AEAD Resp Header IV");

// ==================== VMess AEAD parser ====================
async function parseP4Header(buffer, uuidBytes) {
  if (buffer.length < 42) throw new Error("Data too short");
  const auth_id = buffer.subarray(0, 16);
  let remaining = buffer.subarray(16);

  const len_encrypted = remaining.subarray(0, 18);
  remaining = remaining.subarray(18);
  const nonce = remaining.subarray(0, 8);
  remaining = remaining.subarray(8);

  const key = md5(uuidBytes, str2arr("c48619fe-8f02-49e0-b9e9-edf763e17e21"));
  const header_length_key = kdf(key, [KDFSALT_LEN_KEY, auth_id, nonce]).subarray(0, 16);
  const header_length_nonce = kdf(key, [KDFSALT_LEN_IV, auth_id, nonce]).subarray(0, 12);
  const decryptedLen = await aesGcmDecrypt(header_length_key, header_length_nonce, len_encrypted, auth_id);
  const header_length = (decryptedLen[0] << 8) | decryptedLen[1];
  if (header_length <= 0 || header_length > 4096) throw new Error("Invalid header length");

  const cmd_encrypted = remaining.subarray(0, header_length + 16);
  const rawClientData = remaining.subarray(header_length + 16);

  const payload_key = kdf(key, [KDFSALT_PAYLOAD_KEY, auth_id, nonce]).subarray(0, 16);
  const payload_nonce = kdf(key, [KDFSALT_PAYLOAD_IV, auth_id, nonce]).subarray(0, 12);
  const cmdBuf = await aesGcmDecrypt(payload_key, payload_nonce, cmd_encrypted, auth_id);

  if (cmdBuf[0] !== 1) throw new Error("Invalid VMess version");
  const cmd = cmdBuf[37];
  if (cmd !== 1 && cmd !== 2) throw new Error(`Unsupported cmd ${cmd}`);
  const isUDP = cmd === 2;

  const portRemote = (cmdBuf[38] << 8) | cmdBuf[39];
  let addressRemote = "";
  const addrType = cmdBuf[40];

  if (addrType === 1) {
    addressRemote = `${cmdBuf[41]}.${cmdBuf[42]}.${cmdBuf[43]}.${cmdBuf[44]}`;
  } else if (addrType === 2) {
    const len = cmdBuf[41];
    addressRemote = arr2str(cmdBuf.subarray(42, 42 + len));
  } else if (addrType === 3) {
    const parts = [];
    for (let i = 0; i < 8; i++) parts.push(((cmdBuf[41 + i * 2] << 8) | cmdBuf[41 + i * 2 + 1]).toString(16));
    addressRemote = parts.join(':');
  } else {
    throw new Error(`Invalid addr type ${addrType}`);
  }

  const respKeyBase = sha256(cmdBuf.subarray(17, 33)).subarray(0, 16);
  const respIvBase  = sha256(cmdBuf.subarray(1, 17)).subarray(0, 16);
  const encryptedLength = await aesGcmEncrypt(
    kdf(respKeyBase, [KDFSALT_RESP_LEN_KEY]).subarray(0, 16),
    kdf(respIvBase,  [KDFSALT_RESP_LEN_IV]).subarray(0, 12),
    new Uint8Array([0, 4])
  );
  const encryptedHeaderPayload = await aesGcmEncrypt(
    kdf(respKeyBase, [KDFSALT_RESP_HDR_KEY]).subarray(0, 16),
    kdf(respIvBase,  [KDFSALT_RESP_HDR_IV]).subarray(0, 12),
    new Uint8Array([cmdBuf[33], 0, 0, 0])
  );

  return {
    hasError: false,
    addressRemote,
    portRemote,
    rawClientData,
    version: concat(encryptedLength, encryptedHeaderPayload),
    isUDP
  };
}

// ==================== Build subscription ====================
async function buildSubscription(req) {
  await getisp();
  const { domain } = getEndpointInfo(req);
  const namePart = NAME ? `${NAME}-${ISP}` : ISP;
  const isIP = IPV4_REGEX.test(domain);
  const ssB64 = Buffer.from(`none:${UUID}`).toString('base64');

  const vlessURI = (tls) => tls
    ? `vless://${UUID}@${domain}:443?path=%2Fvless&security=tls&encryption=none&host=${domain}&fp=chrome&type=ws&sni=${domain}#${namePart}-TLS`
    : `vless://${UUID}@${domain}:80?path=%2Fvless&security=none&encryption=none&host=${domain}&fp=chrome&type=ws#${namePart}`;

  const trojanURI = (tls) => tls
    ? `trojan://${UUID}@${domain}:443?path=%2Ftrojan&security=tls&host=${domain}&fp=chrome&type=ws&sni=${domain}#${namePart}-TLS`
    : `trojan://${UUID}@${domain}:80?path=%2Ftrojan&security=none&host=${domain}&fp=chrome&type=ws#${namePart}`;

  const ssURI = (tls) => tls
    ? `ss://${ssB64}@${domain}:443?plugin=v2ray-plugin;mode%3Dwebsocket;host%3D${domain};path%3D%2Fss;tls;sni%3D${domain};skip-cert-verify%3Dtrue;mux%3D0#${namePart}-TLS`
    : `ss://${ssB64}@${domain}:80?plugin=v2ray-plugin;mode%3Dwebsocket;host%3D${domain};path%3D%2Fss;skip-cert-verify%3Dtrue;mux%3D0#${namePart}`;

  const vmessURI = (tls) => {
    const cfg = {
      v: '2',
      ps: tls ? `${namePart}-TLS` : namePart,
      add: domain,
      port: tls ? '443' : '80',
      id: UUID,
      aid: '0',
      scy: 'zero',
      net: 'ws',
      type: 'none',
      host: domain,
      path: '/vmess',
      tls: tls ? 'tls' : '',
      sni: tls ? domain : '',
      alpn: '',
      fp: ''
    };
    return `vmess://${Buffer.from(JSON.stringify(cfg)).toString('base64')}`;
  };

  const configs = [];
  if (isIP) {
    configs.push(
      vlessURI(false), trojanURI(false), ssURI(false), vmessURI(false)
    );
  } else {
    configs.push(
      vlessURI(true),  vlessURI(false),
      trojanURI(true), trojanURI(false),
      ssURI(true),     ssURI(false),
      vmessURI(true),  vmessURI(false),
    );
  }
  return configs.join('\n');
}

// ==================== HTTP server ====================
const httpServer = http.createServer(async (req, res) => {
  if (req.url === '/') {
    const filePath = path.join(__dirname, 'index.html');
    fs.readFile(filePath, 'utf8', (err, content) => {
      if (err) { res.writeHead(200, { 'Content-Type': 'text/html' }); res.end('Hello world!'); return; }
      res.writeHead(200, { 'Content-Type': 'text/html' }); res.end(content);
    });
    return;
  } else if (req.url.split('?')[0] === `/${SUB_PATH}`) {
    try {
      const subscription = await buildSubscription(req);
      res.writeHead(200, { 'Content-Type': 'text/plain' });
      res.end(Buffer.from(subscription).toString('base64') + '\n');
    } catch (err) {
      logErr('[SUB] error:', err.message);
      res.writeHead(500, { 'Content-Type': 'text/plain' }); res.end('Internal Server Error\n');
    }
    return;
  } else {
    res.writeHead(404, { 'Content-Type': 'text/plain' }); res.end('Not Found\n');
  }
});

// ==================== VLESS handler ====================
function handleVlsConnection(ws, msg) {
  const [VERSION] = msg;
  const id = msg.slice(1, 17);
  if (!id.every((v, i) => v == parseInt(uuid.substr(i * 2, 2), 16))) return false;

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

// ==================== Trojan handler ====================
function handleTrojConnection(ws, msg) {
  try {
    if (msg.length < 58) return false;
    const receivedHash = msg.slice(0, 56).toString();
    const hash = crypto.createHash('sha224').update(UUID).digest('hex');
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

// ==================== SS handler ====================
function handleSsConnection(ws, msg) {
  try {
    let offset = 0;
    const atyp = msg[offset]; offset += 1;
    let host, port;
    if (atyp === 0x01) { host = msg.slice(offset, offset + 4).join('.'); offset += 4; }
    else if (atyp === 0x03) { const l = msg[offset]; offset += 1; host = msg.slice(offset, offset + l).toString(); offset += l; }
    else if (atyp === 0x04) { host = msg.slice(offset, offset + 16).reduce((s, b, i, a) => (i % 2 ? s.concat(a.slice(i - 1, i + 1)) : s), []).map(b => b.readUInt16BE(0).toString(16)).join(':'); offset += 16; }
    else return false;
    port = msg.readUInt16BE(offset); offset += 2;
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

// ==================== VMess handler (AEAD) ====================
function setupUDPHandler(ws, responseHeader, initialChunk) {
  let isHeaderSent = false;

  const processChunk = async (chunk) => {
    let offset = 0;
    while (offset < chunk.length) {
      if (offset + 2 > chunk.length) break;
      const len = (chunk[offset] << 8) | chunk[offset + 1];
      offset += 2;
      if (offset + len > chunk.length) break;
      const dnsQuery = chunk.slice(offset, offset + len);
      offset += len;

      try {
        const dohUrl = DOH_SERVERS[Math.floor(Math.random() * DOH_SERVERS.length)];
        const resp = await axios.post(dohUrl, Buffer.from(dnsQuery), {
          headers: { 'content-type': 'application/dns-message' },
          responseType: 'arraybuffer',
          timeout: 5000
        });
        const dnsResp = new Uint8Array(resp.data);
        const lenBuf = new Uint8Array([(dnsResp.length >> 8) & 0xff, dnsResp.length & 0xff]);
        const packet = concat(lenBuf, dnsResp);

        if (ws.readyState !== WebSocket.OPEN) return;

        if (isHeaderSent) {
          ws.send(Buffer.from(packet));
        } else {
          ws.send(Buffer.concat([Buffer.from(responseHeader), Buffer.from(packet)]));
          isHeaderSent = true;
        }
      } catch (e) {
        logErr('[DOH] error:', e.message);
      }
    }
  };

  processChunk(new Uint8Array(initialChunk)).catch(e => logErr('[DOH] init error:', e.message));
  return { write: processChunk };
}

async function handleVmessConnection(ws, msg) {
  const buffer = new Uint8Array(msg);
  let tcpSocket = null;
  let udpHandler = null;
  const pendingWrites = [];

  ws.on('message', (m) => {
    try {
      if (udpHandler) { udpHandler.write(new Uint8Array(m)); return; }
      if (tcpSocket && !tcpSocket.destroyed) {
        tcpSocket.write(Buffer.from(m));
      } else {
        pendingWrites.push(m);
      }
    } catch (e) { logErr('[VMESS] msg error:', e.message); }
  });

  try {
    const uuidBytes = toBuffer(UUID);
    const header = await parseP4Header(buffer, uuidBytes);
    if (header.hasError) { ws.close(); return false; }

    const { addressRemote, portRemote, rawClientData, version, isUDP } = header;

    if (isBlockedDomain(addressRemote)) { ws.close(); return false; }

    if (isUDP) {
      if (portRemote === DNS_PORT) {
        udpHandler = setupUDPHandler(ws, version, rawClientData);
        return true;
      }
      logErr('[VMESS] UDP only supported for DNS port 53');
      ws.close();
      return false;
    }

    let host = addressRemote;
    try { host = await resolveHost(addressRemote); } catch { /* use domain */ }

    tcpSocket = net.connect({ host, port: portRemote });
    let responseHeader = version;

    tcpSocket.on('connect', () => {
      log(`[VMESS] connected ${addressRemote}:${portRemote}`);
      if (rawClientData && rawClientData.length > 0) {
        tcpSocket.write(Buffer.from(rawClientData));
      }
      for (const pw of pendingWrites) tcpSocket.write(Buffer.from(pw));
      pendingWrites.length = 0;
    });

    tcpSocket.on('data', (chunk) => {
      if (ws.readyState !== WebSocket.OPEN) { tcpSocket.destroy(); return; }
      if (responseHeader) {
        ws.send(Buffer.concat([Buffer.from(responseHeader), chunk]));
        responseHeader = null;
      } else {
        ws.send(chunk);
      }
    });

    tcpSocket.on('error', (e) => { logErr('[VMESS] tcp error:', e.message); ws.close(); });
    tcpSocket.on('close', () => ws.close());

    ws.on('close', () => { if (tcpSocket && !tcpSocket.destroyed) tcpSocket.destroy(); });
    ws.on('error', () => { if (tcpSocket && !tcpSocket.destroyed) tcpSocket.destroy(); });

    return true;
  } catch (e) {
    logErr('[VMESS] error:', e.message);
    ws.close();
    return false;
  }
}

// ==================== WebSocket dispatcher ====================
const wss = new WebSocket.Server({ server: httpServer });
wss.on('connection', (ws, req) => {
  const pathOnly = (req.url || '').split('?')[0];

  let handler;
  if (pathOnly === WS_PATHS.vless)        handler = handleVlsConnection;
  else if (pathOnly === WS_PATHS.trojan)  handler = handleTrojConnection;
  else if (pathOnly === WS_PATHS.ss)      handler = handleSsConnection;
  else if (pathOnly === WS_PATHS.vmess)   handler = handleVmessConnection;
  else { ws.close(); return; }

  ws.once('message', async (msg) => {
    try {
      const ok = await handler(ws, msg);
      if (!ok && ws.readyState === WebSocket.OPEN) ws.close();
    } catch (e) {
      logErr('[DISPATCH] error:', e.message);
      if (ws.readyState === WebSocket.OPEN) ws.close();
    }
  }).on('error', () => {});
});

// ==================== Start ====================
httpServer.listen(PORT, () => {
  console.log(`Server is running on ${PORT}`);
  console.log(`UUID (env): ${UUID}`);
  console.log(`WS paths → ${WS_PATHS.vless}, ${WS_PATHS.trojan}, ${WS_PATHS.ss}, ${WS_PATHS.vmess}`);
});
