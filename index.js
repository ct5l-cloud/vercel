#!/usr/bin/env node

const http = require('http');
const fs = require('fs');
const net = require('net');
const path = require('path');
const crypto = require('crypto');
const { Buffer } = require('buffer');
const axios = require('axios');
const { WebSocket, createWebSocketStream } = require('ws');

// ========================== 环境变量配置 ==========================
const UUID = process.env.UUID || 'd1cf4b9c-3e57-085d-b34a-797fcf601381';
const SUB_PATH = process.env.SUB_PATH || 'vercel';
const NAME = process.env.NAME || 'Vercel';
const PORT = process.env.PORT || 3000;

// 日志控制
const SHOW_LOG = !!(process.env.SHOW_LOG);
function log(...args) { if (SHOW_LOG) console.log(...args); }
function logErr(...args) { if (SHOW_LOG) console.error(...args); }
function logWarn(...args) { if (SHOW_LOG) console.warn(...args); }

// 辅助工具
const WSPATH = process.env.WSPATH || UUID.slice(0, 8);
let uuid = UUID.replace(/-/g, ""), ISP = '';
const DNS_SERVERS = ['8.8.4.4', '1.1.1.1'];
const BLOCKED_DOMAINS = [
  'speedtest.net', 'fast.com', 'speedtest.cn', 'speed.cloudflare.com', 'speedof.me',
  'testmy.net', 'bandwidth.place', 'speed.io', 'librespeed.org', 'speedcheck.org'
];
const IPV4_REGEX = /^(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)$/;

// ============== VMess AEAD: helper binary & crypto ==============
const str2arr = (s) => new TextEncoder().encode(s);
const arr2str = (a) => new TextDecoder().decode(a);
const concat = (...arrays) => {
  const result = new Uint8Array(arrays.reduce((sum, a) => sum + a.length, 0));
  let offset = 0;
  for (const a of arrays) { result.set(a, offset); offset += a.length; }
  return result;
};
const alloc = (size, fill = 0) => {
  const arr = new Uint8Array(size);
  if (fill) arr.fill(fill);
  return arr;
};

const VMESS_SALT = {
  LEN_KEY:     str2arr("VMess Header AEAD Key_Length"),
  LEN_IV:      str2arr("VMess Header AEAD Nonce_Length"),
  PAYLOAD_KEY: str2arr("VMess Header AEAD Key"),
  PAYLOAD_IV:  str2arr("VMess Header AEAD Nonce"),
  RESP_LEN_KEY: str2arr("AEAD Resp Header Len Key"),
  RESP_LEN_IV:  str2arr("AEAD Resp Header Len IV"),
  RESP_KEY:     str2arr("AEAD Resp Header Key"),
  RESP_IV:      str2arr("AEAD Resp Header IV"),
};
const VMESS_MD5_SALT = str2arr("c48619fe-8f02-49e0-b9e9-edf763e17e21");

function toBuffer(uuidStr) {
  const hex = uuidStr.replace(/-/g, '');
  const arr = new Uint8Array(16);
  for (let i = 0; i < 16; i++) arr[i] = parseInt(hex.substr(i * 2, 2), 16);
  return arr;
}

function sha256(data) {
  return new Uint8Array(crypto.createHash('sha256').update(Buffer.from(data)).digest());
}
function md5(data) {
  return new Uint8Array(crypto.createHash('md5').update(Buffer.from(data)).digest());
}
function createRecursiveHash(key, underlying) {
  const ipad = alloc(64, 0x36);
  const opad = alloc(64, 0x5c);
  const keyBuf = key instanceof Uint8Array ? key : str2arr(key);
  for (let i = 0; i < keyBuf.length; i++) { ipad[i] ^= keyBuf[i]; opad[i] ^= keyBuf[i]; }
  return (data) => underlying(concat(opad, underlying(concat(ipad, data))));
}
function kdf(key, path) {
  let fn = sha256;
  fn = createRecursiveHash(str2arr("VMess AEAD KDF"), fn);
  for (const p of path) fn = createRecursiveHash(p, fn);
  return fn(key);
}

async function aesGcmDecrypt(key, iv, data, aad) {
  const buf = Buffer.from(data);
  const tag = buf.slice(buf.length - 16);
  const ct = buf.slice(0, buf.length - 16);
  const decipher = crypto.createDecipheriv('aes-128-gcm', Buffer.from(key), Buffer.from(iv));
  if (aad) decipher.setAAD(Buffer.from(aad));
  decipher.setAuthTag(tag);
  const decrypted = Buffer.concat([decipher.update(ct), decipher.final()]);
  return new Uint8Array(decrypted);
}

async function aesGcmEncrypt(key, iv, data, aad) {
  const cipher = crypto.createCipheriv('aes-128-gcm', Buffer.from(key), Buffer.from(iv));
  if (aad) cipher.setAAD(Buffer.from(aad));
  const encrypted = Buffer.concat([cipher.update(Buffer.from(data)), cipher.final()]);
  return new Uint8Array(Buffer.concat([encrypted, cipher.getAuthTag()]));
}

// Cek apakah payload adalah VMess AEAD (coba dekripsi length header)
async function isVMess(buffer) {
  if (buffer.length < 42) return false;
  try {
    const uuidBytes = toBuffer(UUID);
    const auth_id = buffer.subarray(0, 16);
    const len_encrypted = buffer.subarray(16, 34);
    const nonce = buffer.subarray(34, 42);
    const key = md5(concat(uuidBytes, VMESS_MD5_SALT));
    const len_key = kdf(key, [VMESS_SALT.LEN_KEY, auth_id, nonce]).subarray(0, 16);
    const len_iv  = kdf(key, [VMESS_SALT.LEN_IV, auth_id, nonce]).subarray(0, 12);
    const decryptedLen = await aesGcmDecrypt(len_key, len_iv, len_encrypted, auth_id);
    const header_length = (decryptedLen[0] << 8) | decryptedLen[1];
    return header_length > 0 && header_length < 4096;
  } catch (e) {
    return false;
  }
}

// Parse VMess AEAD header → returns { addressRemote, portRemote, rawClientData, version(AEAD response), isUDP }
async function parseVmessHeader(buffer) {
  const uuidBytes = toBuffer(UUID);
  if (buffer.length < 42) throw new Error("Data too short for VMess header");

  const auth_id = buffer.subarray(0, 16);
  let remaining = buffer.subarray(16);

  const len_encrypted = remaining.subarray(0, 18);
  remaining = remaining.subarray(18);

  const nonce = remaining.subarray(0, 8);
  remaining = remaining.subarray(8);

  const key = md5(concat(uuidBytes, VMESS_MD5_SALT));
  const mainKey = key;

  const len_key = kdf(key, [VMESS_SALT.LEN_KEY, auth_id, nonce]).subarray(0, 16);
  const len_iv  = kdf(key, [VMESS_SALT.LEN_IV, auth_id, nonce]).subarray(0, 12);
  const decryptedLen = await aesGcmDecrypt(len_key, len_iv, len_encrypted, auth_id);
  const header_length = (decryptedLen[0] << 8) | decryptedLen[1];

  if (remaining.length < header_length + 16) throw new Error("Data too short for VMess command");
  const cmd_encrypted = remaining.subarray(0, header_length + 16);
  const rawClientData = remaining.subarray(header_length + 16);

  const payload_key = kdf(mainKey, [VMESS_SALT.PAYLOAD_KEY, auth_id, nonce]).subarray(0, 16);
  const payload_iv  = kdf(mainKey, [VMESS_SALT.PAYLOAD_IV, auth_id, nonce]).subarray(0, 12);
  const cmdBuf = await aesGcmDecrypt(payload_key, payload_iv, cmd_encrypted, auth_id);

  if (cmdBuf[0] !== 1) throw new Error("Invalid VMess version");
  const iv = cmdBuf.subarray(1, 17);
  const keyResp = cmdBuf.subarray(17, 33);
  const responseAuth = cmdBuf[33];
  const command = cmdBuf[37];
  const portRemote = (cmdBuf[38] << 8) | cmdBuf[39];
  const addrType = cmdBuf[40];
  let addressRemote = "";

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
    throw new Error("Invalid VMess address type");
  }

  // Bangun AEAD response header (encrypted)
  const respKeyBase = sha256(keyResp).subarray(0, 16);
  const respIvBase  = sha256(iv).subarray(0, 16);

  const respLenKey = kdf(respKeyBase, [VMESS_SALT.RESP_LEN_KEY]).subarray(0, 16);
  const respLenIv  = kdf(respIvBase,  [VMESS_SALT.RESP_LEN_IV]).subarray(0, 12);
  const encryptedLength = await aesGcmEncrypt(respLenKey, respLenIv, new Uint8Array([0, 4]));

  const respPayloadKey = kdf(respKeyBase, [VMESS_SALT.RESP_KEY]).subarray(0, 16);
  const respPayloadIv  = kdf(respIvBase,  [VMESS_SALT.RESP_IV]).subarray(0, 12);
  const encryptedHeaderPayload = await aesGcmEncrypt(respPayloadKey, respPayloadIv, new Uint8Array([responseAuth, 0, 0, 0]));

  return {
    hasError: false,
    addressRemote,
    portRemote,
    rawClientData,
    version: concat(encryptedLength, encryptedHeaderPayload),
    isUDP: portRemote === 53,
  };
}

// ============== AUTO-DETECT ENDPOINT DARI REQUEST ==============
function getEndpointInfo(req) {
  const rawHost = (req.headers['x-forwarded-host'] || req.headers.host || 'localhost')
    .split(',')[0].trim();
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

async function tryResolveIP(domain, timeoutMs = 3000) {
  if (IPV4_REGEX.test(domain)) return domain;
  try {
    return await Promise.race([
      resolveHost(domain),
      new Promise((_, rej) => setTimeout(() => rej(new Error('timeout')), timeoutMs))
    ]);
  } catch { return domain; }
}

// ============== BUILD SUBSCRIPTION (TLS + non-TLS) ==============
async function buildSubscription(req) {
  await getisp();
  const { domain } = getEndpointInfo(req);
  const namePart = NAME ? `${NAME}-${ISP}` : ISP;
  const wsPath = `%2F${WSPATH}`;
  const isIP = IPV4_REGEX.test(domain);
  const ip = await tryResolveIP(domain);
  const ssB64 = Buffer.from(`none:${UUID}`).toString('base64');

  const vlessURI = (tls) => tls
    ? `vless://${UUID}@${ip}:443?path=${wsPath}&security=tls&encryption=none&host=${domain}&fp=chrome&type=ws&sni=${domain}#${namePart}-TLS`
    : `vless://${UUID}@${ip}:80?path=${wsPath}&security=none&encryption=none&host=${domain}&fp=chrome&type=ws#${namePart}`;

  const trojanURI = (tls) => tls
    ? `trojan://${UUID}@${ip}:443?path=${wsPath}&security=tls&host=${domain}&fp=chrome&type=ws&sni=${domain}#${namePart}-TLS`
    : `trojan://${UUID}@${ip}:80?path=${wsPath}&security=none&host=${domain}&fp=chrome&type=ws#${namePart}`;

  const ssURI = (tls) => tls
    ? `ss://${ssB64}@${ip}:443?plugin=v2ray-plugin;mode%3Dwebsocket;host%3D${domain};path%3D${wsPath};tls;sni%3D${domain};skip-cert-verify%3Dtrue;mux%3D0#${namePart}-TLS`
    : `ss://${ssB64}@${ip}:80?plugin=v2ray-plugin;mode%3Dwebsocket;host%3D${domain};path%3D${wsPath};skip-cert-verify%3Dtrue;mux%3D0#${namePart}`;

  const vmessURI = (tls) => {
    const cfg = tls
      ? { v:"2", ps:`${namePart}-TLS`, add:ip, port:"443", id:UUID, aid:"0", scy:"auto", net:"ws", type:"none", host:domain, path:`/${WSPATH}`, tls:"tls", sni:domain, alpn:"", fp:"chrome" }
      : { v:"2", ps:namePart,        add:ip, port:"80",  id:UUID, aid:"0", scy:"auto", net:"ws", type:"none", host:domain, path:`/${WSPATH}`, tls:"",    sni:"",     alpn:"", fp:"chrome" };
    return `vmess://${Buffer.from(JSON.stringify(cfg)).toString('base64')}`;
  };

  const configs = [];
  if (isIP) {
    configs.push(vlessURI(false), trojanURI(false), ssURI(false), vmessURI(false));
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

// HTTP 路由
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

// ============== HANDLER VLESS ==============
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

// ============== HANDLER TROJAN ==============
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

// ============== HANDLER SS ==============
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

// ============== HANDLER VMess (AEAD) ==============
async function handleVmessConnection(ws, msg) {
  try {
    const header = await parseVmessHeader(msg);

    if (header.isUDP) {
      logWarn('[VMess] UDP tidak didukung');
      ws.close();
      return true;
    }
    if (isBlockedDomain(header.addressRemote)) { ws.close(); return true; }

    log('[VMess] target:', header.addressRemote, 'port:', header.portRemote);

    // Kirim AEAD response header ke client (wajib sebelum data dari target)
    ws.send(header.version);

    const duplex = createWebSocketStream(ws);
    resolveHost(header.addressRemote)
      .then(ip => {
        net.connect({ host: ip, port: header.portRemote }, function () {
          if (header.rawClientData.length > 0) this.write(Buffer.from(header.rawClientData));
          duplex.on('error', () => {}).pipe(this).on('error', () => {}).pipe(duplex);
        }).on('error', () => {});
      })
      .catch(() => {
        net.connect({ host: header.addressRemote, port: header.portRemote }, function () {
          if (header.rawClientData.length > 0) this.write(Buffer.from(header.rawClientData));
          duplex.on('error', () => {}).pipe(this).on('error', () => {}).pipe(duplex);
        }).on('error', () => {});
      });
    return true;
  } catch (e) {
    logErr('[VMess] parse error:', e.message);
    return false;
  }
}

// ============== WebSocket dispatcher ==============
const wss = new WebSocket.Server({ server: httpServer });
wss.on('connection', (ws, req) => {
  const url = req.url || '';
  if (!url.startsWith(`/${WSPATH}`)) { ws.close(); return; }

  ws.once('message', async (msg) => {
    // Convert Buffer → Uint8Array (view, no copy) untuk VMess
    const u8 = new Uint8Array(msg.buffer, msg.byteOffset, msg.length);

    // 1) VLESS — cepat (byte0=0 + UUID match)
    if (msg.length > 17 && msg[0] === 0) {
      const id = msg.slice(1, 17);
      const isVless = id.every((v, i) => v == parseInt(uuid.substr(i * 2, 2), 16));
      if (isVless) { if (!handleVlsConnection(ws, msg)) ws.close(); return; }
    }

    // 2) Trojan — cepat (hash SHA224)
    if (msg.length >= 58) { if (handleTrojConnection(ws, msg)) return; }

    // 3) VMess AEAD — coba dekripsi header length
    if (await isVMess(u8)) {
      const ok = await handleVmessConnection(ws, u8);
      if (!ok) ws.close();
      return;
    }

    // 4) Shadowsocks — fallback
    if (msg.length > 0 && (msg[0] === 0x01 || msg[0] === 0x03 || msg[0] === 0x04)) {
      if (handleSsConnection(ws, msg)) return;
    }

    ws.close();
  }).on('error', () => {});
});

// start service
httpServer.listen(PORT, () => {
  console.log(`Server is running on ${PORT}`);
});