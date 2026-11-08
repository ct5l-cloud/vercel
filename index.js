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

// ============== Path per protokol (fixed) ==============
const WS_PATHS = {
  vless:  '/vless',
  trojan: '/trojan',
  ss:     '/ss',
};

// 辅助工具
let uuid = UUID.replace(/-/g, ""), ISP = '';
const DNS_SERVERS = ['8.8.4.4', '1.1.1.1'];
const BLOCKED_DOMAINS = [
  'speedtest.net', 'fast.com', 'speedtest.cn', 'speed.cloudflare.com', 'speedof.me',
  'testmy.net', 'bandwidth.place', 'speed.io', 'librespeed.org', 'speedcheck.org'
];
const IPV4_REGEX = /^(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)$/;

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

// ============== BUILD SUBSCRIPTION (TLS + non-TLS) ==============
async function buildSubscription(req) {
  await getisp();
  const { domain } = getEndpointInfo(req);
  const namePart = NAME ? `${NAME}-${ISP}` : ISP;
  const isIP = IPV4_REGEX.test(domain);
  const ssB64 = Buffer.from(`none:${UUID}`).toString('base64');

  // Pakai domain langsung — bukan IP
  const vlessURI = (tls) => tls
    ? `vless://${UUID}@${domain}:443?path=%2Fvless&security=tls&encryption=none&host=${domain}&fp=chrome&type=ws&sni=${domain}#${namePart}-TLS`
    : `vless://${UUID}@${domain}:80?path=%2Fvless&security=none&encryption=none&host=${domain}&fp=chrome&type=ws#${namePart}`;

  const trojanURI = (tls) => tls
    ? `trojan://${UUID}@${domain}:443?path=%2Ftrojan&security=tls&host=${domain}&fp=chrome&type=ws&sni=${domain}#${namePart}-TLS`
    : `trojan://${UUID}@${domain}:80?path=%2Ftrojan&security=none&host=${domain}&fp=chrome&type=ws#${namePart}`;

  const ssURI = (tls) => tls
    ? `ss://${ssB64}@${domain}:443?plugin=v2ray-plugin;mode%3Dwebsocket;host%3D${domain};path%3D%2Fss;tls;sni%3D${domain};skip-cert-verify%3Dtrue;mux%3D0#${namePart}-TLS`
    : `ss://${ssB64}@${domain}:80?plugin=v2ray-plugin;mode%3Dwebsocket;host%3D${domain};path%3D%2Fss;skip-cert-verify%3Dtrue;mux%3D0#${namePart}`;

  const configs = [];
  if (isIP) {
    configs.push(vlessURI(false), trojanURI(false), ssURI(false));
  } else {
    configs.push(
      vlessURI(true),  vlessURI(false),
      trojanURI(true), trojanURI(false),
      ssURI(true),     ssURI(false),
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

// ============== WebSocket dispatcher (by PATH) ==============
const wss = new WebSocket.Server({ server: httpServer });
wss.on('connection', (ws, req) => {
  const pathOnly = (req.url || '').split('?')[0];

  let handler;
  if (pathOnly === WS_PATHS.vless)        handler = handleVlsConnection;
  else if (pathOnly === WS_PATHS.trojan)  handler = handleTrojConnection;
  else if (pathOnly === WS_PATHS.ss)      handler = handleSsConnection;
  else { ws.close(); return; }

  ws.once('message', (msg) => {
    const ok = handler(ws, msg);
    if (!ok) ws.close();
  }).on('error', () => {});
});

// start service
httpServer.listen(PORT, () => {
  console.log(`Server is running on ${PORT}`);
  console.log(`WS paths → ${WS_PATHS.vless}, ${WS_PATHS.trojan}, ${WS_PATHS.ss}`);
});