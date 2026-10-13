const express = require('express');
const http = require('http');
const cors = require('cors');
const { Server } = require('socket.io');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const net = require('net');
const tls = require('tls');

const PORT = Number(process.env.PORT || 4000);
const ALLOWED_ORIGIN = process.env.CLIENT_ORIGIN || '*';
const ALLOWED_ORIGINS = ALLOWED_ORIGIN.split(',').map(value => value.trim()).filter(Boolean);
const corsOrigin = (origin, callback) => {
  // Allow server-to-server / health checks without an Origin header.
  if (!origin || ALLOWED_ORIGINS.includes('*') || ALLOWED_ORIGINS.includes(origin)) return callback(null, true);
  return callback(new Error('Origin not allowed by CORS'));
};

const app = express();
const server = http.createServer(app);

const io = new Server(server, {
  cors: { origin: corsOrigin, methods: ['GET', 'POST'] }
});

app.use(cors({ origin: corsOrigin }));
app.use(express.json({ limit: '1mb' }));

// A backend URL is not the game website. This root route avoids Express' confusing default response.
app.get('/', (_req, res) => res.json({
  service: 'Territory Lines API',
  ok: true,
  health: '/health',
  authConfig: '/api/auth/google/config'
}));

const GRID_SIZE = 4;
const TURN_TIME = 15000;
const RECONNECT_GRACE_MS = 60000;

const rooms = new Map();
const activeUsernames = new Map();
const matchmakingQueue = new Map();
const userDirectory = new Map();
const DATA_DIR = path.join(__dirname, 'data');
fs.mkdirSync(DATA_DIR, { recursive: true });
const USERS_FILE = path.join(DATA_DIR, 'users.json');

function loadAccounts() {
  try {
    const raw = JSON.parse(fs.readFileSync(USERS_FILE, 'utf8'));
    Object.entries(raw).forEach(([username, account]) => {
      userDirectory.set(username, { username, displayName: cleanName(account.displayName) || username, avatar: cleanAvatar(account.avatar), level: Math.max(1, Number(account.level) || 1), rating: Math.max(0, Number(account.rating) || 1000) });
    });
  } catch { /* first launch */ }
}
function readAccounts() { try { return JSON.parse(fs.readFileSync(USERS_FILE, 'utf8')); } catch { return {}; } }
function writeAccounts(accounts) { fs.writeFileSync(USERS_FILE, JSON.stringify(accounts, null, 2)); }
function hashPassword(password, salt = crypto.randomBytes(16).toString('hex')) { return `${salt}:${crypto.scryptSync(password, salt, 64).toString('hex')}`; }
function verifyPassword(password, stored) { try { const [salt, expected] = String(stored).split(':'); const actual = crypto.scryptSync(password, salt, 64).toString('hex'); return expected && crypto.timingSafeEqual(Buffer.from(actual, 'hex'), Buffer.from(expected, 'hex')); } catch { return false; } }
const AUTH_SECRET_FILE = path.join(DATA_DIR, '.auth-secret');
function loadAuthSecret() {
  if (process.env.AUTH_SECRET) return process.env.AUTH_SECRET;
  try {
    const existing = fs.readFileSync(AUTH_SECRET_FILE, 'utf8').trim();
    if (existing) return existing;
  } catch {}
  const generated = crypto.randomBytes(48).toString('hex');
  try { fs.writeFileSync(AUTH_SECRET_FILE, generated, { mode: 0o600 }); } catch {}
  return generated;
}
const TOKEN_SECRET = loadAuthSecret();
function makeToken(username) { const body = Buffer.from(JSON.stringify({ u: username, exp: Date.now() + 1000 * 60 * 60 * 24 * 30 })).toString('base64url'); const sig = crypto.createHmac('sha256', TOKEN_SECRET).update(body).digest('base64url'); return `${body}.${sig}`; }
function verifyToken(token) { try { const [body, sig] = String(token || '').split('.'); if (!body || !sig) return null; const expected = crypto.createHmac('sha256', TOKEN_SECRET).update(body).digest('base64url'); if (!crypto.timingSafeEqual(Buffer.from(sig), Buffer.from(expected))) return null; const data = JSON.parse(Buffer.from(body, 'base64url').toString('utf8')); return data.exp > Date.now() ? data.u : null; } catch { return null; } }
const friendRequests = new Map();
const friendships = new Map();

const normalizeUsername = value =>
  String(value || '').trim().toLowerCase();

const validUsername = value =>
  /^[a-z0-9_]{3,16}$/.test(value);

const normalizeEmail = value => String(value || '').trim().toLowerCase();
const validEmail = value => /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(normalizeEmail(value));

const cleanName = value =>
  String(value || '').trim().slice(0, 18);

const allowedAvatars = [
  '⚡', '🔥', '👑', '🐉', '🤖', '👾', '🚀', '🎯', '⚔️', '💀', '🛡️', '💎'
];

const cleanAvatar = value =>
  allowedAvatars.includes(value) ? value : '⚡';

loadAccounts();

function ensureSocialUser(username, profile = {}) {
  const key = normalizeUsername(username);
  if (!key) return null;
  if (!userDirectory.has(key)) {
    userDirectory.set(key, {
      username: key,
      displayName: cleanName(profile.displayName) || key,
      avatar: cleanAvatar(profile.avatar),
      level: Math.max(1, Number(profile.level) || 1),
      rating: Math.max(0, Number(profile.rating) || 1000)
    });
  } else {
    const user = userDirectory.get(key);
    if (profile.displayName) user.displayName = cleanName(profile.displayName);
    if (profile.avatar) user.avatar = cleanAvatar(profile.avatar);
  }
  if (!friendRequests.has(key)) friendRequests.set(key, new Set());
  if (!friendships.has(key)) friendships.set(key, new Set());
  return userDirectory.get(key);
}

function socialSnapshot(username) {
  const key = normalizeUsername(username);
  const user = ensureSocialUser(key);
  const friends = [...(friendships.get(key) || [])].map(friend => {
    const data = userDirectory.get(friend) || { username: friend, displayName: friend, avatar: '⚡', level: 1, rating: 1000 };
    return { ...data, online: activeUsernames.has(friend) };
  });
  const incoming = [...(friendRequests.get(key) || [])].map(from => {
    const data = userDirectory.get(from) || { username: from, displayName: from, avatar: '⚡', level: 1, rating: 1000 };
    return { ...data };
  });
  const outgoing = [];
  for (const [target, requests] of friendRequests.entries()) {
    if (requests.has(key)) outgoing.push(userDirectory.get(target) || { username: target, displayName: target, avatar: '⚡', level: 1, rating: 1000 });
  }
  return { friends, incoming, outgoing, self: user };
}

function emitSocial(username) {
  const socketId = activeUsernames.get(normalizeUsername(username));
  if (!socketId) return;
  const target = io.sockets.sockets.get(socketId);
  if (target) target.emit('social_update', socialSnapshot(username));
}

const passwordResetCodes = new Map();
const resetRequestTimes = new Map();
const googleOAuthStates = new Map();
const googleLoginCodes = new Map();
const OTP_TTL_MS = 10 * 60 * 1000;

function smtpCredentials() {
  return {
    user: process.env.SMTP_USER || process.env.EMAIL_USER || process.env.GMAIL_USER,
    pass: process.env.SMTP_PASS || process.env.SMTP_PASSWORD || process.env.EMAIL_PASS || process.env.EMAIL_PASSWORD || process.env.GMAIL_APP_PASSWORD,
    host: process.env.SMTP_HOST || 'smtp.gmail.com',
    port: Number(process.env.SMTP_PORT || 465)
  };
}

async function sendTransactionalEmail({ from, to, subject, text, html }) {
  // Render Free blocks outbound SMTP ports, so prefer Resend's HTTPS API when configured.
  const apiKey = process.env.RESEND_API_KEY;
  if (apiKey) {
    const sender = process.env.RESEND_FROM || 'Territory Lines <onboarding@resend.dev>';
    const response = await fetch('https://api.resend.com/emails', {
      method: 'POST',
      headers: {
        Authorization: `Bearer ${apiKey}`,
        'Content-Type': 'application/json'
      },
      body: JSON.stringify({
        from: sender,
        to: [to],
        subject,
        text,
        html
      })
    });
    const result = await response.json().catch(() => ({}));
    if (!response.ok) {
      const detail = result?.message || result?.name || `HTTP ${response.status}`;
      throw new Error(`Resend email API failed (${response.status}): ${detail}`);
    }
    return result;
  }
  // Backward-compatible fallback for deployments that still use SMTP.
  return sendSmtpEmail({ from, to, subject, text, html });
}

function sendSmtpEmail({ from, to, subject, text, html }) {
  const config = smtpCredentials();
  if (!config.user || !config.pass) return Promise.reject(new Error('SMTP credentials are missing.'));
  if (![465, 587].includes(config.port)) return Promise.reject(new Error('SMTP_PORT must be 465 or 587.'));
  return new Promise((resolve, reject) => {
    let socket;
    let buffer = '';
    let lines = [];
    let responses = [];
    let waiters = [];
    let attachedHandlers = null;
    let settled = false;
    const timeout = setTimeout(() => finish(new Error('SMTP connection timed out.')), 20000);
    function finish(error) {
      if (settled) return;
      settled = true;
      clearTimeout(timeout);
      try { socket?.end(); } catch {}
      if (error) reject(error); else resolve();
    }
    function attach(target) {
      socket = target;
      const onTimeout = () => finish(new Error('SMTP connection timed out.'));
      const onData = chunk => {
        buffer += chunk.toString('utf8');
        let index;
        while ((index = buffer.indexOf('\r\n')) >= 0) {
          const line = buffer.slice(0, index);
          buffer = buffer.slice(index + 2);
          lines.push(line);
          if (/^\d{3} /.test(line)) {
            const response = { code: Number(line.slice(0, 3)), text: lines.join('\n') };
            lines = [];
            const waiter = waiters.shift();
            if (waiter) waiter(response); else responses.push(response);
          }
        }
      };
      const onError = error => finish(error);
      const onEnd = () => { if (!settled) finish(new Error('SMTP server closed the connection.')); };
      attachedHandlers = { target, onTimeout, onData, onError, onEnd };
      target.setTimeout?.(18000);
      target.on('timeout', onTimeout);
      target.on('data', onData);
      target.on('error', onError);
      target.on('end', onEnd);
    }
    function detach(target) {
      if (!attachedHandlers || attachedHandlers.target !== target) return;
      target.off('timeout', attachedHandlers.onTimeout);
      target.off('data', attachedHandlers.onData);
      target.off('error', attachedHandlers.onError);
      target.off('end', attachedHandlers.onEnd);
      attachedHandlers = null;
    }
    function readResponse() {
      if (responses.length) return Promise.resolve(responses.shift());
      return new Promise(resolveResponse => waiters.push(resolveResponse));
    }
    async function command(value, expected) {
      socket.write(`${value}\r\n`);
      const response = await readResponse();
      if (!expected.includes(response.code)) throw new Error(`SMTP command failed (${response.code}): ${response.text}`);
      return response;
    }
    const b64 = value => Buffer.from(String(value), 'utf8').toString('base64');
    const encodedSubject = `=?UTF-8?B?${b64(subject)}?=`;
    const boundary = `tl_${crypto.randomBytes(12).toString('hex')}`;
    const safeText = String(text || '').replace(/\r?\n/g, '\r\n');
    const safeHtml = String(html || '').replace(/\r?\n/g, '\r\n');
    const mime = [
      `From: ${from}`, `To: ${to}`, `Subject: ${encodedSubject}`, 'MIME-Version: 1.0',
      `Content-Type: multipart/alternative; boundary="${boundary}"`, '',
      `--${boundary}`, 'Content-Type: text/plain; charset=UTF-8', 'Content-Transfer-Encoding: 8bit', '', safeText, '',
      `--${boundary}`, 'Content-Type: text/html; charset=UTF-8', 'Content-Transfer-Encoding: 8bit', '', safeHtml, '',
      `--${boundary}--`, ''
    ].join('\r\n').replace(/(^|\r\n)\./g, '$1..');
    (async () => {
      try {
        if (config.port === 465) {
          attach(tls.connect({ host: config.host, port: config.port, servername: config.host }));
        } else {
          attach(net.connect({ host: config.host, port: config.port }));
        }
        await readResponse(); // greeting
        await command(`EHLO ${process.env.SMTP_HELO_NAME || 'territory-lines'}`, [250]);
        if (config.port === 587) {
          await command('STARTTLS', [220]);
          const rawSocket = socket;
          detach(rawSocket);
          const secureSocket = tls.connect({ socket: rawSocket, servername: config.host });
          buffer = ''; lines = []; responses = []; waiters = [];
          attach(secureSocket);
          await new Promise((resolveSecure, rejectSecure) => {
            secureSocket.once('secureConnect', resolveSecure);
            secureSocket.once('error', rejectSecure);
          });
          await command(`EHLO ${process.env.SMTP_HELO_NAME || 'territory-lines'}`, [250]);
        }
        await command('AUTH LOGIN', [334]);
        await command(b64(config.user), [334]);
        await command(b64(config.pass.replace(/\s/g, '')), [235]);
        const envelopeFrom = String(from).match(/<([^>]+)>/)?.[1] || String(from);
        await command(`MAIL FROM:<${envelopeFrom}>`, [250]);
        await command(`RCPT TO:<${to}>`, [250, 251]);
        await command('DATA', [354]);
        socket.write(`${mime}\r\n.\r\n`);
        const sent = await readResponse();
        if (sent.code !== 250) throw new Error(`SMTP message rejected (${sent.code}): ${sent.text}`);
        try { await command('QUIT', [221]); } catch {}
        finish();
      } catch (error) { finish(error); }
    })();
  });
}

function makeGoogleUsername(email, accounts) {
  const local = normalizeEmail(email).split('@')[0].toLowerCase().replace(/[^a-z0-9_]/g, '_').replace(/^_+|_+$/g, '').slice(0, 12) || 'player';
  let base = local.length >= 3 ? local : `${local}player`.slice(0, 12);
  let candidate = base;
  let n = 2;
  while (accounts[candidate]) {
    const suffix = String(n++);
    candidate = `${base.slice(0, 16 - suffix.length)}${suffix}`;
  }
  return candidate;
}

function upsertGoogleAccount(google) {
  const email = normalizeEmail(google?.email);
  if (!google?.sub || !validEmail(email) || ![true, 'true'].includes(google.email_verified)) throw new Error('Google account is not verified.');
  const accounts = readAccounts();
  let account = Object.values(accounts).find(item => normalizeEmail(item.email) === email);
  if (!account) {
    const username = makeGoogleUsername(email, accounts);
    const displayName = cleanName(google.name || google.given_name || username) || username;
    account = { username, email, displayName, avatar: '⚡', googleId: google.sub, level: 1, rating: 1000, createdAt: new Date().toISOString(), authProvider: 'google' };
    accounts[username] = account;
  } else {
    account.googleId = google.sub;
    account.authProvider = account.passwordHash ? (account.authProvider || 'email') : 'google';
    if (!account.displayName && google.name) account.displayName = cleanName(google.name);
  }
  writeAccounts(accounts);
  ensureSocialUser(account.username, account);
  return account;
}

function publicAuthProfile(account) {
  return { username: account.username, email: account.email || '', displayName: account.displayName, avatar: account.avatar || '⚡', level: account.level || 1, rating: account.rating || 1000 };
}

function createGoogleLoginCode(account) {
  const code = crypto.randomBytes(32).toString('base64url');
  googleLoginCodes.set(code, { token: makeToken(account.username), profile: publicAuthProfile(account), expiresAt: Date.now() + 60 * 1000 });
  return code;
}

app.get('/api/auth/google/config', (req, res) => res.json({ clientId: process.env.GOOGLE_CLIENT_ID || '' }));

// Redirect-based OAuth flow for the Android app and existing Google OAuth client.
app.get('/api/auth/google', (req, res) => {
  const clientId = process.env.GOOGLE_CLIENT_ID;
  const redirectUri = process.env.GOOGLE_REDIRECT_URI;
  if (!clientId || !process.env.GOOGLE_CLIENT_SECRET || !redirectUri) {
    return res.status(503).send('Google OAuth is not configured. Set GOOGLE_CLIENT_ID, GOOGLE_CLIENT_SECRET and GOOGLE_REDIRECT_URI on the server.');
  }
  const platform = String(req.query?.platform || '').toLowerCase() === 'android' ? 'android' : 'web';
  const webReturnUrl = process.env.GOOGLE_WEB_RETURN_URL || (ALLOWED_ORIGIN !== '*' ? ALLOWED_ORIGIN.split(',')[0].trim() : '');
  if (platform === 'web' && !webReturnUrl) return res.status(503).send('Set GOOGLE_WEB_RETURN_URL or CLIENT_ORIGIN to complete web OAuth.');
  const state = crypto.randomBytes(24).toString('base64url');
  googleOAuthStates.set(state, { platform, expiresAt: Date.now() + 10 * 60 * 1000 });
  const authorization = new URL('https://accounts.google.com/o/oauth2/v2/auth');
  authorization.searchParams.set('client_id', clientId);
  authorization.searchParams.set('redirect_uri', redirectUri);
  authorization.searchParams.set('response_type', 'code');
  authorization.searchParams.set('scope', 'openid email profile');
  authorization.searchParams.set('state', state);
  authorization.searchParams.set('prompt', 'select_account');
  res.redirect(302, authorization.toString());
});

app.get('/api/auth/google/callback', async (req, res) => {
  const state = String(req.query?.state || '');
  const savedState = googleOAuthStates.get(state);
  googleOAuthStates.delete(state);
  if (!savedState || savedState.expiresAt < Date.now()) return res.status(400).send('Google sign-in expired. Return to Territory Lines and try again.');
  if (req.query?.error) return res.status(401).send('Google sign-in was cancelled. Return to Territory Lines to try again.');
  const code = String(req.query?.code || '');
  if (!code) return res.status(400).send('Google did not return an authorization code.');
  try {
    const redirectUri = process.env.GOOGLE_REDIRECT_URI;
    const tokenResponse = await fetch('https://oauth2.googleapis.com/token', {
      method: 'POST',
      headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
      body: new URLSearchParams({ code, client_id: process.env.GOOGLE_CLIENT_ID, client_secret: process.env.GOOGLE_CLIENT_SECRET, redirect_uri: redirectUri, grant_type: 'authorization_code' })
    });
    const tokens = await tokenResponse.json().catch(() => ({}));
    if (!tokenResponse.ok || !tokens.access_token) return res.status(401).send('Google could not verify this sign-in. Return to Territory Lines and try again.');
    const userResponse = await fetch('https://openidconnect.googleapis.com/v1/userinfo', { headers: { Authorization: `Bearer ${tokens.access_token}` } });
    const google = await userResponse.json().catch(() => ({}));
    if (!userResponse.ok || ![true, 'true'].includes(google.email_verified)) return res.status(401).send('Google did not provide a verified email address.');
    const account = upsertGoogleAccount(google);
    const loginCode = createGoogleLoginCode(account);
    const returnTo = savedState.platform === 'android'
      ? (process.env.GOOGLE_APP_RETURN_URL || 'territorylines://auth')
      : (process.env.GOOGLE_WEB_RETURN_URL || (ALLOWED_ORIGIN !== '*' ? ALLOWED_ORIGIN.split(',')[0].trim() : ''));
    const returnUrl = new URL(returnTo);
    returnUrl.searchParams.set(savedState.platform === 'android' ? 'code' : 'google_code', loginCode);
    return res.redirect(302, returnUrl.toString());
  } catch (error) {
    console.error('Google OAuth callback error:', error?.message || error);
    return res.status(502).send('Google sign-in could not be completed. Return to Territory Lines and try again.');
  }
});

app.post('/api/auth/google/exchange', (req, res) => {
  const code = String(req.body?.code || '');
  const session = googleLoginCodes.get(code);
  googleLoginCodes.delete(code);
  if (!session || session.expiresAt < Date.now()) return res.status(401).json({ message: 'Google sign-in link expired. Please try again.' });
  res.json({ token: session.token, profile: session.profile });
});

app.post('/api/auth/google', async (req, res) => {
  try {
    const credential = String(req.body?.credential || '');
    if (!credential) return res.status(400).json({ message: 'Google did not return a sign-in credential.' });
    if (!process.env.GOOGLE_CLIENT_ID) return res.status(503).json({ message: 'Google sign-in is not configured on the server yet.' });
    const response = await fetch(`https://oauth2.googleapis.com/tokeninfo?id_token=${encodeURIComponent(credential)}`);
    const google = await response.json().catch(() => ({}));
    if (!response.ok || google.aud !== process.env.GOOGLE_CLIENT_ID || ![true, 'true'].includes(google.email_verified) || !validEmail(google.email)) {
      return res.status(401).json({ message: 'Google sign-in could not be verified. Please try again.' });
    }
    const account = upsertGoogleAccount(google);
    return res.json({ token: makeToken(account.username), profile: publicAuthProfile(account) });
  } catch (error) {
    console.error('Google auth error:', error?.message || error);
    return res.status(502).json({ message: 'Could not contact Google to verify sign-in. Please try again.' });
  }
});

app.post('/api/auth/password-reset/request', async (req, res) => {
  const email = normalizeEmail(req.body?.email);
  if (!validEmail(email)) return res.status(400).json({ message: 'Enter a valid email address.' });
  const now = Date.now();
  const lastRequest = resetRequestTimes.get(email) || 0;
  if (now - lastRequest < 45 * 1000) return res.status(429).json({ message: 'Please wait a little before requesting another code.' });
  resetRequestTimes.set(email, now);
  const smtp = smtpCredentials();
  if (!process.env.RESEND_API_KEY && (!smtp.user || !smtp.pass)) {
    return res.status(503).json({ message: 'Email delivery is not configured. Set RESEND_API_KEY or configure SMTP_USER and SMTP_PASS on the server.' });
  }
  const accounts = readAccounts();
  const account = Object.values(accounts).find(item => normalizeEmail(item.email) === email);
  // Same response for known and unknown addresses to avoid account enumeration.
  if (!account) return res.json({ message: 'If an account exists for this email, a verification code has been sent.' });
  const code = String(crypto.randomInt(0, 1000000)).padStart(6, '0');
  passwordResetCodes.set(email, { code, expiresAt: now + OTP_TTL_MS, attempts: 0 });
  try {
    const from = process.env.RESEND_FROM || process.env.SMTP_FROM || smtp.user || 'Territory Lines <onboarding@resend.dev>';
    await sendTransactionalEmail({
      from, to: email, subject: 'Your Territory Lines password reset code',
      text: `Your Territory Lines verification code is ${code}. It expires in 10 minutes. If you did not request this, you can ignore this email.`,
      html: `<div style="font-family:Arial,sans-serif;max-width:520px;margin:auto;color:#263940"><h2>Territory Lines</h2><p>Use this verification code to reset your password:</p><div style="font-size:32px;font-weight:700;letter-spacing:8px;padding:18px;background:#f1f5f2;border-radius:10px;text-align:center">${code}</div><p>This code expires in 10 minutes. If you did not request this, ignore this email.</p></div>`
    });
    return res.json({ message: 'If an account exists for this email, a verification code has been sent.' });
  } catch (error) {
    passwordResetCodes.delete(email);
    console.error('Password reset email error:', error?.message || error);
    return res.status(502).json({ message: 'Could not send the email right now. Check SMTP settings and try again.' });
  }
});

app.post('/api/auth/password-reset/confirm', (req, res) => {
  const email = normalizeEmail(req.body?.email);
  const code = String(req.body?.code || '').trim();
  const password = String(req.body?.password || '');
  if (!validEmail(email)) return res.status(400).json({ message: 'Enter a valid email address.' });
  if (!/^\d{6}$/.test(code)) return res.status(400).json({ message: 'Enter the 6-digit verification code.' });
  if (password.length < 8) return res.status(400).json({ message: 'Password must be at least 8 characters.' });
  const stored = passwordResetCodes.get(email);
  if (!stored || stored.expiresAt < Date.now()) { passwordResetCodes.delete(email); return res.status(400).json({ message: 'That code has expired. Request a new one.' }); }
  stored.attempts += 1;
  if (stored.attempts > 5) { passwordResetCodes.delete(email); return res.status(429).json({ message: 'Too many attempts. Request a new code.' }); }
  if (stored.code !== code) return res.status(400).json({ message: 'That verification code is incorrect.' });
  const accounts = readAccounts();
  const account = Object.values(accounts).find(item => normalizeEmail(item.email) === email);
  if (!account) { passwordResetCodes.delete(email); return res.status(400).json({ message: 'Unable to reset this account. Request a new code.' }); }
  account.passwordHash = hashPassword(password);
  account.authProvider = account.googleId ? 'google+email' : 'email';
  writeAccounts(accounts);
  passwordResetCodes.delete(email);
  resetRequestTimes.delete(email);
  return res.json({ message: 'Password updated. You can now sign in.' });
});

app.post('/api/auth/register', (req, res) => {
  const username = normalizeUsername(req.body?.username);
  const email = normalizeEmail(req.body?.email);
  const password = String(req.body?.password || '');
  const displayName = cleanName(req.body?.displayName) || username;
  if (!validUsername(username)) return res.status(400).json({ message: 'Username must be 3–16 characters using letters, numbers or _.' });
  if (!validEmail(email)) return res.status(400).json({ message: 'Enter a valid email address.' });
  if (password.length < 8) return res.status(400).json({ message: 'Password must be at least 8 characters.' });
  const accounts = readAccounts();
  if (accounts[username]) return res.status(409).json({ message: 'That username is already taken.' });
  if (Object.values(accounts).some(account => normalizeEmail(account.email) === email)) return res.status(409).json({ message: 'That email is already linked to an account.' });
  const account = { username, email, displayName, avatar: '⚡', passwordHash: hashPassword(password), level: 1, rating: 1000, createdAt: new Date().toISOString() };
  accounts[username] = account; writeAccounts(accounts);
  ensureSocialUser(username, account);
  res.json({ token: makeToken(username), profile: { username, email, displayName, avatar: account.avatar, level: 1, rating: 1000 } });
});

app.post('/api/auth/login', (req, res) => {
  const identifier = normalizeEmail(req.body?.identifier || req.body?.email || req.body?.username);
  const password = String(req.body?.password || '');
  const accounts = readAccounts();
  const account = Object.values(accounts).find(item => normalizeEmail(item.email) === identifier) || accounts[normalizeUsername(identifier)];
  if (!account || !verifyPassword(password, account.passwordHash)) return res.status(401).json({ message: 'Invalid email/username or password.' });
  ensureSocialUser(account.username, account);
  res.json({ token: makeToken(account.username), profile: { username: account.username, email: account.email || '', displayName: account.displayName, avatar: account.avatar || '⚡', level: account.level || 1, rating: account.rating || 1000 } });
});

app.get('/api/auth/me', (req, res) => {
  const username = verifyToken(String(req.headers.authorization || '').replace(/^Bearer\s+/i, ''));
  const account = username && readAccounts()[username];
  if (!account) return res.status(401).json({ message: 'Session expired.' });
  res.json({ profile: { username, email: account.email || '', displayName: account.displayName, avatar: account.avatar || '⚡', level: account.level || 1, rating: account.rating || 1000 } });
});

app.get('/health', (req, res) => {
  res.json({
    ok: true,
    rooms: rooms.size,
    activeUsers: activeUsernames.size,
    matchmaking: matchmakingQueue.size
  });
});

/* =========================================================
   BOARD & GAME LOGIC
========================================================= */

function emptyBoard() {
  return {
    hLines: Array.from({ length: GRID_SIZE + 1 }, () => Array(GRID_SIZE).fill(0)),
    vLines: Array.from({ length: GRID_SIZE }, () => Array(GRID_SIZE + 1).fill(0)),
    boxes: Array.from({ length: GRID_SIZE }, () => Array(GRID_SIZE).fill(0))
  };
}

function cloneBoard(board) {
  return {
    hLines: board.hLines.map(row => [...row]),
    vLines: board.vLines.map(row => [...row]),
    boxes: board.boxes.map(row => [...row])
  };
}

function scores(boxes) {
  const result = { p1: 0, p2: 0, p3: 0, p4: 0 };
  boxes.forEach(row => row.forEach(value => {
    if (value >= 1 && value <= 4) result[`p${value}`] += 1;
  }));
  return result;
}

function finished(boxes) {
  return boxes.every(row => row.every(cell => cell !== 0));
}

function availableMoves(board) {
  const moves = [];
  for (let r = 0; r <= GRID_SIZE; r++) {
    for (let c = 0; c < GRID_SIZE; c++) {
      if (board.hLines[r][c] === 0) moves.push({ type: 'H', r, c });
    }
  }
  for (let r = 0; r < GRID_SIZE; r++) {
    for (let c = 0; c <= GRID_SIZE; c++) {
      if (board.vLines[r][c] === 0) moves.push({ type: 'V', r, c });
    }
  }
  return moves;
}

function applyMove(board, move, playerIndex) {
  if (
    !move ||
    !['H', 'V'].includes(move.type) ||
    !Number.isInteger(move.r) ||
    !Number.isInteger(move.c)
  ) {
    return null;
  }

  const next = cloneBoard(board);

  if (move.type === 'H') {
    if (
      move.r < 0 ||
      move.r > GRID_SIZE ||
      move.c < 0 ||
      move.c >= GRID_SIZE ||
      next.hLines[move.r][move.c] !== 0
    ) {
      return null;
    }
    next.hLines[move.r][move.c] = playerIndex + 1;
  } else {
    if (
      move.r < 0 ||
      move.r >= GRID_SIZE ||
      move.c < 0 ||
      move.c > GRID_SIZE ||
      next.vLines[move.r][move.c] !== 0
    ) {
      return null;
    }
    next.vLines[move.r][move.c] = playerIndex + 1;
  }

  const closed = [];
  for (let r = 0; r < GRID_SIZE; r++) {
    for (let c = 0; c < GRID_SIZE; c++) {
      if (next.boxes[r][c] !== 0) continue;
      const complete =
        next.hLines[r][c] &&
        next.hLines[r + 1][c] &&
        next.vLines[r][c] &&
        next.vLines[r][c + 1];

      if (complete) {
        next.boxes[r][c] = playerIndex + 1;
        closed.push({ r, c });
      }
    }
  }

  return {
    board: next,
    closed,
    extraTurn: closed.length > 0
  };
}

function chooseTimeoutMove(board) {
  const moves = availableMoves(board);
  for (const move of moves) {
    const result = applyMove(board, move, 0);
    if (result?.closed.length) return move;
  }
  if (!moves.length) return null;
  return moves[Math.floor(Math.random() * moves.length)];
}

/* =========================================================
   PLAYER & USERNAME HELPERS
========================================================= */

function publicPlayers(room) {
  return room.players.map(player => ({
    id: player.id,
    playerId: player.playerId,
    index: player.index,
    displayName: player.displayName,
    username: player.username,
    avatar: player.avatar,
    connected: player.connected !== false,
    reconnectDeadline: player.reconnectDeadline || 0
  }));
}

function reserveUsername(socket, username) {
  const normalized = normalizeUsername(username);
  if (!validUsername(normalized)) {
    return {
      ok: false,
      message: 'Username must be 3–16 characters using letters, numbers or _.'
    };
  }

  const existing = activeUsernames.get(normalized);
  if (existing && existing !== socket.id) {
    const existingSocket = io.sockets.sockets.get(existing);
    if (existingSocket) {
      return {
        ok: false,
        message: 'That username is already being used.'
      };
    }
    // The previous socket disappeared without completing cleanup (for example during a network drop).
    // Release the stale reservation so the authenticated player can recover immediately.
    activeUsernames.delete(normalized);
  }

  const oldUsername = socket.data.username;
  if (oldUsername && oldUsername !== normalized && activeUsernames.get(oldUsername) === socket.id) {
    activeUsernames.delete(oldUsername);
  }

  activeUsernames.set(normalized, socket.id);
  socket.data.username = normalized;
  ensureSocialUser(normalized, { displayName: socket.data.displayName, avatar: socket.data.avatar });
  return { ok: true, username: normalized };
}

function releaseUsername(socket) {
  const username = socket.data.username;
  if (username && activeUsernames.get(username) === socket.id) {
    activeUsernames.delete(username);
  }
  socket.data.username = null;
}

function playerPayload(socket, payload) {
  const displayName = cleanName(payload?.displayName);
  const username = normalizeUsername(payload?.username);
  const playerId = String(payload?.playerId || socket.id);

  if (displayName.length < 2) {
    return { error: 'Display name must be at least 2 characters.' };
  }
  if (!validUsername(username)) {
    return { error: 'Username must be 3–16 characters using letters, numbers or _.' };
  }
  if (normalizeUsername(socket.data.username) !== username) return { error: 'Authentication required for this username.' };

  if (socket.data.username !== username) {
    const reservation = reserveUsername(socket, username);
    if (!reservation.ok) return { error: reservation.message };
  }

  socket.data.displayName = displayName;
  socket.data.avatar = cleanAvatar(payload?.avatar);
  socket.data.level = Math.max(1, Number(payload?.level) || 1);
  socket.data.rating = Math.max(0, Number(payload?.rating) || 1000);
  ensureSocialUser(username, { displayName, avatar: payload?.avatar, level: socket.data.level, rating: socket.data.rating });

  return {
    player: {
      id: socket.id,
      playerId,
      index: 0,
      displayName,
      username,
      avatar: cleanAvatar(payload?.avatar),
      level: socket.data.level || 1,
      rating: socket.data.rating || 1000,
      connected: true
    }
  };
}

/* =========================================================
   ROOM MANAGEMENT
========================================================= */

function generateRoomCode() {
  let code;
  do {
    code = String(Math.floor(1000 + Math.random() * 9000));
  } while (rooms.has(code));
  return code;
}

function clearTimer(room) {
  if (room.turnTimer) clearTimeout(room.turnTimer);
  room.turnTimer = null;
}

function roomState(room) {
  return {
    hLines: room.board.hLines,
    vLines: room.board.vLines,
    boxes: room.board.boxes,
    turn: room.turn,
    deadline: room.deadline
  };
}

/* =========================================================
   TURN TIMERS & GAME LIFECYCLE
========================================================= */

function startTimer(room) {
  clearTimer(room);
  if (room.finished || room.players.length < 2 || room.pausedForReconnect) return;

  room.deadline = Date.now() + TURN_TIME;
  io.to(room.id).emit('turn_timer', {
    turn: room.turn,
    deadline: room.deadline
  });

  room.turnTimer = setTimeout(() => {
    if (!rooms.has(room.id) || room.finished || room.players.length < 2) return;

    const move = chooseTimeoutMove(room.board);
    if (!move) {
      finishGame(room);
      return;
    }

    processMove(room, room.turn, move, true);
  }, TURN_TIME + 100);
}

function finishGame(room) {
  clearTimer(room);
  room.finished = true;
  room.deadline = 0;

  const finalScores = scores(room.board.boxes);
  let winnerIndex = null;
  const scoreList = room.players.map(p => ({ index: p.index, score: finalScores[`p${p.index + 1}`] || 0 }));
  scoreList.sort((a, b) => b.score - a.score);
  if (scoreList.length && (scoreList.length === 1 || scoreList[0].score > scoreList[1].score)) winnerIndex = scoreList[0].index;

  io.to(room.id).emit('game_over', {
    scores: finalScores,
    winnerIndex
  });
}

function processMove(room, playerIndex, move, timedOut = false) {
  if (room.finished || room.players.length < 2 || room.turn !== playerIndex) {
    return false;
  }

  const result = applyMove(room.board, move, playerIndex);
  if (!result) return false;

  room.board = result.board;
  room.turn = result.extraTurn ? playerIndex : (playerIndex + 1) % room.players.length;

  io.to(room.id).emit('state_update', {
    state: roomState(room),
    move,
    closed: result.closed,
    timedOut
  });

  if (finished(room.board.boxes)) {
    finishGame(room);
  } else {
    startTimer(room);
  }

  return true;
}

/* =========================================================
   PRIVATE ROOM & MATCHMAKING
========================================================= */

function createPrivateRoom(socket, payload) {
  const data = playerPayload(socket, payload);
  if (data.error) return data;

  const player = data.player;
  player.index = 0;

  const id = generateRoomCode();
  const maxPlayers = [2, 3, 4].includes(Number(payload?.maxPlayers)) ? Number(payload.maxPlayers) : 2;
  const room = {
    id,
    mode: 'friends',
    maxPlayers,
    hostUsername: player.username,
    started: false,
    players: [player],
    board: emptyBoard(),
    turn: 0,
    deadline: 0,
    turnTimer: null,
    finished: false,
    rematchRequests: new Set(),
    reconnectTimers: new Map(),
    pausedForReconnect: false
  };

  rooms.set(id, room);
  socket.data.roomId = id;
  socket.data.matchMode = 'friends';
  socket.join(id);

  return { room, player };
}

function startPrivateRoom(room) {
  if (!room || room.started || room.players.length < 2) return false;
  room.started = true;
  room.board = emptyBoard();
  room.turn = 0;
  room.finished = false;
  room.deadline = 0;
  io.to(room.id).emit('game_start', { roomId: room.id, players: publicPlayers(room), state: roomState(room) });
  startTimer(room);
  return true;
}

function removePlayer(socketId, reason, isDisconnect = false) {
  const socket = io.sockets.sockets.get(socketId);
  const roomId = socket?.data?.roomId;
  if (!roomId) return;

  const room = rooms.get(roomId);
  if (!room) return;

  const playerIndex = room.players.findIndex(p => p.id === socketId);
  if (playerIndex < 0) return;

  const player = room.players[playerIndex];

  // Temporary connection loss: keep the player in the room for a full 60-second recovery window.
  // The room, board, turn and playerId stay alive so a browser/app restart can restore the match.
  if (isDisconnect && (room.mode === 'online' || (room.mode === 'friends' && room.started)) && !room.finished && room.players.length === 2) {
    player.connected = false;
    room.pausedForReconnect = true;
    clearTimer(room);
    player.reconnectDeadline = Date.now() + RECONNECT_GRACE_MS;
    io.to(room.id).emit('opponent_disconnected', {
      playerId: player.playerId,
      deadline: player.reconnectDeadline,
      seconds: Math.ceil(RECONNECT_GRACE_MS / 1000),
      message: 'Opponent disconnected. You can wait for them to reconnect.'
    });

    if (!room.reconnectTimers) room.reconnectTimers = new Map();
    if (room.reconnectTimers.has(player.playerId)) clearTimeout(room.reconnectTimers.get(player.playerId));

    const timeout = setTimeout(() => {
      room.reconnectTimers.delete(player.playerId);
      player.reconnectDeadline = 0;
      if (activeUsernames.get(player.username) === socketId) activeUsernames.delete(player.username);
      forceRemovePlayer(room, socketId, 'Opponent failed to reconnect within 60 seconds.');
    }, RECONNECT_GRACE_MS);

    room.reconnectTimers.set(player.playerId, timeout);
    return;
  }

  forceRemovePlayer(room, socketId, reason);
}

function forceRemovePlayer(room, socketId, reason) {
  const index = room.players.findIndex(p => p.id === socketId);
  const removedPlayer = index >= 0 ? room.players[index] : null;
  if (index >= 0) {
    room.players.splice(index, 1);
  }

  if (removedPlayer && room.reconnectTimers?.has(removedPlayer.playerId)) {
    clearTimeout(room.reconnectTimers.get(removedPlayer.playerId));
    room.reconnectTimers.delete(removedPlayer.playerId);
  }

  clearTimer(room);

  const leavingSocket = io.sockets.sockets.get(socketId);
  if (leavingSocket) {
    leavingSocket.leave(room.id);
    leavingSocket.data.roomId = null;
    leavingSocket.data.matchMode = null;
  }

  if (room.mode === 'friends') {
    room.board = emptyBoard();
    room.turn = 0;
    room.deadline = 0;
    room.finished = false;
    room.started = false;
    room.rematchRequests.clear();

    if (!room.players.length) {
      rooms.delete(room.id);
      return;
    }

    room.players.forEach((player, index) => { player.index = index; });
    room.hostUsername = room.players[0].username;
    io.to(room.id).emit('opponent_left', {
      roomId: room.id,
      players: publicPlayers(room),
      reason: reason || 'A player left. The room is open again.',
      eventType: 'left'
    });
    io.to(room.id).emit('room_update', { players: publicPlayers(room), maxPlayers: room.maxPlayers, hostUsername: room.hostUsername, started: room.started });
    return;
  }

  // Random Online Match
  rooms.delete(room.id);
  const remaining = room.players[0];
  if (remaining) {
    const other = io.sockets.sockets.get(remaining.id);
    if (other) {
      other.leave(room.id);
      other.data.roomId = null;
      other.data.matchMode = null;
      other.emit('opponent_left', { reason: reason || 'Opponent left the match.', eventType: 'left' });
    }
  }
}

function removeFromQueue(socket) {
  matchmakingQueue.delete(socket.id);
  socket.data.matchmaking = false;
}

function tryMatch() {
  const entries = [...matchmakingQueue.entries()];

  while (entries.length >= 2) {
    const [idA, dataA] = entries.shift();
    const [idB, dataB] = entries.shift();

    if (!matchmakingQueue.has(idA) || !matchmakingQueue.has(idB)) {
      continue;
    }

    matchmakingQueue.delete(idA);
    matchmakingQueue.delete(idB);

    const playerA = io.sockets.sockets.get(idA);
    const playerB = io.sockets.sockets.get(idB);

    if (!playerA || !playerB) continue;

    const roomId = `M-${Math.random().toString(36).slice(2, 8).toUpperCase()}`;

    const p1 = { ...dataA, index: 0, connected: true };
    const p2 = { ...dataB, index: 1, connected: true };

    const room = {
      id: roomId,
      mode: 'online',
      players: [p1, p2],
      board: emptyBoard(),
      turn: 0,
      deadline: 0,
      turnTimer: null,
      finished: false,
      rematchRequests: new Set(),
      reconnectTimers: new Map()
    };

    rooms.set(roomId, room);

    playerA.data.roomId = roomId;
    playerB.data.roomId = roomId;
    playerA.data.matchMode = 'online';
    playerB.data.matchMode = 'online';
    playerA.data.matchmaking = false;
    playerB.data.matchmaking = false;

    playerA.join(roomId);
    playerB.join(roomId);

    const players = publicPlayers(room);

    playerA.emit('match_found', {
      roomId,
      playerIndex: 0,
      players,
      state: roomState(room)
    });

    playerB.emit('match_found', {
      roomId,
      playerIndex: 1,
      players,
      state: roomState(room)
    });

    startTimer(room);
  }
}

/* =========================================================
   SOCKET.IO EVENT HANDLERS
========================================================= */

io.use((socket, next) => {
  const username = verifyToken(socket.handshake.auth?.token);
  if (!username || !readAccounts()[username]) return next(new Error('AUTH_REQUIRED'));
  socket.data.username = username;
  const account = readAccounts()[username];
  socket.data.displayName = account.displayName; socket.data.avatar = cleanAvatar(account.avatar);
  socket.data.level = account.level || 1; socket.data.rating = account.rating || 1000;
  next();
});

io.on('connection', socket => {
  console.log(`🔌 Connected: ${socket.id}`);
  socket.data.displayName = socket.data.displayName || '';
  socket.data.avatar = socket.data.avatar || '⚡';

  socket.on('register_profile', ({ username, displayName, avatar, level, rating } = {}) => {
    const authenticated = normalizeUsername(socket.data.username);
    if (!authenticated || authenticated !== normalizeUsername(username)) { socket.emit('server_error', 'Authenticated username mismatch.'); return; }
    const result = reserveUsername(socket, authenticated);
    if (!result.ok) { socket.emit('server_error', result.message); return; }
    socket.data.displayName = cleanName(displayName) || socket.data.displayName || authenticated;
    socket.data.avatar = cleanAvatar(avatar || socket.data.avatar);
    socket.data.level = Math.max(1, Number(level) || socket.data.level || 1);
    socket.data.rating = Math.max(0, Number(rating) || socket.data.rating || 1000);
    const accounts = readAccounts(); if (accounts[authenticated]) { accounts[authenticated].displayName = socket.data.displayName; accounts[authenticated].avatar = socket.data.avatar; accounts[authenticated].level = socket.data.level; accounts[authenticated].rating = socket.data.rating; writeAccounts(accounts); }
    ensureSocialUser(authenticated, { displayName: socket.data.displayName, avatar: socket.data.avatar, level: socket.data.level, rating: socket.data.rating });
    socket.emit('social_update', socialSnapshot(authenticated));
  });

  socket.on('check_username', ({ username } = {}) => {
    const normalized = normalizeUsername(username);
    const owner = activeUsernames.get(normalized);
    socket.emit('username_status', {
      available: validUsername(normalized) && (!owner || owner === socket.id),
      message: owner && owner !== socket.id ? 'That username is already being used.' : ''
    });
  });

  socket.on('reserve_username', ({ username } = {}) => {
    const result = reserveUsername(socket, username);
    socket.emit('username_reserved', result);
    if (result.ok) socket.emit('social_update', socialSnapshot(result.username));
  });

  socket.on('social_get', () => {
    if (!socket.data.username) { socket.emit('server_error', 'Reserve a username first.'); return; }
    socket.emit('social_update', socialSnapshot(socket.data.username));
  });

  socket.on('social_profile_update', ({ displayName, avatar, level, rating } = {}) => {
    if (!socket.data.username) return;
    socket.data.displayName = cleanName(displayName) || socket.data.displayName;
    socket.data.avatar = cleanAvatar(avatar || socket.data.avatar);
    socket.data.level = Math.max(1, Number(level) || socket.data.level || 1);
    socket.data.rating = Math.max(0, Number(rating) || socket.data.rating || 1000);
    ensureSocialUser(socket.data.username, { displayName: socket.data.displayName, avatar: socket.data.avatar, level: socket.data.level, rating: socket.data.rating });
    socket.emit('social_update', socialSnapshot(socket.data.username));
  });

  socket.on('friend_request_send', ({ username } = {}) => {
    const from = normalizeUsername(socket.data.username);
    const target = normalizeUsername(username);
    if (!from || !target || from === target || !validUsername(target)) { socket.emit('server_error', 'Enter a valid friend username.'); return; }
    if (!userDirectory.has(target)) { socket.emit('server_error', 'Player not found. They must have joined this development server at least once.'); return; }
    if (friendships.get(from)?.has(target)) { socket.emit('server_error', 'Already friends.'); return; }
    if (!friendRequests.has(target)) friendRequests.set(target, new Set());
    friendRequests.get(target).add(from);
    emitSocial(target);
    emitSocial(from);
    socket.emit('friend_request_sent', target);
  });

  socket.on('friend_request_respond', ({ username, accept } = {}) => {
    const me = normalizeUsername(socket.data.username);
    const other = normalizeUsername(username);
    const incoming = friendRequests.get(me);
    if (!incoming?.has(other)) { socket.emit('server_error', 'Friend request no longer exists.'); return; }
    incoming.delete(other);
    if (accept) {
      friendships.get(me)?.add(other);
      if (!friendships.has(other)) friendships.set(other, new Set());
      friendships.get(other).add(me);
    }
    emitSocial(me);
    emitSocial(other);
  });

  socket.on('friend_remove', ({ username } = {}) => {
    const me = normalizeUsername(socket.data.username);
    const other = normalizeUsername(username);
    friendships.get(me)?.delete(other);
    friendships.get(other)?.delete(me);
    emitSocial(me);
    emitSocial(other);
  });

  socket.on('friend_challenge', ({ username } = {}) => {
    const me = normalizeUsername(socket.data.username);
    const target = normalizeUsername(username);
    if (!friendships.get(me)?.has(target)) { socket.emit('server_error', 'You must be friends before challenging this player.'); return; }
    const targetId = activeUsernames.get(target);
    if (!targetId) { socket.emit('server_error', 'That friend is offline.'); return; }
    const targetSocket = io.sockets.sockets.get(targetId);
    if (!targetSocket) { socket.emit('server_error', 'That friend is offline.'); return; }
    const data = playerPayload(socket, { displayName: socket.data.displayName, username: me, avatar: socket.data.avatar });
    if (data.error) { socket.emit('server_error', data.error); return; }
    if (socket.data.roomId || targetSocket.data.roomId) { socket.emit('server_error', 'One player is already in a match.'); return; }
    const roomId = generateRoomCode();
    const player = data.player;
    player.index = 0;
    const room = { id: roomId, mode: 'friends', maxPlayers: 2, hostUsername: player.username, started: false, players: [player], board: emptyBoard(), turn: 0, deadline: 0, turnTimer: null, finished: false, rematchRequests: new Set(), reconnectTimers: new Map(), pausedForReconnect: false };
    rooms.set(roomId, room);
    socket.data.roomId = roomId; socket.data.matchMode = 'friends'; socket.join(roomId);
    targetSocket.emit('friend_challenge', { roomId, from: socialSnapshot(me).self });
    socket.emit('challenge_lobby_created', { roomId, players: publicPlayers(room), maxPlayers: room.maxPlayers, hostUsername: room.hostUsername });
  });

  /*
    RECONNECT MATCH HANDLER
  */
  socket.on('reconnect_match', ({ roomId, playerId } = {}) => {
    const room = rooms.get(String(roomId || ''));
    if (!room) {
      socket.emit('reconnect_failed', 'Match no longer exists.');
      return;
    }

    const player = room.players.find(p => p.playerId === playerId);
    if (!player) {
      socket.emit('reconnect_failed', 'Player not found in match.');
      return;
    }
    if (normalizeUsername(socket.data.username) !== normalizeUsername(player.username)) {
      socket.emit('reconnect_failed', 'This account cannot restore that match.');
      return;
    }

    // Cancel disconnect timer if active
    if (room.reconnectTimers && room.reconnectTimers.has(player.playerId)) {
      clearTimeout(room.reconnectTimers.get(player.playerId));
      room.reconnectTimers.delete(player.playerId);
    }
    player.reconnectDeadline = 0;

    // Re-bind socket ID and restore the player's session identity.
    player.id = socket.id;
    player.connected = true;
    room.pausedForReconnect = false;
    socket.data.username = player.username;
    socket.data.displayName = player.displayName;
    socket.data.avatar = player.avatar;
    socket.data.level = player.level || 1;
    socket.data.rating = player.rating || 1000;
    activeUsernames.set(player.username, socket.id);
    ensureSocialUser(player.username, { displayName: player.displayName, avatar: player.avatar, level: player.level, rating: player.rating });
    socket.data.roomId = room.id;
    socket.data.matchMode = room.mode;
    socket.join(room.id);

    socket.emit('reconnected_success', {
      roomId: room.id,
      playerIndex: player.index,
      players: publicPlayers(room),
      state: roomState(room),
      finished: room.finished,
      mode: room.mode
    });

    socket.to(room.id).emit('opponent_reconnected', {
      players: publicPlayers(room),
      playerId: player.playerId
    });
    if (!room.finished) startTimer(room);
  });

  /*
    CREATE PRIVATE ROOM
  */
  socket.on('create_room', payload => {
    if (socket.data.roomId) {
      socket.emit('server_error', 'You are already in a room.');
      return;
    }

    const result = createPrivateRoom(socket, payload);
    if (result.error) {
      socket.emit('server_error', result.error);
      return;
    }

    socket.emit('room_created', {
      roomId: result.room.id,
      playerIndex: result.player.index,
      players: publicPlayers(result.room),
      maxPlayers: result.room.maxPlayers,
      hostUsername: result.room.hostUsername,
      state: roomState(result.room)
    });
  });

  /*
    JOIN PRIVATE ROOM
  */
  socket.on('join_room', payload => {
    if (socket.data.roomId) {
      socket.emit('server_error', 'You are already in a room.');
      return;
    }
    const roomId = String(payload?.roomId || '').trim().toUpperCase();
    const room = rooms.get(roomId);
    if (!room || room.mode !== 'friends') { socket.emit('server_error', 'Room not found.'); return; }
    if (room.started) { socket.emit('server_error', 'This match has already started.'); return; }
    if (room.players.length >= (room.maxPlayers || 2)) { socket.emit('server_error', 'Room is already full.'); return; }
    const data = playerPayload(socket, payload);
    if (data.error) { socket.emit('server_error', data.error); return; }
    if (room.players.some(p => p.username === data.player.username)) { socket.emit('server_error', 'You are already in this room.'); return; }
    const player = data.player;
    player.index = room.players.length;
    room.players.push(player);
    socket.data.roomId = roomId;
    socket.data.matchMode = 'friends';
    socket.join(roomId);
    io.to(roomId).emit('room_update', { players: publicPlayers(room), maxPlayers: room.maxPlayers, hostUsername: room.hostUsername, started: room.started });
    socket.emit('room_joined', { roomId, playerIndex: player.index, players: publicPlayers(room), maxPlayers: room.maxPlayers, hostUsername: room.hostUsername });
    if (room.players.length >= room.maxPlayers) startPrivateRoom(room);
  });

  socket.on('start_private_room', ({ roomId } = {}) => {
    const room = rooms.get(String(roomId || '').trim().toUpperCase());
    if (!room || room.mode !== 'friends') { socket.emit('server_error', 'Room not found.'); return; }
    if (normalizeUsername(socket.data.username) !== room.hostUsername) { socket.emit('server_error', 'Only the room host can start the match.'); return; }
    if (room.players.length < 2) { socket.emit('server_error', 'Invite at least one friend before starting.'); return; }
    startPrivateRoom(room);
  });

  socket.on('invite_friend_to_room', ({ username, roomId } = {}) => {
    const me = normalizeUsername(socket.data.username);
    const target = normalizeUsername(username);
    const room = rooms.get(String(roomId || '').trim().toUpperCase());
    if (!room || room.mode !== 'friends' || room.started) { socket.emit('server_error', 'This room is no longer accepting invitations.'); return; }
    if (room.hostUsername !== me && !room.players.some(p => p.username === me)) { socket.emit('server_error', 'Join the room before inviting friends.'); return; }
    if (!friendships.get(me)?.has(target)) { socket.emit('server_error', 'You can invite players on your friends list only.'); return; }
    if (room.players.length >= room.maxPlayers) { socket.emit('server_error', 'This room is full.'); return; }
    const targetId = activeUsernames.get(target);
    const targetSocket = targetId && io.sockets.sockets.get(targetId);
    if (!targetSocket) { socket.emit('server_error', 'That friend is offline.'); return; }
    if (targetSocket.data.roomId) { socket.emit('server_error', 'That friend is already in a match or room.'); return; }
    targetSocket.emit('friend_challenge', { roomId: room.id, maxPlayers: room.maxPlayers, from: socialSnapshot(me).self });
    socket.emit('room_invite_sent', { username: target, roomId: room.id });
  });

  /*
    RANDOM MATCHMAKING
  */
  socket.on('find_match', payload => {
    if (!socket.data.username) { socket.emit('server_error', 'AUTH_REQUIRED'); return; }
    if (socket.data.roomId) {
      socket.emit('server_error', 'Leave your current match first.');
      return;
    }

    if (matchmakingQueue.has(socket.id)) return;

    const data = playerPayload(socket, payload);
    if (data.error) {
      socket.emit('server_error', data.error);
      return;
    }

    matchmakingQueue.set(socket.id, data.player);
    socket.data.matchmaking = true;

    socket.emit('matchmaking_status', {
      searching: true,
      playersSearching: matchmakingQueue.size
    });

    tryMatch();
  });

  socket.on('cancel_matchmaking', () => {
    removeFromQueue(socket);
    socket.emit('matchmaking_status', {
      searching: false,
      playersSearching: matchmakingQueue.size
    });
  });

  /*
    GAME MOVE
  */
  socket.on('make_move', ({ roomId, move } = {}) => {
    const room = rooms.get(String(roomId || ''));
    if (!room) {
      socket.emit('server_error', 'Match no longer exists.');
      return;
    }

    const player = room.players.find(p => p.id === socket.id);
    if (!player) {
      socket.emit('server_error', 'You are not in this match.');
      return;
    }

    const success = processMove(room, player.index, move);
    if (!success) {
      socket.emit('server_error', 'Invalid move.');
    }
  });

  /*
    REMATCH HANDLER
  */
  socket.on('request_rematch', ({ roomId } = {}) => {
    const room = rooms.get(String(roomId || ''));
    if (!room || room.players.length < 2) {
      socket.emit('server_error', 'Room is no longer active for rematch.');
      return;
    }

    if (!room.rematchRequests) room.rematchRequests = new Set();
    room.rematchRequests.add(socket.id);

    io.to(room.id).emit('rematch_requested', {
      requestedBy: socket.id,
      count: room.rematchRequests.size
    });

    if (room.rematchRequests.size >= 2) {
      // Both requested rematch! Reset board
      room.board = emptyBoard();
      room.turn = 0;
      room.finished = false;
      room.rematchRequests.clear();

      io.to(room.id).emit('match_rematch_started', {
        players: publicPlayers(room),
        state: roomState(room)
      });

      startTimer(room);
    }
  });

  /*
    REACTIONS
  */
  socket.on('send_reaction', ({ roomId, emoji } = {}) => {
    const room = rooms.get(String(roomId || ''));
    if (!room || !room.players.some(p => p.id === socket.id)) return;
    socket.to(room.id).emit('reaction_received', emoji);
  });

  /*
    LEAVE ROOM
  */
  socket.on('leave_room', ({ roomId } = {}) => {
    removePlayer(socket.id, 'Opponent left the match.', false);
    socket.data.matchmaking = false;
    // Keep the authenticated identity reserved while the socket remains connected.
    // This lets a player leave a match and immediately queue for another one.
  });

  /*
    DISCONNECT
  */
  socket.on('disconnect', reason => {
    console.log(`❌ Disconnected: ${socket.id} (${reason})`);
    removeFromQueue(socket);
    removePlayer(socket.id, 'Opponent disconnected.', true);
    releaseUsername(socket);
  });
});

server.listen(PORT, () => {
  console.log(`⚡ Territory Lines server running on port ${PORT}`);
});
