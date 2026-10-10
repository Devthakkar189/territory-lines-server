const express = require('express');
const http = require('http');
const cors = require('cors');
const { Server } = require('socket.io');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = Number(process.env.PORT || 4000);
const ALLOWED_ORIGIN = process.env.CLIENT_ORIGIN || '*';

const app = express();
const server = http.createServer(app);

const io = new Server(server, {
  cors: {
    origin: ALLOWED_ORIGIN,
    methods: ['GET', 'POST']
  }
});

app.use(cors({ origin: ALLOWED_ORIGIN }));
app.use(express.json());

const GRID_SIZE = 4;
const TURN_TIME = 15000;
const RECONNECT_GRACE_MS = 60000;

const rooms = new Map();
const activeUsernames = new Map();
const matchmakingQueue = new Map();
const userDirectory = new Map();
// On hosted deployments, point DATA_DIR at a persistent mounted volume.
const DATA_DIR = process.env.DATA_DIR ? path.resolve(process.env.DATA_DIR) : path.join(__dirname, 'data');
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
function writeAccounts(accounts) {
  const tempFile = `${USERS_FILE}.${process.pid}.tmp`;
  fs.writeFileSync(tempFile, JSON.stringify(accounts, null, 2), { mode: 0o600 });
  fs.renameSync(tempFile, USERS_FILE);
}
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

// Google OAuth (server-side code flow). Keep client secrets only in Render environment variables.
const googleOAuthStates = new Map();
const GOOGLE_RETURN_URL = process.env.GOOGLE_APP_RETURN_URL || 'territorylines://auth';
function googleOAuthReady() {
  return !!(process.env.GOOGLE_CLIENT_ID && process.env.GOOGLE_CLIENT_SECRET && process.env.GOOGLE_REDIRECT_URI);
}
function publicProfile(account) {
  return {
    username: account.username,
    email: account.email || '',
    displayName: account.displayName || account.username,
    avatar: account.avatar || '⚡',
    level: Math.max(1, Number(account.level) || 1),
    rating: Math.max(0, Number(account.rating) || 1000),
    playerId: account.playerId || account.username
  };
}
function uniqueGoogleUsername(seed, accounts) {
  const base = String(seed || 'player').toLowerCase().replace(/[^a-z0-9_]/g, '_').replace(/_+/g, '_').replace(/^_|_$/g, '').slice(0, 10) || 'player';
  let candidate = base.length >= 3 ? base : `${base}player`;
  if (!accounts[candidate] && validUsername(candidate)) return candidate;
  for (let i = 0; i < 30; i++) {
    const suffix = crypto.randomBytes(2).toString('hex');
    candidate = `${base.slice(0, 11)}_${suffix}`.slice(0, 16);
    if (validUsername(candidate) && !accounts[candidate]) return candidate;
  }
  return `p_${crypto.randomBytes(6).toString('hex')}`.slice(0, 16);
}
app.get('/api/auth/google', (req, res) => {
  if (!googleOAuthReady()) return res.status(503).send('Google sign-in is not configured on the server yet.');
  // Expire old states and keep the map bounded.
  for (const [state, value] of googleOAuthStates) if (value.expiresAt < Date.now()) googleOAuthStates.delete(state);
  if (googleOAuthStates.size > 5000) googleOAuthStates.clear();
  const state = crypto.randomBytes(32).toString('base64url');
  googleOAuthStates.set(state, { expiresAt: Date.now() + 10 * 60_000 });
  const target = new URL('https://accounts.google.com/o/oauth2/v2/auth');
  target.search = new URLSearchParams({
    client_id: process.env.GOOGLE_CLIENT_ID,
    redirect_uri: process.env.GOOGLE_REDIRECT_URI,
    response_type: 'code',
    scope: 'openid email profile',
    state,
    prompt: 'select_account'
  }).toString();
  res.redirect(302, target.toString());
});
app.get('/api/auth/google/callback', async (req, res) => {
  const state = String(req.query.state || '');
  const savedState = googleOAuthStates.get(state);
  googleOAuthStates.delete(state);
  if (!savedState || savedState.expiresAt < Date.now()) return res.status(400).send('Google sign-in expired or failed state validation. Please return to Territory Lines and try again.');
  if (req.query.error) return res.status(400).send('Google sign-in was cancelled or denied. You can return to Territory Lines and try again.');
  const code = String(req.query.code || '');
  if (!code || !googleOAuthReady()) return res.status(400).send('Google sign-in callback is missing required configuration or authorization code.');
  try {
    const tokenResponse = await fetch('https://oauth2.googleapis.com/token', {
      method: 'POST',
      headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
      body: new URLSearchParams({
        code,
        client_id: process.env.GOOGLE_CLIENT_ID,
        client_secret: process.env.GOOGLE_CLIENT_SECRET,
        redirect_uri: process.env.GOOGLE_REDIRECT_URI,
        grant_type: 'authorization_code'
      })
    });
    const tokenData = await tokenResponse.json();
    if (!tokenResponse.ok || !tokenData.access_token) throw new Error('Google token exchange failed');
    const identityResponse = await fetch('https://openidconnect.googleapis.com/v1/userinfo', {
      headers: { Authorization: `Bearer ${tokenData.access_token}` }
    });
    const identity = await identityResponse.json();
    if (!identityResponse.ok || !identity.sub || !identity.email || identity.email_verified !== true) throw new Error('Google identity could not be verified');

    const accounts = readAccounts();
    let account = Object.values(accounts).find(item => item.googleSub === identity.sub);
    if (!account) {
      // Link to an existing account only when Google confirms the same email address.
      account = Object.values(accounts).find(item => normalizeEmail(item.email) === normalizeEmail(identity.email));
      if (account && account.googleSub && account.googleSub !== identity.sub) return res.status(409).send('This game account is already linked to a different Google account. Sign in with your original method.');
      if (!account) {
        const username = uniqueGoogleUsername(String(identity.email).split('@')[0], accounts);
        account = {
          username,
          email: normalizeEmail(identity.email),
          displayName: cleanName(identity.name) || username,
          avatar: '⚡',
          passwordHash: null,
          level: 1,
          rating: 1000,
          playerId: crypto.randomUUID(),
          createdAt: new Date().toISOString()
        };
        accounts[username] = account;
      }
      account.googleSub = identity.sub;
      if (!account.playerId) account.playerId = crypto.randomUUID();
      if (!account.displayName) account.displayName = cleanName(identity.name) || account.username;
      writeAccounts(accounts);
    }
    ensureSocialUser(account.username, account);
    const token = makeToken(account.username);
    const profile = publicProfile(account);
    // Only permit the fixed app scheme; never accept a redirect target from request parameters.
    const appReturn = new URL(GOOGLE_RETURN_URL);
    if (appReturn.protocol !== 'territorylines:' || appReturn.hostname !== 'auth' || appReturn.search || appReturn.hash) throw new Error('GOOGLE_APP_RETURN_URL must be territorylines://auth');
    const fragment = new URLSearchParams({ territory_token: token, territory_profile: JSON.stringify(profile) }).toString();
    res.redirect(302, `${appReturn.toString()}#${fragment}`);
  } catch (err) {
    console.error('Google OAuth failed:', err.message);
    res.status(502).send('Google sign-in could not be completed. Return to Territory Lines and try again.');
  }
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


// Password recovery uses short-lived email OTPs. Configure SMTP_* environment variables on Render.
const resetCodes = new Map();
const verifiedResetTickets = new Map();
let mailer = null;
try { mailer = require('nodemailer'); } catch {}
function smtpReady() { return !!(mailer && process.env.SMTP_HOST && process.env.SMTP_PORT && process.env.SMTP_USER && process.env.SMTP_PASS && process.env.SMTP_FROM); }
app.post('/api/auth/forgot-password', async (req, res) => {
  const email = normalizeEmail(req.body?.email);
  if (!validEmail(email)) return res.status(400).json({ message: 'Enter a valid email address.' });
  if (!smtpReady()) return res.status(503).json({ message: 'Email recovery is not configured yet. Add SMTP settings to the Render server first.' });
  const accounts = readAccounts();
  const account = Object.values(accounts).find(item => normalizeEmail(item.email) === email);
  // Do not reveal whether an account exists.
  if (!account) return res.json({ message: 'If an account matches that email, a recovery code has been sent.' });
  const now = Date.now();
  const prior = resetCodes.get(email);
  if (prior && now - prior.createdAt < 60_000) return res.status(429).json({ message: 'Please wait a minute before requesting another code.' });
  const code = String(crypto.randomInt(0, 1000000)).padStart(6, '0');
  resetCodes.set(email, { hash: crypto.createHash('sha256').update(code).digest('hex'), createdAt: now, expiresAt: now + 10 * 60_000, attempts: 0, username: account.username });
  try {
    const transporter = mailer.createTransport({ host: process.env.SMTP_HOST, port: Number(process.env.SMTP_PORT), secure: String(process.env.SMTP_SECURE || 'false') === 'true', auth: { user: process.env.SMTP_USER, pass: process.env.SMTP_PASS } });
    await transporter.sendMail({ from: process.env.SMTP_FROM, to: email, subject: 'Territory Lines password reset code', text: `Your Territory Lines password reset code is ${code}. It expires in 10 minutes. If you did not request this, ignore this email.`, html: `<p>Your Territory Lines password reset code is:</p><p style="font-size:28px;font-weight:bold;letter-spacing:6px">${code}</p><p>This code expires in 10 minutes. If you did not request this, ignore this email.</p>` });
    return res.json({ message: 'If an account matches that email, a recovery code has been sent.' });
  } catch (err) { resetCodes.delete(email); console.error('Password reset email failed:', err.message); return res.status(502).json({ message: 'Could not send the email right now. Check the server email settings and try again.' }); }
});
app.post('/api/auth/verify-reset-code', (req, res) => {
  const email = normalizeEmail(req.body?.email), code = String(req.body?.code || '').trim();
  if (!validEmail(email) || !/^\d{6}$/.test(code)) return res.status(400).json({ message: 'Enter your email and the 6-digit code.' });
  const entry = resetCodes.get(email);
  if (!entry || Date.now() > entry.expiresAt) { resetCodes.delete(email); return res.status(400).json({ message: 'That code has expired. Request a new one.' }); }
  entry.attempts += 1;
  if (entry.attempts > 5) { resetCodes.delete(email); return res.status(429).json({ message: 'Too many attempts. Request a new code.' }); }
  const supplied = crypto.createHash('sha256').update(code).digest('hex');
  if (supplied !== entry.hash) return res.status(400).json({ message: 'That code is incorrect.' });
  const accounts = readAccounts(); const account = accounts[entry.username];
  if (!account || normalizeEmail(account.email) !== email) { resetCodes.delete(email); return res.status(400).json({ message: 'Account could not be verified. Request a new code.' }); }
  const resetTicket = crypto.randomBytes(32).toString('hex');
  verifiedResetTickets.set(resetTicket, { email, username: entry.username, expiresAt: Math.min(entry.expiresAt, Date.now() + 5 * 60_000) });
  resetCodes.delete(email);
  return res.json({ message: 'Email code verified. You can now choose a new password.', resetTicket });
});

app.post('/api/auth/reset-password', (req, res) => {
  const email = normalizeEmail(req.body?.email), resetTicket = String(req.body?.resetTicket || ''), newPassword = String(req.body?.newPassword || '');
  if (!validEmail(email) || !resetTicket) return res.status(400).json({ message: 'Verify your email code first.' });
  if (newPassword.length < 8) return res.status(400).json({ message: 'New password must be at least 8 characters.' });
  const ticket = verifiedResetTickets.get(resetTicket);
  if (!ticket || ticket.email !== email || Date.now() > ticket.expiresAt) { verifiedResetTickets.delete(resetTicket); return res.status(400).json({ message: 'Verification expired. Request and verify a new code.' }); }
  const accounts = readAccounts(); const account = accounts[ticket.username];
  if (!account || normalizeEmail(account.email) !== email) { verifiedResetTickets.delete(resetTicket); return res.status(400).json({ message: 'Account could not be verified. Request a new code.' }); }
  account.passwordHash = hashPassword(newPassword); writeAccounts(accounts); verifiedResetTickets.delete(resetTicket);
  return res.json({ message: 'Password updated. You can now sign in.' });
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
  boxes.forEach(row => {
    row.forEach(value => {
      if (value >= 1 && value <= 4) result[`p${value}`]++;
    });
  });
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
  const room = {
    id,
    mode: 'friends',
    maxPlayers: [2, 3, 4].includes(Number(payload?.maxPlayers)) ? Number(payload.maxPlayers) : 2,
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
  if (isDisconnect && (room.mode === 'online' || room.mode === 'friends') && !room.finished && room.players.length >= 2) {
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
    room.rematchRequests.clear();

    if (!room.players.length) {
      rooms.delete(room.id);
      return;
    }

    room.players[0].index = 0;
    const remaining = io.sockets.sockets.get(room.players[0].id);
    if (remaining) {
      remaining.emit('opponent_left', {
        roomId: room.id,
        players: publicPlayers(room),
        reason: reason || 'Opponent left. Room remains open.',
        eventType: 'left'
      });
      remaining.emit('room_update', { players: publicPlayers(room) });
    }
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
    const room = { id: roomId, mode: 'friends', players: [player], board: emptyBoard(), turn: 0, deadline: 0, turnTimer: null, finished: false, rematchRequests: new Set(), reconnectTimers: new Map(), pausedForReconnect: false };
    rooms.set(roomId, room);
    socket.data.roomId = roomId; socket.data.matchMode = 'friends'; socket.join(roomId);
    targetSocket.emit('friend_challenge', { roomId, from: socialSnapshot(me).self });
    socket.emit('challenge_lobby_created', { roomId, players: publicPlayers(room) });
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
      state: roomState(result.room),
      maxPlayers: result.room.maxPlayers,
      started: result.room.started
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

    const roomId = String(payload?.roomId || '').trim();
    const room = rooms.get(roomId);

    if (!room || room.mode !== 'friends') {
      socket.emit('server_error', 'Room not found.');
      return;
    }

    if (room.started) {
      socket.emit('server_error', 'This match has already started.');
      return;
    }

    if (room.players.length >= room.maxPlayers) {
      socket.emit('server_error', 'Room is already full.');
      return;
    }

    const data = playerPayload(socket, payload);
    if (data.error) {
      socket.emit('server_error', data.error);
      return;
    }

    const player = data.player;
    player.index = room.players.length;
    room.players.push(player);

    socket.data.roomId = roomId;
    socket.data.matchMode = 'friends';
    socket.join(roomId);

    io.to(roomId).emit('room_update', { players: publicPlayers(room), maxPlayers: room.maxPlayers, started: room.started });

    socket.emit('room_joined', {
      roomId,
      playerIndex: player.index,
      players: publicPlayers(room),
      maxPlayers: room.maxPlayers
    });
  });

  socket.on('start_private_room', ({ roomId } = {}) => {
    const room = rooms.get(String(roomId || ''));
    if (!room || room.mode !== 'friends') { socket.emit('server_error', 'Room not found.'); return; }
    if (room.players[0]?.id !== socket.id) { socket.emit('server_error', 'Only the host can start this match.'); return; }
    if (room.started) { socket.emit('server_error', 'The match has already started.'); return; }
    if (room.players.length !== room.maxPlayers) { socket.emit('server_error', `Invite ${room.maxPlayers - room.players.length} more player(s) before starting.`); return; }
    room.started = true;
    room.board = emptyBoard(); room.turn = 0; room.finished = false;
    io.to(room.id).emit('game_start', { roomId: room.id, players: publicPlayers(room), state: roomState(room) });
    startTimer(room);
  });

  socket.on('invite_friend_to_room', ({ roomId, username } = {}) => {
    const room = rooms.get(String(roomId || ''));
    const me = normalizeUsername(socket.data.username);
    const target = normalizeUsername(username);
    if (!room || room.mode !== 'friends' || room.players[0]?.id !== socket.id || room.started) { socket.emit('server_error', 'Only the host can invite friends to an open room.'); return; }
    if (!target || !friendships.get(me)?.has(target)) { socket.emit('server_error', 'You can invite only an in-game friend.'); return; }
    if (room.players.some(p => p.username === target)) { socket.emit('server_error', 'That friend is already in the room.'); return; }
    if (room.players.length >= room.maxPlayers) { socket.emit('server_error', 'Room is already full.'); return; }
    const targetId = activeUsernames.get(target);
    const targetSocket = targetId && io.sockets.sockets.get(targetId);
    if (!targetSocket) { socket.emit('server_error', 'That friend is offline.'); return; }
    targetSocket.emit('room_invite', { roomId: room.id, from: socialSnapshot(me).self, maxPlayers: room.maxPlayers });
    socket.emit('room_invite_sent', { username: target });
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

    if (room.rematchRequests.size >= room.players.length) {
      // Both requested rematch! Reset board
      room.board = emptyBoard();
      room.turn = 0;
      room.finished = false;
      room.started = true;
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
