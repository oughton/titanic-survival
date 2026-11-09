'use strict';
// =====================================================================
//  TITANIC: LAST LIFEBOAT — single player survival game
//  Phase 1: on the sinking ship (find & board a lifeboat)
//  Phase 2: in the lifeboat (dodge icebergs & sharks until the Carpathia)
// =====================================================================
const HAS_DOM = typeof document !== 'undefined';

// ---------------- Config ----------------
const SHIP_L = 2600, HALF = 120, PR = 6, CELL = 10;
const T_SINK = 180, T_RESCUE = 300, N_BOTS = 59;
const HOUSES = [[180, 440], [520, 900], [980, 1360], [1440, 1800], [1880, 2180]]
  .map(([a, b]) => ({ x: a, y: -62, w: b - a, h: 124 }));
const FUNNELS = [700, 1150, 1620, 2030];
const COLLAPSING = [1620, 1150];
const BOAT_XS = [300, 560, 820, 1520, 1760, 2000];
const OCEAN_HALF = 300;

const FIRST = ['Arthur', 'Edith', 'Walter', 'Mabel', 'Harold', 'Florence', 'Ernest', 'Ada', 'Albert', 'Clara', 'Frederick', 'Ivy', 'George', 'Lillian', 'Henry', 'Maud', 'Percy', 'Elsie', 'Stanley', 'Violet', 'Thomas', 'Agnes', 'William', 'Rose', 'Charles', 'Nora', 'Herbert', 'Dora', 'Leonard', 'Gladys', 'Samuel', 'Hilda', 'Oscar', 'Beatrice', 'Victor', 'Annie', 'Edgar', 'Winifred', 'Cyril', 'Ethel'];
const LAST = ['Ashby', 'Bramwell', 'Carver', 'Dunmore', 'Ellery', 'Fenwick', 'Garland', 'Hollis', 'Ingram', 'Jessop', 'Kendrick', 'Lowell', 'Marsh', 'Norwood', 'Oakes', 'Pembury', 'Quill', 'Radley', 'Selwyn', 'Thorne', 'Upton', 'Vance', 'Whitlock', 'Yardley', 'Ainsworth', 'Blythe', 'Corby', 'Dalton', 'Everly', 'Frome'];
const COATS = ['#2b3a55', '#5a3825', '#6d2632', '#4a4f57', '#2f5133', '#4b3566', '#7a6a4f', '#1f2b2f', '#80493a', '#3e5c76'];
const SKIN = ['#f1c9a5', '#e0ac85', '#c68863', '#8d5a3b', '#f5d5bc'];

// ---------------- Utils ----------------
const rand = (a, b) => a + Math.random() * (b - a);
const randi = (a, b) => Math.floor(rand(a, b + 1));
const pick = a => a[Math.floor(Math.random() * a.length)];
const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
const dist = (ax, ay, bx, by) => Math.hypot(ax - bx, ay - by);
const norm = (x, y, m = 1) => { const d = Math.hypot(x, y); return d < 1e-6 ? [0, 0] : [x / d * m, y / d * m]; };
const angDiff = (a, b) => { let d = a - b; while (d > Math.PI) d -= 2 * Math.PI; while (d < -Math.PI) d += 2 * Math.PI; return d; };
const hash = n => { const s = Math.sin(n * 12.9898 + 78.233) * 43758.5453; return s - Math.floor(s); };
const fmt = s => { s = Math.max(0, s); const m = Math.floor(s / 60), r = Math.floor(s % 60); return m + ':' + String(r).padStart(2, '0'); };
const clock = t => { const mins = 23 * 60 + 40 + t * 0.9; const h = Math.floor(mins / 60) % 24, m = Math.floor(mins % 60); return String(h).padStart(2, '0') + ':' + String(m).padStart(2, '0'); };

// ---------------- Ship geometry ----------------
function hw(x) {
  if (x < 0 || x > SHIP_L) return 0;
  if (x < 90) { const t = (90 - x) / 90; return HALF * Math.sqrt(Math.max(0, 1 - t * t)); }
  if (x > 2250) { const t = (x - 2250) / 350; return HALF * (1 - Math.pow(t, 1.6)); }
  return HALF;
}
function sinkFrac(t) { return Math.min(1, 0.03 + 0.97 * Math.pow(Math.max(0, t) / T_SINK, 1.5)); }
function waterlineAt(t) { return SHIP_L + 30 - sinkFrac(t) * (SHIP_L + 90); }
function floodTime(x) {
  const f = (SHIP_L + 30 - x) / (SHIP_L + 90);
  if (f <= 0.03) return 0;
  return T_SINK * Math.pow((f - 0.03) / 0.97, 1 / 1.5);
}
function inRect(x, y, r, R) { return x > R.x - r && x < R.x + R.w + r && y > R.y - r && y < R.y + R.h + r; }
function walkable(x, y, r = PR) {
  if (x < r || x > SHIP_L - r) return false;
  if (Math.abs(y) > hw(x) - r) return false;
  for (const h of HOUSES) if (inRect(x, y, r, h)) return false;
  if (G) for (const f of G.fallen) if (inRect(x, y, r, f)) return false;
  return true;
}

// ---------------- Navigation (flow fields) ----------------
const GW = Math.ceil((SHIP_L + 20) / CELL), GH = Math.ceil((2 * HALF + 20) / CELL);
function cellOf(x, y) {
  const cx = Math.floor(x / CELL), cy = Math.floor((y + HALF + 10) / CELL);
  if (cx < 0 || cy < 0 || cx >= GW || cy >= GH) return -1;
  return cy * GW + cx;
}
function cellCenter(i) { return [((i % GW) + 0.5) * CELL, (Math.floor(i / GW) + 0.5) * CELL - HALF - 10]; }
function buildWalk() {
  const w = new Uint8Array(GW * GH);
  for (let i = 0; i < w.length; i++) { const [x, y] = cellCenter(i); w[i] = walkable(x, y) ? 1 : 0; }
  return w;
}
function bfs(walk, srcs) {
  const d = new Float32Array(GW * GH).fill(1e9), q = new Int32Array(GW * GH);
  let h = 0, tl = 0;
  for (const s of srcs) if (s >= 0 && d[s] > 0) { d[s] = 0; q[tl++] = s; }
  while (h < tl) {
    const c = q[h++], cx = c % GW, cy = (c / GW) | 0, nd = d[c] + 1;
    if (cx > 0 && walk[c - 1] && d[c - 1] > nd) { d[c - 1] = nd; q[tl++] = c - 1; }
    if (cx < GW - 1 && walk[c + 1] && d[c + 1] > nd) { d[c + 1] = nd; q[tl++] = c + 1; }
    if (cy > 0 && walk[c - GW] && d[c - GW] > nd) { d[c - GW] = nd; q[tl++] = c - GW; }
    if (cy < GH - 1 && walk[c + GW] && d[c + GW] > nd) { d[c + GW] = nd; q[tl++] = c + GW; }
  }
  return d;
}
function computeFields() {
  const walk = buildWalk();
  G.fields = G.boats.map(b => bfs(walk, [cellOf(b.gx, b.gy)]));
  const st = [];
  for (let i = 0; i < walk.length; i++) if (walk[i] && cellCenter(i)[0] < 150) st.push(i);
  G.sternField = bfs(walk, st);
}
function navDir(p, field, tx, ty) {
  const ci = cellOf(p.x, p.y);
  if (ci < 0) return norm(tx - p.x, ty - p.y);
  if (field[ci] <= 1.5) return norm(tx - p.x, ty - p.y);
  let best = field[ci], bi = -1;
  const cx = ci % GW, cy = (ci / GW) | 0;
  for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
    if (!dx && !dy) continue;
    const nx = cx + dx, ny = cy + dy;
    if (nx < 0 || ny < 0 || nx >= GW || ny >= GH) continue;
    const n = ny * GW + nx;
    const v = field[n] + (dx && dy ? 0.4 : 0);
    if (v < best) { best = v; bi = n; }
  }
  if (bi < 0) return norm(tx - p.x, ty - p.y);
  const [nx, ny] = cellCenter(bi);
  return norm(nx - p.x, ny - p.y);
}

// ---------------- Game state ----------------
let G = null;
const input = { dx: 0, dy: 0, action: false, sprint: false };

function makePerson(isPlayer, i) {
  let x, y;
  do {
    x = isPlayer ? rand(700, 1900) : rand(110, 2220);
    y = rand(-112, 112);
  } while (!walkable(x, y));
  return {
    name: isPlayer ? 'You' : pick(FIRST) + ' ' + pick(LAST), isPlayer, id: i,
    x, y, vx: 0, vy: 0, kx: 0, ky: 0, ang: rand(0, 6.28),
    speed: isPlayer ? 78 : rand(50, 72), state: 'ship', cold: 0, stun: 0,
    deathT: -1, cause: '', boat: -1, target: -1, think: rand(0, 1),
    aware: isPlayer ? 0 : rand(0, 20), boardTime: rand(1.8, 3.0), panic: Math.random(),
    color: isPlayer ? '#ffd23f' : pick(COATS), skin: pick(SKIN), stamina: 1,
    wanderA: rand(0, 6.28), inWater: false,
  };
}

function newGame(opts = {}) {
  G = {
    opts, t: 0, sf: 0, waterline: SHIP_L + 30, phase: 'ship', people: [], boats: [], debris: [],
    funnelEvents: [], fallen: [], msgs: [], flags: {}, shake: 0, flash: 0, nextRocket: 0,
    ocean: null, player: null, done: false, ff: false, debrisAcc: 0, tc: [], launchTimer: 0,
  };
  for (const side of [-1, 1]) for (const x of BOAT_XS) {
    const ft = floodTime(x + 70);
    const openT = rand(6, Math.min(115, ft - 30));
    const closeT = Math.min(openT + rand(11, 20), ft - 3);
    G.boats.push({
      id: 0, x, side, cap: randi(2, 4), seats: [], state: 'covered', openT, closeT, launchT: 0,
      gx: x, gy: side * (HALF - 14), boarder: null, progress: 0, hasPlayer: false,
    });
  }
  // number boats like the real ship: odd starboard, even port, from bow to stern
  const order = [...G.boats].sort((a, b) => b.x - a.x);
  let so = 1, po = 2;
  for (const b of order) { if (b.side > 0) { b.id = so; so += 2; } else { b.id = po; po += 2; } }
  G.player = makePerson(true, 0);
  G.people.push(G.player);
  for (let i = 1; i <= N_BOTS; i++) G.people.push(makePerson(false, i));
  computeFields();
  if (!opts.headless) {
    msg('23:40 — Titanic has struck an iceberg and is sinking by the bow!', '#ffd23f');
    msg('Reach a lifeboat that is LOADING and hold SPACE at its gangway to board.', '#cfe3ff');
  }
  return G;
}

function msg(text, color = '#e8eef5') {
  if (G.ff || G.opts.headless) return;
  G.msgs.push({ text, color, t: G.t });
  if (G.msgs.length > 6) G.msgs.shift();
}

function kill(p, cause) {
  if (p.state === 'dead' || p.state === 'rescued') return;
  p.state = 'dead'; p.deathT = G.t; p.cause = cause;
  if (p.isPlayer && !G.opts.playerBot) {
    G.phase = 'dead';
    G.deathCam = { x: p.x, y: p.y };
    if (typeof onPlayerDeath === 'function') onPlayerDeath();
  }
}

// ---------------- Main simulation step ----------------
function step(dt) {
  G.t += dt;
  G.sf = sinkFrac(G.t);
  G.waterline = waterlineAt(G.t);
  shipEvents(dt);
  updateBoats(dt);
  G.tc = G.boats.map(() => 0);
  for (const p of G.people) if (p.state === 'ship' && p.target >= 0) G.tc[p.target]++;
  for (const p of G.people) if (p.state === 'ship') updatePerson(p, dt);
  separate();
  updateDebris(dt);
  updateFunnels(dt);
  updateSeaBoats(dt);
  if (G.phase === 'launching') { G.launchTimer -= dt; if (G.launchTimer <= 0) startOcean(); }
  if (G.phase === 'ocean') updateOcean(dt);
  G.shake = Math.max(0, G.shake - dt * 1.5);
  G.flash = Math.max(0, G.flash - dt * 1.2);
  if (G.t >= T_RESCUE && !G.done) finish();
}

function shipEvents() {
  const f = G.flags, sf = G.sf;
  const once = (k, cond, fn) => { if (!f[k] && cond) { f[k] = 1; fn(); } };
  once('bow', sf > 0.22, () => msg('The bow slips beneath the waves. The deck is tilting!', '#9fd0ff'));
  once('rockets', sf > 0.42, () => { msg('Distress rockets light up the sky.', '#ffb3b3'); G.nextRocket = G.t; });
  if (sf > 0.42 && sf < 0.85 && G.t >= G.nextRocket) { G.flash = 1; G.nextRocket = G.t + rand(7, 11); }
  once('band', sf > 0.66, () => msg('The band plays on…', '#e8d9a8'));
  once('lights', sf > 0.82, () => { msg('The lights flicker and die!', '#ff8f6b'); G.shake = 0.6; });
  once('split', sf > 0.88, () => { msg('With a terrible roar, the ship breaks in two!', '#ff6b6b'); G.shake = 1.4; sound('crash'); });
  once('sunk', sf >= 1, () => msg('02:20 — Titanic has sunk. The sea is freezing.', '#9fd0ff'));
}

function updateBoats(dt) {
  G.boats.forEach((b, i) => {
    if (b.state === 'covered' && G.t >= b.openT) {
      b.state = 'loading';
      msg(`Boat ${b.id} (${b.side < 0 ? 'port' : 'starboard'}) is now loading — ${b.cap} seats!`, '#3ddc84');
    }
    if (b.state === 'loading') {
      let c = null, cd = 26;
      for (const p of G.people) {
        if (p.state !== 'ship' || p.stun > 0) continue;
        const d = dist(p.x, p.y, b.gx, b.gy);
        if (d < cd) { cd = d; c = p; }
      }
      if (c !== b.boarder) { b.boarder = c; b.progress = 0; }
      if (c) {
        const human = c.isPlayer && !G.opts.playerBot;
        const rate = human ? (input.action ? 1 / 1.2 : 0) : 1 / c.boardTime;
        b.progress += rate * dt;
        if (b.progress >= 1) { board(c, b, i); b.boarder = null; b.progress = 0; }
      }
      if (G.t >= b.closeT || G.waterline < b.x + 70) launch(b);
    } else if (b.state === 'covered' && G.waterline < b.x + 70) launch(b);
  });
}

function board(p, b, i) {
  p.state = 'boat'; p.boat = i; p.target = -1;
  b.seats.push(p);
  if (b.seats.length >= b.cap) b.closeT = Math.min(b.closeT, G.t + 1.5);
  if (p.isPlayer && !G.opts.playerBot) {
    b.hasPlayer = true;
    msg(`You're aboard Boat ${b.id}! Waiting to be lowered…`, '#3ddc84');
    sound('chime');
  }
}

function launch(b) {
  b.state = 'launched'; b.launchT = G.t;
  for (const p of b.seats) p.state = 'sea';
  if (b.hasPlayer) {
    G.phase = 'launching'; G.launchTimer = 3;
    msg(`Lower away! Boat ${b.id} is going down to the sea.`, '#3ddc84');
  } else if (b.seats.length < b.cap) {
    msg(`Boat ${b.id} lowered with only ${b.seats.length} of ${b.cap} seats filled.`, '#9fb3c8');
  } else msg(`Boat ${b.id} lowered — full.`, '#9fb3c8');
}

function updateSeaBoats(dt) {
  for (const b of G.boats) {
    if (b.state !== 'launched' || b.hasPlayer) continue;
    const tau = G.t - b.launchT;
    const p = 0.0015 + tau * 0.00002;
    if (Math.random() < p * dt) {
      b.state = 'lost';
      const cause = Math.random() < 0.6 ? 'Lifeboat holed by an iceberg' : 'Lifeboat capsized by a shark';
      for (const q of b.seats) kill(q, cause);
      if (b.seats.length) msg(`Lifeboat ${b.id} was lost at sea (${cause.toLowerCase().replace('lifeboat ', '')}).`, '#ff8f8f');
    }
  }
}

// ---------------- People ----------------
function tryMove(p, dx, dy) {
  if (walkable(p.x + dx, p.y + dy)) { p.x += dx; p.y += dy; return true; }
  if (walkable(p.x + dx, p.y)) { p.x += dx; return false; }
  if (walkable(p.x, p.y + dy)) { p.y += dy; return false; }
  return false;
}

function updatePerson(p, dt) {
  p.inWater = p.x > G.waterline;
  if (p.inWater) p.cold += (G.sf >= 1 ? 16 : 12) * dt;
  else p.cold = Math.max(0, p.cold - 6 * dt);
  if (p.cold >= 100) return kill(p, 'Froze in the icy water');

  if (p.kx || p.ky) {
    tryMove(p, p.kx * dt, p.ky * dt);
    p.kx *= Math.pow(0.02, dt); p.ky *= Math.pow(0.02, dt);
    if (Math.abs(p.kx) + Math.abs(p.ky) < 2) p.kx = p.ky = 0;
  }
  if (p.stun > 0) { p.stun -= dt; p.vx = p.vy = 0; return; }

  let dir, spd = p.speed;
  if (p.isPlayer && !G.opts.playerBot) {
    dir = [input.dx, input.dy];
    p.sprinting = false;
    if (input.sprint && p.stamina > 0.02 && (dir[0] || dir[1])) {
      spd = 125; p.stamina -= dt * 0.3; p.sprinting = true;
    } else p.stamina = Math.min(1, p.stamina + dt * 0.15);
  } else dir = botControl(p, dt);
  if (p.inWater) spd *= 0.5;
  const k = Math.min(1, dt * 10);
  p.vx += (dir[0] * spd - p.vx) * k;
  p.vy += (dir[1] * spd - p.vy) * k;
  if (Math.abs(p.vx) + Math.abs(p.vy) > 5) p.ang = Math.atan2(p.vy, p.vx);
  if (!tryMove(p, p.vx * dt, p.vy * dt) && !p.isPlayer) p.wanderA += Math.PI * rand(0.5, 1.5);
}

function botControl(p, dt) {
  if (G.t < p.aware && !p.inWater) {
    p.wanderA += rand(-2, 2) * dt;
    return [Math.cos(p.wanderA) * 0.3, Math.sin(p.wanderA) * 0.3];
  }
  p.think -= dt;
  if (p.think <= 0) { p.think = rand(0.5, 1.2); chooseTarget(p); }
  if (p.target >= 0) {
    const b = G.boats[p.target];
    if (b.state !== 'loading' && b.state !== 'covered') { p.target = -1; p.think = 0; }
    else {
      const d = dist(p.x, p.y, b.gx, b.gy);
      if (d < 30) return norm(b.gx - p.x, b.gy - p.y, d < 4 ? 0.2 : 1);
      return navDir(p, G.fields[p.target], b.gx, b.gy);
    }
  }
  const ci = cellOf(p.x, p.y);
  if (ci >= 0 && G.sternField[ci] <= 3) {
    p.wanderA += rand(-2, 2) * dt;
    return [Math.cos(p.wanderA) * 0.2, Math.sin(p.wanderA) * 0.2];
  }
  return navDir(p, G.sternField, 40, p.y);
}

function chooseTarget(p) {
  const ci = cellOf(p.x, p.y);
  const spd = p.speed * (p.inWater ? 0.5 : 1);
  let best = -1, bs = 1e9;
  G.boats.forEach((b, i) => {
    if (b.state !== 'covered' && b.state !== 'loading') return;
    const free = b.cap - b.seats.length;
    if (free <= 0) return;
    let dd = ci >= 0 ? G.fields[i][ci] : 1e9;
    if (dd >= 1e9) dd = dist(p.x, p.y, b.gx, b.gy) / CELL * 1.5;
    const eta = dd * CELL / spd * 1.15;
    if (G.t + eta > b.closeT - 1) return;
    const others = G.tc[i] - (p.target === i ? 1 : 0);
    let s = eta + Math.max(0, others - free + 1) * 3 + Math.max(0, b.openT - G.t - eta) * 0.4 + p.panic * rand(0, 6);
    if (i === p.target) s *= 0.75;
    if (s < bs) { bs = s; best = i; }
  });
  p.target = best;
}

function separate() {
  const ps = G.people.filter(p => p.state === 'ship');
  const D = PR * 2;
  for (let i = 0; i < ps.length; i++) {
    const a = ps[i];
    for (let j = i + 1; j < ps.length; j++) {
      const b = ps[j];
      const dx = b.x - a.x, dy = b.y - a.y;
      if (Math.abs(dx) >= D || Math.abs(dy) >= D) continue;
      const d2 = dx * dx + dy * dy;
      if (d2 >= D * D) continue;
      const d = Math.sqrt(d2) || 0.01, ov = D - d;
      const nx = d2 ? dx / d : 1, ny = d2 ? dy / d : 0;
      const ma = mass(a), mb = mass(b), tot = ma + mb;
      tryMove(a, -nx * ov * mb / tot, -ny * ov * mb / tot);
      tryMove(b, nx * ov * ma / tot, ny * ov * ma / tot);
    }
  }
}
function mass(p) { return p.stun > 0 ? 0.5 : p.isPlayer ? (p.sprinting ? 3 : 1.6) : 1; }

// ---------------- Hazards on deck ----------------
const DEBRIS_KINDS = [
  { k: 'chair', w: 16, h: 9, stun: 1.0, wgt: 5 },
  { k: 'crate', w: 13, h: 13, stun: 1.2, wgt: 3 },
  { k: 'barrel', w: 11, h: 11, stun: 1.1, wgt: 3 },
  { k: 'piano', w: 28, h: 16, stun: 2.4, wgt: 1 },
];
function spawnDebris() {
  const tot = DEBRIS_KINDS.reduce((s, d) => s + d.wgt, 0);
  let r = Math.random() * tot, kind = DEBRIS_KINDS[0];
  for (const d of DEBRIS_KINDS) { r -= d.wgt; if (r <= 0) { kind = d; break; } }
  for (let tries = 0; tries < 6; tries++) {
    const x = rand(80, G.waterline - 220);
    const side = Math.random() < 0.5 ? -1 : 1;
    const y = side * rand(66 + kind.h / 2, 114 - kind.h / 2);
    if (Math.abs(y) + kind.h / 2 > hw(x) - 2) continue;
    if (G.fallen.some(f => inRect(x, y, kind.w / 2, f))) continue;
    G.debris.push({ ...kind, x, y, vx: 0, spin: 0 });
    return;
  }
}
function updateDebris(dt) {
  if (G.t > 20 && G.waterline > 320 && G.sf < 0.97) {
    G.debrisAcc += (0.35 + 2.4 * G.sf) * dt;
    while (G.debrisAcc >= 1) { G.debrisAcc--; spawnDebris(); }
  }
  for (const d of G.debris) {
    d.vx = Math.min(210, d.vx + (25 + 120 * G.sf) * dt * (d.k === 'piano' ? 0.8 : 1));
    d.x += d.vx * dt;
    if (d.k === 'barrel') d.spin += d.vx * dt * 0.2;
    if (d.x > G.waterline + 10 || Math.abs(d.y) + d.h / 2 > hw(d.x) || G.fallen.some(f => inRect(d.x, d.y, d.w / 2, f))) { d.dead = true; continue; }
    if (d.vx < 30) continue;
    for (const p of G.people) {
      if (p.state !== 'ship' || p.stun > 0) continue;
      if (Math.abs(p.x - d.x) < d.w / 2 + PR && Math.abs(p.y - d.y) < d.h / 2 + PR) {
        p.stun = d.stun; p.kx = d.vx * 0.9; p.ky = Math.sign(p.y - d.y || 1) * 60;
        d.vx *= 0.7;
        if (p.isPlayer && !G.opts.playerBot) { msg(`You were knocked down by a sliding ${d.k}!`, '#ffb36b'); G.shake = 0.5; sound('thud'); }
      }
    }
  }
  G.debris = G.debris.filter(d => !d.dead);
}

function updateFunnels(dt) {
  for (const fx of COLLAPSING) {
    if (!G.flags['f' + fx] && G.waterline < fx + 260) {
      G.flags['f' + fx] = 1;
      const side = Math.random() < 0.5 ? -1 : 1;
      const zone = { x: fx - 24, w: 48, y: side < 0 ? -HALF - 2 : 62, h: HALF - 60 };
      G.funnelEvents.push({ fx, side, timer: 2.8, zone });
      msg(`Funnel collapsing onto the ${side < 0 ? 'port' : 'starboard'} deck — get clear!`, '#ff6b6b');
      sound('creak');
    }
  }
  for (const e of G.funnelEvents) {
    e.timer -= dt;
    if (e.timer <= 0 && !e.done) {
      e.done = true;
      for (const p of G.people) if (p.state === 'ship' && inRect(p.x, p.y, PR, e.zone)) kill(p, 'Crushed by a falling funnel');
      G.fallen.push(e.zone);
      G.flags['fallen' + e.fx] = e.side;
      G.shake = 1.2;
      sound('crash');
      computeFields();
    }
  }
  G.funnelEvents = G.funnelEvents.filter(e => !e.done);
}

// ---------------- Ocean phase ----------------
function startOcean() {
  G.phase = 'ocean';
  const b = G.boats[G.player.boat];
  G.ocean = {
    b, x: 0, y: 0, vx: 0, speed: 55, stamina: 1, ice: [], sharks: [], iceAcc: 0, sharkAcc: 0,
    t0: G.t, carp: false, oar: 0, rowing: false, dead: false,
  };
  msg(`Boat ${b.id} is in the water. Survive until the Carpathia arrives!`, '#3ddc84');
  msg('ALL icebergs will sink you. Sharks with RED fins will too — grey ones are harmless.', '#ffd23f');
  for (let i = 0; i < 4; i++) spawnBerg(G.ocean, -rand(260, 680), 0);
}
function spawnBerg(o, yOff, diff) {
  const r = rand(14, 40) * (1 + 0.4 * diff);
  const n = 10, pts = [];
  for (let i = 0; i < n; i++) pts.push(rand(0.75, 1.12));
  o.ice.push({ x: rand(-OCEAN_HALF, OCEAN_HALF), y: o.y + yOff, r, pts, vx: rand(-8, 8), rot: rand(0, 6.28) });
}
function spawnShark(o, diff) {
  const killer = Math.random() < 0.3 + 0.35 * diff;
  let x, y, ang;
  if (Math.random() < 0.5) {
    const s = Math.random() < 0.5 ? -1 : 1;
    x = s * (OCEAN_HALF + 30); y = o.y - rand(100, 500);
    ang = s < 0 ? rand(-0.5, 0.5) : Math.PI + rand(-0.5, 0.5);
  } else {
    x = rand(-280, 280); y = o.y - rand(560, 680); ang = Math.PI / 2 + rand(-0.6, 0.6);
  }
  o.sharks.push({ x, y, ang, killer, chase: 0, tired: 0, cd: 0, wig: rand(0, 6) });
}
function updateOcean(dt) {
  const o = G.ocean;
  if (!o || o.dead) return;
  const ot = G.t - o.t0, left = T_RESCUE - G.t, diff = Math.min(1, ot / 140);
  o.vx += (input.dx * 130 - o.vx) * Math.min(1, dt * 3);
  o.x += o.vx * dt;
  const lim = OCEAN_HALF - 14;
  if (o.x < -lim) { o.x = -lim; o.vx = Math.max(0, o.vx); }
  if (o.x > lim) { o.x = lim; o.vx = Math.min(0, o.vx); }
  let tgt = 55; o.rowing = false;
  if ((input.dy < -0.4 || input.action) && o.stamina > 0.02) { tgt = 105; o.stamina -= dt * 0.3; o.rowing = true; }
  else { if (input.dy > 0.4) tgt = 22; o.stamina = Math.min(1, o.stamina + dt * 0.14); }
  o.speed += (tgt - o.speed) * Math.min(1, dt * 1.8);
  o.y -= o.speed * dt;
  o.oar += dt * (o.speed / 55) * 5;

  if (left > 15) {
    o.iceAcc += dt * (o.speed / 100) * (0.5 + 1.0 * diff);
    while (o.iceAcc >= 1) { o.iceAcc--; spawnBerg(o, -rand(560, 700), diff); }
    if (ot > 5) {
      o.sharkAcc += dt * (0.1 + 0.26 * diff);
      while (o.sharkAcc >= 1) { o.sharkAcc--; spawnShark(o, diff); }
    }
  }
  const c1y = o.y - 11, c2y = o.y + 11;
  for (const b of o.ice) {
    b.x += b.vx * dt;
    const rr = b.r * 0.82 + 9;
    if (dist(b.x, b.y, o.x, c1y) < rr || dist(b.x, b.y, o.x, c2y) < rr) return sinkPlayer('Lifeboat holed by an iceberg');
  }
  for (const s of o.sharks) {
    s.wig += dt * 6; s.cd = Math.max(0, s.cd - dt);
    const dx = o.x - s.x, dy = o.y - s.y, d = Math.hypot(dx, dy);
    let speed = 30, turn = 0.8, want = s.ang + Math.sin(s.wig * 0.15) * 0.5;
    if (s.killer) {
      if (d < 300 && s.tired <= 0) {
        s.chase += dt;
        want = Math.atan2(dy - o.speed * 0.3, dx);
        speed = 60 + 28 * diff; turn = 1.5 + diff * 0.6;
        if (s.chase > 7) { s.tired = 5; s.chase = 0; }
      } else { s.tired -= dt; speed = 40; }
    }
    s.ang += clamp(angDiff(want, s.ang), -turn * dt, turn * dt);
    s.x += Math.cos(s.ang) * speed * dt;
    s.y += Math.sin(s.ang) * speed * dt;
    const hx = s.x + Math.cos(s.ang) * 10, hy = s.y + Math.sin(s.ang) * 10;
    if (dist(hx, hy, o.x, c1y) < 15 || dist(hx, hy, o.x, c2y) < 15) {
      if (s.killer) return sinkPlayer('Lifeboat capsized by a shark');
      if (s.cd <= 0) {
        o.vx += (o.x > s.x ? 1 : -1) * 110; s.ang += Math.PI; s.cd = 1.5;
        msg('A harmless basking shark bumps the boat.', '#9fb3c8');
        sound('thud');
      }
    }
  }
  o.ice = o.ice.filter(b => b.y < o.y + 450);
  o.sharks = o.sharks.filter(s => s.y < o.y + 500 && s.y > o.y - 950 && Math.abs(s.x) < 460);
  if (left < 15 && !o.carp) { o.carp = true; msg('Lights on the horizon — the RMS CARPATHIA is coming!', '#ffd23f'); sound('horn'); }
}
function sinkPlayer(cause) {
  const o = G.ocean;
  o.dead = true;
  const b = o.b;
  b.state = 'lost';
  G.shake = 1.2;
  sound('crash');
  for (const p of b.seats) if (!p.isPlayer) kill(p, cause);
  kill(G.player, cause);
}

// ---------------- End of game ----------------
function finish() {
  G.done = true;
  for (const p of G.people) {
    if (p.state === 'sea') { p.state = 'rescued'; p.deathT = T_RESCUE; p.cause = 'Rescued by the Carpathia'; }
    else if (p.state === 'ship' || p.state === 'boat') kill(p, 'Went down with the ship');
  }
  if (!G.opts.headless && typeof showResults === 'function') showResults();
}
function fastForward() {
  G.ff = true;
  while (!G.done) step(1 / 20);
}
function survScore(p) { return p.state === 'rescued' ? 1e6 : p.deathT; }

if (typeof module !== 'undefined') module.exports = { newGame, step, fastForward, getG: () => G, T_RESCUE };

// =====================================================================
//  Everything below only runs in a browser
// =====================================================================
let canvas, ctx, W = 0, H = 0, DPR = 1, paused = false;
const keys = {};
const touch = { id: null, ox: 0, oy: 0, x: 0, y: 0, actionId: null, used: false };

// ---------------- Sound ----------------
let AC = null;
function initAudio() { if (!HAS_DOM || AC) return; try { AC = new (window.AudioContext || window.webkitAudioContext)(); } catch (e) { AC = null; } }
function noiseBuf(dur) {
  const b = AC.createBuffer(1, AC.sampleRate * dur, AC.sampleRate), d = b.getChannelData(0);
  for (let i = 0; i < d.length; i++) d[i] = Math.random() * 2 - 1;
  return b;
}
function sound(type) {
  if (!AC || !G || G.ff || G.opts.headless || muted) return;
  const t = AC.currentTime, out = AC.createGain();
  out.connect(AC.destination);
  const env = (g, a, peak, dec) => { g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(peak, t + a); g.gain.exponentialRampToValueAtTime(0.0001, t + a + dec); };
  if (type === 'horn') {
    const lp = AC.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 500; lp.connect(out);
    for (const f of [72, 108]) { const o = AC.createOscillator(); o.type = 'sawtooth'; o.frequency.value = f; o.connect(lp); o.start(t); o.stop(t + 2.6); }
    out.gain.setValueAtTime(0.0001, t); out.gain.exponentialRampToValueAtTime(0.18, t + 0.3); out.gain.setValueAtTime(0.18, t + 2); out.gain.exponentialRampToValueAtTime(0.0001, t + 2.6);
  } else if (type === 'chime') {
    const o = AC.createOscillator(); o.type = 'sine'; o.frequency.setValueAtTime(660, t); o.frequency.setValueAtTime(990, t + 0.12);
    o.connect(out); env(out, 0.01, 0.2, 0.4); o.start(t); o.stop(t + 0.5);
  } else if (type === 'crash' || type === 'thud' || type === 'creak') {
    const s = AC.createBufferSource(); s.buffer = noiseBuf(1.2);
    const lp = AC.createBiquadFilter(); lp.type = 'lowpass';
    lp.frequency.value = type === 'crash' ? 700 : type === 'thud' ? 300 : 1200;
    s.connect(lp); lp.connect(out);
    env(out, 0.01, type === 'thud' ? 0.25 : 0.35, type === 'thud' ? 0.25 : 1.0);
    s.start(t); s.stop(t + 1.2);
    if (type === 'creak') { const o = AC.createOscillator(); o.type = 'square'; o.frequency.setValueAtTime(90, t); o.frequency.linearRampToValueAtTime(45, t + 1); const g = AC.createGain(); env(g, 0.05, 0.05, 0.9); o.connect(g); g.connect(AC.destination); o.start(t); o.stop(t + 1.1); }
  }
}
let muted = false;

// ---------------- Input ----------------
function readInput() {
  let x = 0, y = 0;
  if (keys.KeyA || keys.ArrowLeft) x--;
  if (keys.KeyD || keys.ArrowRight) x++;
  if (keys.KeyW || keys.ArrowUp) y--;
  if (keys.KeyS || keys.ArrowDown) y++;
  let sprint = !!(keys.ShiftLeft || keys.ShiftRight);
  if (touch.id !== null) {
    const dx = touch.x - touch.ox, dy = touch.y - touch.oy, m = Math.hypot(dx, dy);
    if (m > 8) { x = dx / Math.max(m, 55); y = dy / Math.max(m, 55); if (m > 60) sprint = true; }
  }
  const m = Math.hypot(x, y);
  if (m > 1) { x /= m; y /= m; }
  input.dx = x; input.dy = y; input.sprint = sprint;
  input.action = !!(keys.Space || keys.KeyE || touch.actionId !== null);
}

// ---------------- Rendering helpers ----------------
function circle(x, y, r, fill) { ctx.beginPath(); ctx.arc(x, y, r, 0, Math.PI * 2); ctx.fillStyle = fill; ctx.fill(); }
function rr(x, y, w, h, r) { ctx.beginPath(); ctx.moveTo(x + r, y); ctx.arcTo(x + w, y, x + w, y + h, r); ctx.arcTo(x + w, y + h, x, y + h, r); ctx.arcTo(x, y + h, x, y, r); ctx.arcTo(x, y, x + w, y, r); ctx.closePath(); }
function shipScale() { return Math.min(H / 430, W / 360); }
function oceanScale() { return Math.min(H / 560, W / 640); }

function drawLifeboat(cx, cy, len, wid, ang, occ, cap, alpha = 1, oar = null) {
  ctx.save(); ctx.translate(cx, cy); ctx.rotate(ang); ctx.globalAlpha = alpha;
  if (oar !== null) {
    ctx.strokeStyle = '#c9a36b'; ctx.lineWidth = 1.6;
    for (const k of [-0.2, 0.15]) for (const s of [-1, 1]) {
      const a = Math.sin(oar + k * 3) * 0.5;
      ctx.beginPath(); ctx.moveTo(len * k, s * wid * 0.4);
      ctx.lineTo(len * k - Math.cos(a) * 4 + Math.sin(a) * 8, s * (wid * 0.4 + 16)); ctx.stroke();
    }
  }
  const hull = sc => {
    const l = len / 2 * sc, w = wid / 2 * sc;
    ctx.beginPath(); ctx.moveTo(-l, 0);
    ctx.quadraticCurveTo(-l + 3, -w, -l / 2, -w); ctx.lineTo(l / 2, -w);
    ctx.quadraticCurveTo(l - 3, -w, l, 0); ctx.quadraticCurveTo(l - 3, w, l / 2, w);
    ctx.lineTo(-l / 2, w); ctx.quadraticCurveTo(-l + 3, w, -l, 0); ctx.closePath();
  };
  hull(1); ctx.fillStyle = '#f2efe6'; ctx.fill(); ctx.strokeStyle = '#7d735f'; ctx.lineWidth = 1; ctx.stroke();
  hull(0.8); ctx.fillStyle = '#8b5e34'; ctx.fill();
  ctx.strokeStyle = '#6d4824'; ctx.lineWidth = 1.2;
  for (const k of [-0.25, 0, 0.25]) { ctx.beginPath(); ctx.moveTo(len * k, -wid * 0.38); ctx.lineTo(len * k, wid * 0.38); ctx.stroke(); }
  const cols = Math.max(1, Math.ceil(cap / 2));
  occ.forEach((p, i) => {
    const c = Math.floor(i / 2), x = cols > 1 ? -len * 0.28 + c * (len * 0.56 / (cols - 1)) : 0;
    const y = (i % 2 ? 1 : -1) * wid * 0.18;
    circle(x, y, 3.6, p.color);
    if (p.isPlayer) { ctx.strokeStyle = '#fff'; ctx.lineWidth = 1.2; ctx.stroke(); }
    circle(x + 0.8, y, 2, p.skin);
  });
  ctx.restore();
}

function drawPerson(p, inWater) {
  const t = G.t;
  if (inWater) {
    ctx.strokeStyle = 'rgba(200,230,255,0.45)'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.arc(p.x, p.y, 7 + Math.sin(t * 4 + p.id) * 1.5, 0, Math.PI * 2); ctx.stroke();
    circle(p.x, p.y, 3.4, p.skin);
    if (p.isPlayer) { ctx.strokeStyle = '#ffd23f'; ctx.lineWidth = 1.6; ctx.beginPath(); ctx.arc(p.x, p.y, 10, 0, Math.PI * 2); ctx.stroke(); }
  } else {
    circle(p.x + 1.5, p.y + 1.5, PR, 'rgba(0,0,0,0.25)');
    circle(p.x, p.y, PR, p.color);
    if (p.isPlayer) { ctx.strokeStyle = '#fff'; ctx.lineWidth = 1.5; ctx.stroke(); }
    circle(p.x + Math.cos(p.ang) * 1.6, p.y + Math.sin(p.ang) * 1.6, 3.3, p.skin);
    if (p.cold > 1) circle(p.x, p.y, PR, `rgba(140,200,255,${p.cold / 100 * 0.6})`);
  }
  if (p.stun > 0) {
    for (let i = 0; i < 3; i++) {
      const a = t * 6 + i * 2.1;
      circle(p.x + Math.cos(a) * 8, p.y - 4 + Math.sin(a) * 3, 1.5, '#ffe066');
    }
  }
  if (p.isPlayer) {
    const by = p.y - 13 + Math.sin(t * 5) * 1.5;
    ctx.fillStyle = '#ffd23f';
    ctx.beginPath(); ctx.moveTo(p.x - 4, by - 5); ctx.lineTo(p.x + 4, by - 5); ctx.lineTo(p.x, by); ctx.fill();
  }
}

function drawFunnel(x, y) {
  ctx.fillStyle = 'rgba(0,0,0,0.3)'; ctx.beginPath(); ctx.ellipse(x + 10, y + 10, 26, 20, 0, 0, 7); ctx.fill();
  ctx.fillStyle = '#d8a13a'; ctx.beginPath(); ctx.ellipse(x, y, 26, 20, 0, 0, 7); ctx.fill();
  ctx.strokeStyle = '#a5761f'; ctx.lineWidth = 1.5; ctx.stroke();
  ctx.fillStyle = '#161616'; ctx.beginPath(); ctx.ellipse(x, y, 19, 14, 0, 0, 7); ctx.fill();
  ctx.fillStyle = '#2a2a2a'; ctx.beginPath(); ctx.ellipse(x - 2, y - 2, 14, 9, 0, 0, 7); ctx.fill();
}

function hullPath(ext) {
  ctx.beginPath();
  for (let x = 0; x <= SHIP_L; x += 20) ctx.lineTo(x - (x === 0 ? ext : 0), -(hw(x) + ext * (x === 0 ? 0 : 1)));
  ctx.lineTo(SHIP_L + ext, 0);
  for (let x = SHIP_L; x >= 0; x -= 20) ctx.lineTo(x - (x === 0 ? ext : 0), hw(x) + ext * (x === 0 ? 0 : 1));
  ctx.closePath();
}

function drawWaves(x0, x1, y0, y1, t, spacing, alpha) {
  ctx.strokeStyle = `rgba(140,190,240,${alpha})`; ctx.lineWidth = 1.2;
  ctx.beginPath();
  const gx0 = Math.floor(x0 / spacing), gx1 = Math.ceil(x1 / spacing);
  const gy0 = Math.floor(y0 / (spacing * 0.6)), gy1 = Math.ceil(y1 / (spacing * 0.6));
  for (let gx = gx0; gx <= gx1; gx++) for (let gy = gy0; gy <= gy1; gy++) {
    const h = hash(gx * 131 + gy * 17);
    const x = gx * spacing + h * spacing + Math.sin(t * 0.8 + h * 6) * 4;
    const y = gy * spacing * 0.6 + hash(gx * 7 + gy * 311) * spacing * 0.6;
    ctx.moveTo(x - 6, y); ctx.quadraticCurveTo(x, y - 3, x + 6, y);
  }
  ctx.stroke();
}

// ---------------- Ship scene ----------------
function renderShip() {
  const s = shipScale(), p = G.player, t = G.t;
  let fx = p.x, fy = p.y;
  if (p.state === 'boat' || p.state === 'sea') { const b = G.boats[p.boat]; fx = b.x; fy = b.side * HALF * 0.6; }
  if (G.phase === 'dead' && G.deathCam) { fx = G.deathCam.x; fy = G.deathCam.y; }
  const vw = W / 2 / s;
  let camX = vw * 2 > SHIP_L + 200 ? SHIP_L / 2 : clamp(fx, vw - 100, SHIP_L + 100 - vw);
  let camY = clamp(fy * 0.35, -40, 40) - 30 / s;
  if (G.shake > 0) { camX += rand(-1, 1) * G.shake * 6; camY += rand(-1, 1) * G.shake * 6; }
  G.cam = { x: camX, y: camY, s };

  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.fillStyle = '#071423'; ctx.fillRect(0, 0, W, H);
  ctx.setTransform(DPR * s, 0, 0, DPR * s, DPR * (W / 2 - camX * s), DPR * (H / 2 - camY * s));
  const x0 = camX - vw - 20, x1 = camX + vw + 20, y0 = camY - H / 2 / s - 20, y1 = camY + H / 2 / s + 20;
  drawWaves(x0, x1, y0, y1, t, 60, 0.12);

  // hull and deck
  hullPath(9); ctx.fillStyle = '#121212'; ctx.fill();
  hullPath(0); ctx.fillStyle = '#a77f52'; ctx.fill();
  ctx.save(); hullPath(0); ctx.clip();
  ctx.strokeStyle = 'rgba(60,35,10,0.18)'; ctx.lineWidth = 1;
  ctx.beginPath();
  for (let y = -HALF; y <= HALF; y += 7) { ctx.moveTo(Math.max(0, x0), y); ctx.lineTo(Math.min(SHIP_L, x1), y); }
  ctx.stroke();
  ctx.restore();
  ctx.strokeStyle = '#e8e2d0'; ctx.lineWidth = 1.5; hullPath(0); ctx.stroke();

  // gangway zones
  G.boats.forEach(b => {
    if (b.state !== 'loading' && b.state !== 'covered') return;
    const open = b.state === 'loading';
    ctx.setLineDash([4, 4]);
    ctx.strokeStyle = open ? `rgba(61,220,132,${0.6 + Math.sin(t * 6) * 0.3})` : 'rgba(230,195,74,0.5)';
    ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(b.gx, b.gy, 22, 0, Math.PI * 2); ctx.stroke();
    ctx.setLineDash([]);
  });

  // deckhouses & funnels
  for (const h of HOUSES) {
    ctx.fillStyle = 'rgba(0,0,0,0.25)'; ctx.fillRect(h.x + 6, h.y + 6, h.w, h.h);
    ctx.fillStyle = '#ddd6c3'; ctx.fillRect(h.x, h.y, h.w, h.h);
    ctx.strokeStyle = '#9a927e'; ctx.lineWidth = 2; ctx.strokeRect(h.x, h.y, h.w, h.h);
    ctx.fillStyle = '#cbc3ad'; ctx.fillRect(h.x + 10, h.y + 12, h.w - 20, h.h - 24);
    ctx.fillStyle = '#7e8f99';
    for (let x = h.x + 22; x < h.x + h.w - 20; x += 46) ctx.fillRect(x, -6, 16, 12);
  }
  // debris
  for (const d of G.debris) drawDebris(d);
  // dry people
  for (const q of G.people) if (q.state === 'ship' && !q.inWater && !q.isPlayer) drawPerson(q, false);
  if (p.state === 'ship' && !p.inWater) drawPerson(p, false);
  // funnels on top (tall)
  for (const fxp of FUNNELS) if (G.flags['fallen' + fxp] === undefined) drawFunnel(fxp, 0);
  for (const fxp of COLLAPSING) {
    const side = G.flags['fallen' + fxp];
    if (side === undefined) continue;
    ctx.save(); ctx.translate(fxp, side * 60);
    ctx.fillStyle = '#d8a13a'; ctx.fillRect(-22, side < 0 ? -95 : 0, 44, 95);
    ctx.fillStyle = '#161616'; ctx.fillRect(-22, side < 0 ? -95 : 70, 44, 25);
    ctx.strokeStyle = '#7a5514'; ctx.lineWidth = 2; ctx.strokeRect(-22, side < 0 ? -95 : 0, 44, 95);
    ctx.restore();
  }
  // funnel warnings
  for (const e of G.funnelEvents) {
    const a = 0.25 + 0.25 * Math.sin(t * 18);
    ctx.fillStyle = `rgba(255,40,40,${a})`; ctx.fillRect(e.zone.x, e.zone.y, e.zone.w, e.zone.h);
    ctx.strokeStyle = '#ff4040'; ctx.lineWidth = 2; ctx.strokeRect(e.zone.x, e.zone.y, e.zone.w, e.zone.h);
    ctx.fillStyle = '#fff'; ctx.font = 'bold 22px Georgia'; ctx.textAlign = 'center';
    ctx.fillText('!', e.fx, e.zone.y + e.zone.h / 2 + 8);
  }

  // water flooding the deck
  const wl = G.waterline;
  if (wl < x1) {
    const grd = ctx.createLinearGradient(wl, 0, wl + 160, 0);
    grd.addColorStop(0, 'rgba(14,52,92,0.72)'); grd.addColorStop(1, 'rgba(8,26,46,0.97)');
    ctx.fillStyle = grd; ctx.fillRect(wl, y0, Math.max(10, x1 - wl), y1 - y0);
    drawWaves(Math.max(wl, x0), x1, y0, y1, t, 45, 0.15);
    ctx.strokeStyle = 'rgba(220,240,255,0.75)'; ctx.lineWidth = 2.5; ctx.beginPath();
    for (let y = -HALF - 30; y <= HALF + 30; y += 6) ctx.lineTo(wl + Math.sin(y * 0.09 + t * 3) * 4, y);
    ctx.stroke();
  }
  for (const q of G.people) if (q.state === 'ship' && q.inWater) drawPerson(q, true);

  // lifeboats
  G.boats.forEach(b => {
    let yoff = 0, alpha = 1;
    if (b.state === 'launched' || b.state === 'lost') {
      const a = (t - b.launchT) / 4;
      yoff = Math.min(1, a) * 55 + Math.max(0, a - 1) * 25;
      alpha = clamp(1 - (a - 1.2) / 1.2, 0, 1);
      if (alpha <= 0) return;
    }
    const by = b.side * (HALF + 17 + yoff);
    ctx.strokeStyle = '#3a3a3a'; ctx.lineWidth = 2;
    ctx.beginPath();
    for (const dx of [-24, 24]) { ctx.moveTo(b.x + dx, b.side * (HALF - 2)); ctx.lineTo(b.x + dx, b.side * (HALF + 17)); }
    ctx.stroke();
    drawLifeboat(b.x, by, 60, 20, 0, b.seats, b.cap, alpha);
    if (b.state === 'covered') {
      ctx.fillStyle = 'rgba(90,100,90,0.85)'; rr(b.x - 28, by - 8, 56, 16, 6); ctx.fill();
    }
    // label
    ctx.globalAlpha = alpha;
    ctx.font = 'bold 11px Georgia'; ctx.textAlign = 'center';
    const ly = b.side * (HALF + 44 + yoff) + (b.side > 0 ? 6 : 0);
    let label, col;
    if (b.state === 'covered') { label = `Boat ${b.id} · opens in ${Math.ceil(b.openT - t)}s`; col = '#e6c34a'; }
    else if (b.state === 'loading') { label = `Boat ${b.id} · ${b.seats.length}/${b.cap} · leaves ${Math.max(0, Math.ceil(b.closeT - t))}s`; col = '#3ddc84'; }
    else if (b.state === 'launched') { label = `Boat ${b.id} lowered`; col = '#8fb8e8'; }
    else { label = `Boat ${b.id} lost`; col = '#ff8f8f'; }
    ctx.fillStyle = 'rgba(0,0,0,0.55)'; const tw = ctx.measureText(label).width;
    rr(b.x - tw / 2 - 5, ly - 11, tw + 10, 15, 4); ctx.fill();
    ctx.fillStyle = col; ctx.fillText(label, b.x, ly);
    ctx.globalAlpha = 1;
    if (b.state === 'loading' && b.boarder) {
      const q = b.boarder;
      ctx.strokeStyle = q.isPlayer ? '#ffd23f' : '#ffffff'; ctx.lineWidth = 2.5;
      ctx.beginPath(); ctx.arc(q.x, q.y, 10, -Math.PI / 2, -Math.PI / 2 + Math.PI * 2 * b.progress); ctx.stroke();
    }
  });

  // darkness when lights go out
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  if (G.flags.lights && G.phase !== 'ocean') {
    const sx = W / 2 + (fx - camX) * s, sy = H / 2 + (fy - camY) * s;
    const g = ctx.createRadialGradient(sx, sy, 60 * s, sx, sy, 260 * s);
    g.addColorStop(0, 'rgba(0,0,8,0)'); g.addColorStop(1, 'rgba(0,0,8,0.82)');
    ctx.fillStyle = g; ctx.fillRect(0, 0, W, H);
  }
  if (G.flash > 0) { ctx.fillStyle = `rgba(255,230,230,${G.flash * 0.22})`; ctx.fillRect(0, 0, W, H); }
}

function drawDebris(d) {
  ctx.save(); ctx.translate(d.x, d.y);
  if (d.k === 'chair') {
    ctx.fillStyle = '#6f4b27'; ctx.fillRect(-d.w / 2, -d.h / 2, d.w, d.h);
    ctx.strokeStyle = '#4a3018'; ctx.lineWidth = 1; ctx.beginPath();
    for (let x = -d.w / 2 + 3; x < d.w / 2; x += 3) { ctx.moveTo(x, -d.h / 2); ctx.lineTo(x, d.h / 2); }
    ctx.stroke();
  } else if (d.k === 'crate') {
    ctx.fillStyle = '#9a7442'; ctx.fillRect(-d.w / 2, -d.h / 2, d.w, d.h);
    ctx.strokeStyle = '#5c4220'; ctx.lineWidth = 1.5; ctx.strokeRect(-d.w / 2, -d.h / 2, d.w, d.h);
    ctx.beginPath(); ctx.moveTo(-d.w / 2, -d.h / 2); ctx.lineTo(d.w / 2, d.h / 2); ctx.moveTo(d.w / 2, -d.h / 2); ctx.lineTo(-d.w / 2, d.h / 2); ctx.stroke();
  } else if (d.k === 'barrel') {
    ctx.rotate(d.spin);
    circle(0, 0, d.w / 2, '#6b4a2a');
    ctx.strokeStyle = '#2e2e2e'; ctx.lineWidth = 1.2; ctx.beginPath(); ctx.arc(0, 0, d.w / 2 - 1.5, 0, 7); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(-d.w / 2, 0); ctx.lineTo(d.w / 2, 0); ctx.stroke();
  } else {
    ctx.fillStyle = '#141414'; ctx.fillRect(-d.w / 2, -d.h / 2, d.w, d.h);
    ctx.fillStyle = '#eee'; ctx.fillRect(-d.w / 2 + 2, d.h / 2 - 5, d.w - 4, 3);
  }
  ctx.restore();
}

// ---------------- Ocean scene ----------------
function renderOcean() {
  const o = G.ocean, s = oceanScale(), t = G.t;
  let camX = o.x * 0.25, camY = o.y - (H * 0.2) / s;
  if (G.shake > 0) { camX += rand(-1, 1) * G.shake * 6; camY += rand(-1, 1) * G.shake * 6; }
  const vw = W / 2 / s, vh = H / 2 / s;
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.fillStyle = '#061220'; ctx.fillRect(0, 0, W, H);
  ctx.setTransform(DPR * s, 0, 0, DPR * s, DPR * (W / 2 - camX * s), DPR * (H / 2 - camY * s));
  const x0 = camX - vw, x1 = camX + vw, y0 = camY - vh, y1 = camY + vh;
  drawWaves(x0, x1, y0, y1, t, 50, 0.16);

  // pack ice on the edges
  for (const side of [-1, 1]) {
    ctx.fillStyle = '#c9dcea';
    ctx.beginPath();
    const ys = Math.floor(y0 / 30) * 30;
    ctx.moveTo(side * (OCEAN_HALF + 400), ys - 30);
    for (let y = ys - 30; y <= y1 + 30; y += 30) ctx.lineTo(side * (OCEAN_HALF + 4 + hash(y * 0.37) * 22), y);
    ctx.lineTo(side * (OCEAN_HALF + 400), y1 + 30);
    ctx.closePath(); ctx.fill();
    ctx.strokeStyle = '#8fb3cc'; ctx.lineWidth = 2; ctx.stroke();
  }

  // Carpathia
  if (o.carp) {
    const left = Math.max(0, T_RESCUE - t);
    const cy = o.y - 170 - left * 32;
    ctx.save(); ctx.translate(0, cy);
    ctx.fillStyle = '#1a1a1a';
    ctx.beginPath(); ctx.moveTo(0, 150); ctx.quadraticCurveTo(45, 100, 45, 0); ctx.lineTo(45, -150); ctx.lineTo(-45, -150); ctx.lineTo(-45, 0); ctx.quadraticCurveTo(-45, 100, 0, 150); ctx.fill();
    ctx.fillStyle = '#e8e2d0'; ctx.fillRect(-28, -110, 56, 160);
    ctx.fillStyle = '#c0392b'; ctx.beginPath(); ctx.ellipse(0, -30, 16, 12, 0, 0, 7); ctx.fill();
    ctx.fillStyle = '#111'; ctx.beginPath(); ctx.ellipse(0, -30, 10, 7, 0, 0, 7); ctx.fill();
    for (let i = 0; i < 14; i++) circle(i % 2 ? 40 : -40, -130 + i * 18, 2.2, `rgba(255,230,150,${0.6 + 0.4 * Math.sin(t * 3 + i)})`);
    ctx.fillStyle = '#fff'; ctx.font = 'bold 14px Georgia'; ctx.textAlign = 'center'; ctx.fillText('CARPATHIA', 0, 175);
    ctx.restore();
    if (Math.sin(t * 2) > 0.7) { const g = ctx.createRadialGradient(0, cy - 100, 0, 0, cy - 100, 120); g.addColorStop(0, 'rgba(255,90,90,0.35)'); g.addColorStop(1, 'rgba(255,90,90,0)'); ctx.fillStyle = g; ctx.fillRect(-120, cy - 220, 240, 240); }
  }

  // icebergs
  for (const b of o.ice) {
    if (b.y < y0 - 80 || b.y > y1 + 80) continue;
    const poly = (sc) => {
      ctx.beginPath();
      b.pts.forEach((k, i) => { const a = b.rot + i / b.pts.length * Math.PI * 2; ctx.lineTo(b.x + Math.cos(a) * b.r * k * sc, b.y + Math.sin(a) * b.r * k * sc); });
      ctx.closePath();
    };
    poly(1.25); ctx.fillStyle = 'rgba(110,180,220,0.18)'; ctx.fill();
    poly(1); ctx.fillStyle = '#e9f5ff'; ctx.fill(); ctx.strokeStyle = '#8fc0e0'; ctx.lineWidth = 2; ctx.stroke();
    ctx.save(); ctx.translate(b.x, b.y); ctx.scale(0.55, 0.55); ctx.translate(-b.x - b.r * 0.2, -b.y - b.r * 0.25); poly(1); ctx.fillStyle = '#ffffff'; ctx.fill(); ctx.restore();
  }

  // sharks
  for (const sh of o.sharks) {
    if (sh.y < y0 - 60 || sh.y > y1 + 60) continue;
    ctx.save(); ctx.translate(sh.x, sh.y); ctx.rotate(sh.ang);
    const wig = Math.sin(sh.wig) * 0.25;
    ctx.fillStyle = sh.killer ? 'rgba(20,20,30,0.55)' : 'rgba(40,60,80,0.4)';
    ctx.beginPath(); ctx.ellipse(0, 0, sh.killer ? 22 : 19, sh.killer ? 7 : 6, 0, 0, 7); ctx.fill();
    ctx.beginPath(); ctx.moveTo(-18, 0); ctx.lineTo(-30, -7 + wig * 10); ctx.lineTo(-27, 0); ctx.lineTo(-30, 7 + wig * 10); ctx.closePath(); ctx.fill();
    ctx.strokeStyle = 'rgba(200,230,255,0.35)'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(4, -4); ctx.lineTo(-14, -9); ctx.moveTo(4, 4); ctx.lineTo(-14, 9); ctx.stroke();
    ctx.fillStyle = sh.killer ? '#2a2f36' : '#9aa9b6';
    ctx.beginPath(); ctx.moveTo(6, 0); ctx.lineTo(-6, -4); ctx.lineTo(-4, 0); ctx.lineTo(-6, 4); ctx.closePath(); ctx.fill();
    if (sh.killer) { ctx.strokeStyle = '#ff3b3b'; ctx.lineWidth = 1.6; ctx.stroke(); circle(10, -3, 1.3, '#ff3b3b'); circle(10, 3, 1.3, '#ff3b3b'); }
    ctx.restore();
  }

  // player's boat
  const b = o.b;
  if (!o.dead) drawLifeboat(o.x, o.y, 52, 20, -Math.PI / 2 + clamp(o.vx * 0.002, -0.3, 0.3), b.seats, b.cap, 1, o.oar);
  else {
    ctx.save(); ctx.translate(o.x, o.y); ctx.rotate(1.2);
    ctx.fillStyle = '#5e4a32'; ctx.fillRect(-20, -6, 40, 12);
    ctx.fillStyle = '#f2efe6'; ctx.fillRect(-20, -6, 40, 3); ctx.restore();
  }

  // night & lantern
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  const sx = W / 2 + (o.x - camX) * s, sy = H / 2 + (o.y - camY) * s;
  const g = ctx.createRadialGradient(sx, sy, 90 * s, sx, sy, 420 * s);
  g.addColorStop(0, 'rgba(0,0,10,0)'); g.addColorStop(1, 'rgba(0,0,10,0.6)');
  ctx.fillStyle = g; ctx.fillRect(0, 0, W, H);
  const lg = ctx.createRadialGradient(sx, sy, 0, sx, sy, 70 * s);
  lg.addColorStop(0, 'rgba(255,210,120,0.18)'); lg.addColorStop(1, 'rgba(255,210,120,0)');
  ctx.fillStyle = lg; ctx.fillRect(0, 0, W, H);
}

// ---------------- HUD ----------------
function bar(x, y, w, h, v, col, label) {
  ctx.fillStyle = 'rgba(0,0,0,0.5)'; rr(x, y, w, h, 4); ctx.fill();
  ctx.fillStyle = col; rr(x + 2, y + 2, Math.max(0, (w - 4) * clamp(v, 0, 1)), h - 4, 3); ctx.fill();
  ctx.fillStyle = '#fff'; ctx.font = '11px system-ui, sans-serif'; ctx.textAlign = 'left';
  ctx.fillText(label, x + 6, y + h - 4);
}

function drawMinimap() {
  const mw = Math.min(W - 40, 560), mh = 46, mx = (W - mw) / 2, my = 8;
  ctx.fillStyle = 'rgba(0,0,0,0.55)'; rr(mx - 6, my - 4, mw + 12, mh + 8, 8); ctx.fill();
  const sx = mw / SHIP_L, sy = mh / (2 * (HALF + 36));
  const X = x => mx + x * sx, Y = y => my + mh / 2 + y * sy;
  ctx.beginPath();
  for (let x = 0; x <= SHIP_L; x += 50) ctx.lineTo(X(x), Y(-hw(x)));
  for (let x = SHIP_L; x >= 0; x -= 50) ctx.lineTo(X(x), Y(hw(x)));
  ctx.closePath(); ctx.fillStyle = '#7a5b3a'; ctx.fill();
  ctx.fillStyle = '#cfc8b4'; for (const h of HOUSES) ctx.fillRect(X(h.x), Y(h.y), h.w * sx, h.h * sy);
  ctx.fillStyle = '#a33'; for (const f of G.fallen) ctx.fillRect(X(f.x), Y(f.y), f.w * sx, f.h * sy);
  if (G.waterline < SHIP_L + 20) { ctx.fillStyle = 'rgba(30,100,180,0.85)'; ctx.fillRect(X(Math.max(0, G.waterline)), my, mx + mw - X(Math.max(0, G.waterline)), mh); }
  for (const q of G.people) if (q.state === 'ship' && !q.isPlayer) { ctx.fillStyle = q.inWater ? '#8fc0ff' : '#ddd'; ctx.fillRect(X(q.x) - 0.8, Y(q.y) - 0.8, 1.6, 1.6); }
  for (const b of G.boats) {
    let c = '#777';
    if (b.state === 'covered') c = b.openT - G.t < 10 ? '#e6c34a' : '#888';
    else if (b.state === 'loading') c = Math.sin(G.t * 8) > -0.3 ? '#3ddc84' : '#1d6b40';
    else if (b.state === 'launched') c = '#4a90d9';
    else c = '#a33';
    if (b.state === 'launched' || b.state === 'lost') continue;
    ctx.fillStyle = c; ctx.fillRect(X(b.x) - 5, Y(b.side * (HALF + 18)) - 2.5, 10, 5);
  }
  const p = G.player;
  if (p.state === 'ship') { circle(X(p.x), Y(p.y), 3.2, '#ffd23f'); ctx.strokeStyle = '#000'; ctx.lineWidth = 1; ctx.stroke(); }
  ctx.fillStyle = '#9fb3c8'; ctx.font = '10px system-ui'; ctx.textAlign = 'left'; ctx.fillText('STERN', mx, my + mh + 14);
  ctx.textAlign = 'right'; ctx.fillText('BOW', mx + mw, my + mh + 14);
}

function drawIndicators() {
  const c = G.cam, p = G.player;
  if (p.state !== 'ship') return;
  for (const b of G.boats) {
    const loading = b.state === 'loading' && b.seats.length < b.cap;
    const soon = b.state === 'covered' && b.openT - G.t < 8;
    if (!loading && !soon) continue;
    const sx = W / 2 + (b.gx - c.x) * c.s, sy = H / 2 + (b.gy - c.y) * c.s;
    if (sx > 30 && sx < W - 30 && sy > 70 && sy < H - 30) continue;
    const ex = clamp(sx, 34, W - 34), ey = clamp(sy, 80, H - 34);
    const a = Math.atan2(sy - ey, sx - ex);
    ctx.save(); ctx.translate(ex, ey);
    ctx.fillStyle = loading ? '#3ddc84' : '#e6c34a';
    ctx.rotate(a); ctx.beginPath(); ctx.moveTo(14, 0); ctx.lineTo(-6, -9); ctx.lineTo(-6, 9); ctx.fill();
    ctx.restore();
    ctx.fillStyle = '#fff'; ctx.font = 'bold 11px system-ui'; ctx.textAlign = 'center';
    ctx.fillText(`${b.id}`, ex - Math.cos(a) * 16, ey - Math.sin(a) * 16 + 4);
  }
}

function drawHUD() {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  const p = G.player, t = G.t;
  const atSea = !!G.ocean;
  const top = atSea ? 12 : 70;
  // clock panel
  ctx.fillStyle = 'rgba(0,0,0,0.55)'; rr(10, top, 200, atSea ? 84 : 100, 8); ctx.fill();
  ctx.fillStyle = '#ffd23f'; ctx.font = 'bold 20px Georgia'; ctx.textAlign = 'left';
  ctx.fillText(clock(t), 20, top + 24);
  ctx.fillStyle = '#cfe3ff'; ctx.font = '12px system-ui';
  ctx.fillText(`Survived ${fmt(p.state === 'dead' ? p.deathT : t)}`, 92, top + 22);
  if (atSea || p.state === 'sea') {
    const o = G.ocean;
    ctx.fillText(`Carpathia in ${fmt(T_RESCUE - t)}`, 20, top + 44);
    if (o) bar(20, top + 54, 180, 16, o.stamina, o.rowing ? '#ffb347' : '#e09f3e', 'Rowing strength');
  } else {
    const sunk = Math.round(G.sf * 100);
    ctx.fillText(G.sf >= 1 ? 'Titanic has sunk' : `Ship flooded: ${sunk}%`, 20, top + 44);
    bar(20, top + 52, 180, 16, 1 - p.cold / 100, p.cold > 50 ? '#e05555' : '#6fb7ff', p.inWater ? 'Body heat — GET OUT OF THE WATER' : 'Body heat');
    bar(20, top + 74, 180, 16, p.stamina, '#e0c341', 'Stamina (Shift to sprint)');
  }
  // contextual hint
  let hint = '';
  if (p.state === 'ship') {
    const near = G.boats.find(b => b.state === 'loading' && dist(p.x, p.y, b.gx, b.gy) < 40);
    const nearC = G.boats.find(b => b.state === 'covered' && dist(p.x, p.y, b.gx, b.gy) < 40);
    if (near) {
      if (near.boarder === p) hint = input.action ? 'Boarding… keep holding!' : 'HOLD SPACE to board!';
      else hint = 'Someone is ahead of you — push to the front of the gangway!';
    } else if (nearC) hint = `Boat ${nearC.id} isn't ready yet — opens in ${Math.ceil(nearC.openT - t)}s`;
    else if (p.inWater) hint = 'You are in the freezing water — move toward the stern (left)!';
    else if (!G.boats.some(b => b.state === 'loading' || b.state === 'covered')) hint = 'No lifeboats left… head for the stern and hold on!';
  } else if (p.state === 'boat') hint = 'Aboard! Waiting for the boat to be lowered…';
  else if (G.phase === 'ocean' && t - G.ocean.t0 < 8) hint = '←/→ steer · ↑ or SPACE row hard · ↓ slow down';
  if (hint) {
    ctx.font = 'bold 15px system-ui'; ctx.textAlign = 'center';
    const tw = ctx.measureText(hint).width;
    ctx.fillStyle = 'rgba(0,0,0,0.6)'; rr(W / 2 - tw / 2 - 12, H - 92, tw + 24, 28, 8); ctx.fill();
    ctx.fillStyle = '#fff'; ctx.fillText(hint, W / 2, H - 73);
  }
  // messages
  ctx.font = '13px system-ui'; ctx.textAlign = 'right';
  let y = top + 14;
  for (const m of G.msgs) {
    const age = t - m.t;
    if (age > 8) continue;
    ctx.globalAlpha = clamp(1.6 - age / 5, 0, 1);
    const tw = ctx.measureText(m.text).width;
    if (W - tw - 30 < 220 && W < 700) continue;
    ctx.fillStyle = 'rgba(0,0,0,0.5)'; rr(W - tw - 22, y - 13, tw + 14, 19, 5); ctx.fill();
    ctx.fillStyle = m.color; ctx.fillText(m.text, W - 15, y + 1);
    y += 23;
  }
  ctx.globalAlpha = 1;
  // touch controls
  if (touch.used) {
    if (touch.id !== null) {
      ctx.strokeStyle = 'rgba(255,255,255,0.35)'; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(touch.ox, touch.oy, 55, 0, 7); ctx.stroke();
      circle(touch.ox + clamp(touch.x - touch.ox, -55, 55), touch.oy + clamp(touch.y - touch.oy, -55, 55), 20, 'rgba(255,255,255,0.35)');
    }
    circle(W - 70, H - 140, 42, touch.actionId !== null ? 'rgba(61,220,132,0.6)' : 'rgba(255,255,255,0.2)');
    ctx.fillStyle = '#fff'; ctx.font = 'bold 13px system-ui'; ctx.textAlign = 'center';
    ctx.fillText(G.phase === 'ocean' ? 'ROW' : 'BOARD', W - 70, H - 136);
  }
  if (paused) {
    ctx.fillStyle = 'rgba(0,0,0,0.5)'; ctx.fillRect(0, 0, W, H);
    ctx.fillStyle = '#fff'; ctx.font = 'bold 36px Georgia'; ctx.textAlign = 'center'; ctx.fillText('Paused — press P', W / 2, H / 2);
  }
}

function render() {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  if (!G) { renderTitleBg(); return; }
  if (G.ocean) renderOcean(); else renderShip();
  if (!G.ocean) { ctx.setTransform(DPR, 0, 0, DPR, 0, 0); drawMinimap(); drawIndicators(); }
  if (G.phase !== 'results') drawHUD();
}

function renderTitleBg() {
  const t = performance.now() / 1000;
  ctx.fillStyle = '#061220'; ctx.fillRect(0, 0, W, H);
  ctx.save(); ctx.translate(0, t * 8 % 60); drawWaves(-60, W + 60, -60, H + 60, t, 70, 0.14); ctx.restore();
}

// ---------------- UI wiring ----------------
const $ = id => document.getElementById(id);
function show(id) { for (const k of ['title', 'dead', 'results']) $(k).classList.toggle('hidden', k !== id); }

function startGame() {
  initAudio();
  if (AC && AC.state === 'suspended') AC.resume();
  newGame();
  show(null);
  paused = false;
  sound('horn');
}

function onPlayerDeath() {
  const p = G.player;
  $('dead-cause').textContent = p.cause;
  $('dead-time').textContent = `You survived ${fmt(p.deathT)} (until ${clock(p.deathT)}).`;
  setTimeout(() => { if (G && G.phase === 'dead' && !G.done) show('dead'); }, 1400);
}

function showResults() {
  G.phase = 'results';
  const p = G.player;
  const all = [...G.people].sort((a, b) => survScore(b) - survScore(a));
  const rank = 1 + G.people.filter(q => survScore(q) > survScore(p)).length;
  const rescued = G.people.filter(q => q.state === 'rescued').length;
  const boarded = G.boats.reduce((s, b) => s + b.seats.length, 0);
  const lostSea = G.people.filter(q => q.cause.startsWith('Lifeboat')).length;
  const won = p.state === 'rescued';
  const surv = won ? T_RESCUE : p.deathT;
  let best = 0;
  try { best = +localStorage.getItem('titanic_best') || 0; if (surv > best) localStorage.setItem('titanic_best', String(surv)); } catch (e) { }
  const newBest = surv > best;
  $('res-title').textContent = won ? 'RESCUED!' : 'Lost to the sea';
  $('res-title').className = won ? 'win' : 'lose';
  $('res-sub').textContent = won
    ? `The Carpathia pulled you from Boat ${G.boats[p.boat].id} at 04:10. You are one of ${rescued} survivors.`
    : `${p.cause} at ${clock(p.deathT)} — you lasted ${fmt(p.deathT)}.`;
  $('res-rank').textContent = `Rank #${rank} of ${G.people.length}` + (newBest ? ' · New personal best!' : best ? ` · Best: ${best >= T_RESCUE ? 'Rescued' : fmt(best)}` : '');
  $('res-stats').innerHTML =
    `<div><b>${boarded}</b> made it into a lifeboat</div><div><b>${lostSea}</b> were lost from lifeboats</div><div><b>${rescued}</b> rescued</div><div><b>${G.people.length - boarded}</b> went down with the ship</div>`;
  const rows = [];
  const top = all.slice(0, 10);
  if (!top.includes(p)) top.push(p);
  for (const q of top) {
    const r = 1 + G.people.filter(z => survScore(z) > survScore(q)).length;
    rows.push(`<tr class="${q.isPlayer ? 'me' : ''}"><td>#${r}</td><td>${q.name}</td><td>${q.state === 'rescued' ? 'Rescued' : q.cause}</td><td>${q.state === 'rescued' ? '—' : fmt(q.deathT)}</td></tr>`);
  }
  $('res-table').innerHTML = `<tr><th></th><th>Passenger</th><th>Fate</th><th>Time</th></tr>` + rows.join('');
  show('results');
}

function resize() {
  DPR = Math.min(2, window.devicePixelRatio || 1);
  W = window.innerWidth; H = window.innerHeight;
  canvas.width = W * DPR; canvas.height = H * DPR;
  canvas.style.width = W + 'px'; canvas.style.height = H + 'px';
}

let lastTs = 0;
function frame(ts) {
  const dt = Math.min(0.05, (ts - lastTs) / 1000 || 0);
  lastTs = ts;
  readInput();
  if (G && !paused && !G.done && ['ship', 'launching', 'ocean', 'dead'].includes(G.phase)) step(dt);
  render();
  requestAnimationFrame(frame);
}

function initUI() {
  canvas = $('c'); ctx = canvas.getContext('2d');
  resize(); window.addEventListener('resize', resize);
  window.addEventListener('keydown', e => {
    keys[e.code] = true;
    if (['Space', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight'].includes(e.code)) e.preventDefault();
    if (e.code === 'KeyP' && G && !G.done && G.phase !== 'results') paused = !paused;
    if (e.code === 'KeyM') muted = !muted;
    if (e.code === 'Enter' && (!G || G.phase === 'results')) startGame();
  });
  window.addEventListener('keyup', e => { keys[e.code] = false; });
  window.addEventListener('blur', () => { for (const k in keys) keys[k] = false; });
  const tstart = e => {
    touch.used = true;
    for (const t of e.changedTouches) {
      if (t.clientX > W * 0.6 && t.clientY > H * 0.4) touch.actionId = t.identifier;
      else if (touch.id === null) { touch.id = t.identifier; touch.ox = touch.x = t.clientX; touch.oy = touch.y = t.clientY; }
    }
  };
  canvas.addEventListener('touchstart', e => { e.preventDefault(); tstart(e); }, { passive: false });
  canvas.addEventListener('touchmove', e => {
    e.preventDefault();
    for (const t of e.changedTouches) if (t.identifier === touch.id) { touch.x = t.clientX; touch.y = t.clientY; }
  }, { passive: false });
  const tend = e => {
    for (const t of e.changedTouches) {
      if (t.identifier === touch.id) touch.id = null;
      if (t.identifier === touch.actionId) touch.actionId = null;
    }
  };
  canvas.addEventListener('touchend', tend); canvas.addEventListener('touchcancel', tend);
  $('start').onclick = startGame;
  $('again').onclick = startGame;
  $('ff').onclick = () => { show(null); fastForward(); };
  try { const b = +localStorage.getItem('titanic_best'); if (b) $('best').textContent = `Your best: ${b >= T_RESCUE ? 'Rescued by the Carpathia' : fmt(b) + ' survived'}`; } catch (e) { }
  show('title');
  // debug hooks for screenshots: #t=60 (fast-forward ship), #ocean=40 (start at sea for 40s)
  const m = location.hash.match(/^#(t|ocean)=(\d+)/);
  if (m) {
    startGame();
    if (m[1] === 'ocean') {
      const b = G.boats.find(b => b.state !== 'launched');
      G.player.x = b.gx; G.player.y = b.gy; board(G.player, b, G.boats.indexOf(b)); launch(b); startOcean();
    }
    const end = G.t + +m[2];
    while (G.t < end && !G.done) { input.dx = Math.sin(G.t) * 0.5; step(1 / 30); }
  }
  requestAnimationFrame(frame);
}

if (HAS_DOM) window.addEventListener('DOMContentLoaded', initUI);
