'use strict';

// ── ANCHOR TYPES ─────────────────────────────────────────────────────────────
// 0 = Small/Green ×10  1 = Medium/Blue ×3  2 = Large/Red ×1
// attachBonus: instant score on attachment
// speedRange:  [min, max] speedFactor (anchor world-scroll multiplier)
const AT = [
  { r: 9,  grabR: 64,  bonusMult: 10, attachBonus: 5000, speedRange: [1.05, 1.15], hex: '#39ff6a', rgb: '57,255,106', name: 'GREEN' },
  { r: 13, grabR: 88,  bonusMult:  3, attachBonus: 2500, speedRange: [0.95, 1.05], hex: '#00d4ff', rgb: '0,212,255',  name: 'BLUE'  },
  { r: 19, grabR: 106, bonusMult:  1, attachBonus: -1000, speedRange: [0.90, 1.00], hex: '#ff1a4e', rgb: '255,26,78',  name: 'RED'   },
];

// ── 3 INDEPENDENT ANCHOR STREAMS ─────────────────────────────────────────────
// Each stream has a soft vertical bias and its own spawn cursor.
const STREAM_DEFS = [
  { yBias: 0.25, yRange: 0.10 }, // top lane
  { yBias: 0.50, yRange: 0.13 }, // middle lane (most reachable from start)
  { yBias: 0.75, yRange: 0.10 }, // bottom lane
];

// ── CONFIG ───────────────────────────────────────────────────────────────────
const CFG = {
  orbitRadius:        70,
  omega:              3.0,       // rad/s, clockwise on screen
  orbitSpeed:         70 * 3.0,  // tangent speed = 210 px/s

  scrollSpeedInit:    155,
  scrollSpeedMax:     480,
  scrollAccel:        4.0,       // px/s per second

  // Per-stream anchor spacing (3 streams × ~480 ≈ one anchor every ~160 px globally)
  anchorDxMin:        380,
  anchorDxMax:        580,

  // Free-flight physics
  surgeBoost:         220,       // px/s added along tangent direction on detach
  maxBackwardScreenV: 250,       // clamp: screen-relative vx cannot go below −this (prevents instant left-edge death)
  velDamping:         0.75,      // X: vx→driftTarget exponential decay coefficient (half-life ≈ 0.92s → 1.8s crossover)
  velDampingY:        0.9,       // Y: slower decay — preserves vertical momentum for curved trajectories
  driftRatio:         0.5,       // equilibrium screen vx = −scrollSpeed×driftRatio (scales with difficulty)
  gravity:            8,         // px/s² very subtle downward pull — ballistic arcs without forcing downward bias
  redOrbitDrain:      200,       // pts/s drained from score while orbiting a red anchor

  playerScreenXRatio: 0.35,
  anchorYMin:         0.16,
  anchorYMax:         0.84,
  minAnchorSep:       42,        // minimum centre-to-centre distance (visual non-overlap)

  comboStep:          0.5,
  comboMax:           4.0,

  trailMax:           28,
  playerR:            6,
  playerGlowR:        22,

  crashDuration:      5.0,       // full explosion show before game over screen
  crashTimeScale:     0.20,      // slow-mo factor for zoom/shake feel (particles run real-time)
  particleCount:      100,       // neon explosion shards
  shakeAmplitude:     18,        // strong impact shake
  shakeDecay:         2.5,       // slow decay — rumble felt for ~2s
  zoomTarget:         1.08,
};

const DANGER_ZONE_WIDTH = 150; // px — controls visual zone width, shake/pulse trigger, and death boundary (player dies at x=0, the left edge of this zone)

// ── CANVAS ───────────────────────────────────────────────────────────────────
const canvas = document.getElementById('c');
const ctx    = canvas.getContext('2d');

function resize() {
  canvas.width  = window.innerWidth;
  canvas.height = window.innerHeight;
}
resize();
window.addEventListener('resize', resize);

// ── SEEDED RNG (Mulberry32) ──────────────────────────────────────────────────
function mkRng(seed) {
  let s = (seed ^ 0xDEADBEEF) >>> 0;
  return () => {
    s = (s + 0x6D2B79F5) >>> 0;
    let t = Math.imul(s ^ (s >>> 15), 1 | s);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 0x100000000;
  };
}

// ── PERSISTENT STATE ─────────────────────────────────────────────────────────
let highScore = +(localStorage.getItem('ob_hs') || 0);
let inputHeld = false;

// ── GAME STATE ───────────────────────────────────────────────────────────────
// 'boot' | 'running' | 'crash' | 'gameover'
let STATE = 'boot';

let rng, player, cameraX = 0;
let anchors, streams;
let scrollSpeed, runTime, score;
let lastColorName, colorComboCount, comboMultiplier;
let maxComboReached, bestBonusTaken;
let comboPulseTimer, playerBurstTimer;
let trail, particles, floatingTexts;
let crashTimer, crashZoom, crashFade, shakeX, shakeY;
let explosionCoreTimer; // bright core flash at death position
let hasDetached;  // gravity is gated on this — no downward pull before first detach
let redFlashTimer;    // screen red-tint pulse on red anchor attach
let detachFlashTimer; // brief white flash on detach

// Reusable audio — created once to avoid memory leaks and browser policy issues
const swooshAudio = new Audio('assets/audio/swoosh.wav');
swooshAudio.volume = 0.5;

const deathAudio = new Audio('assets/audio/death.mp3');
deathAudio.volume = 0.7;

const musicAudio = new Audio('assets/audio/music.mp3');
musicAudio.loop   = true;
musicAudio.volume = 0.5;

const gameOverAudio = new Audio('assets/audio/game-over.mp3');
gameOverAudio.loop   = true;
gameOverAudio.volume = 0.45;

const introAudio = new Audio('assets/audio/intro.mp3');
introAudio.loop   = true;
introAudio.volume = 0.5;
let introPlaying  = false;

// ── MUTE SYSTEM ───────────────────────────────────────────────────────────────
let isMuted = localStorage.getItem('ob_mute') === '1';
const MUTE_BTN = { x: 0, y: 0, size: 0 }; // updated each render frame for click detection

function setMute(b) {
  isMuted = b;
  localStorage.setItem('ob_mute', b ? '1' : '0');
  swooshAudio.volume   = b ? 0 : 0.5;
  deathAudio.volume    = b ? 0 : 0.7;
  musicAudio.volume    = b ? 0 : 0.5;
  gameOverAudio.volume = b ? 0 : 0.45;
  introAudio.volume    = b ? 0 : 0.5;
}

// Apply persisted mute preference immediately on load
if (isMuted) setMute(true);

function isMuteButtonClick(x, y) {
  return x >= MUTE_BTN.x && x <= MUTE_BTN.x + MUTE_BTN.size &&
         y >= MUTE_BTN.y && y <= MUTE_BTN.y + MUTE_BTN.size;
}

function gameOverMusicStart() {
  if (!gameOverAudio.paused) return;  // already running — don't stack
  gameOverAudio.currentTime = 0;
  gameOverAudio.volume = isMuted ? 0 : 0.45;
  try { gameOverAudio.play(); } catch (_) { /* autoplay blocked — silent fail */ }
}

function gameOverMusicStop() {
  gameOverAudio.pause();
  gameOverAudio.currentTime = 0;
}

function introMusicStart() {
  if (introPlaying) return;
  introAudio.currentTime = 0;
  introAudio.volume = isMuted ? 0 : 0.5;
  introPlaying = true; // optimistic — prevents double-play if key pressed before Promise resolves
  try {
    const p = introAudio.play();
    if (p instanceof Promise) p.catch(() => { introPlaying = false; }); // reset on block
  } catch (_) { introPlaying = false; /* autoplay blocked — silent fail */ }
}

function introMusicStop() {
  introPlaying = false;
  try { introAudio.pause(); introAudio.currentTime = 0; } catch (_) {}
}

let musicFadeInterval = null;

function musicStart() {
  gameOverMusicStop();  // stop game-over track before gameplay music begins
  if (musicFadeInterval) { clearInterval(musicFadeInterval); musicFadeInterval = null; }
  musicAudio.volume = isMuted ? 0 : 0.5;
  if (musicAudio.paused) {
    try { musicAudio.play(); } catch (_) { /* autoplay blocked — silent fail */ }
  }
}

function musicFadeOut() {
  if (musicFadeInterval) { clearInterval(musicFadeInterval); }
  // Fade from current volume to 0 over ~2.5s (step every 40ms, 62 steps × 0.008 ≈ 2480ms)
  musicFadeInterval = setInterval(() => {
    if (musicAudio.volume > 0.006) {
      musicAudio.volume = Math.max(0, musicAudio.volume - 0.008);
    } else {
      musicAudio.volume = 0;
      musicAudio.pause();
      musicAudio.currentTime = 0;
      clearInterval(musicFadeInterval);
      musicFadeInterval = null;
    }
  }, 40);
}

// Snapshot for game-over display
let goScore = 0, goMaxCombo = 0, goBestBonus = 1.0;

// ── SPAWN ─────────────────────────────────────────────────────────────────────
function mkAnchor(x, y, ti) {
  const t = AT[ti];
  const [sfMin, sfMax] = t.speedRange;
  const speedFactor = sfMin + rng() * (sfMax - sfMin);
  return { x, y, r: t.r, grabR: t.grabR, bonusMult: t.bonusMult,
           attachBonus: t.attachBonus, speedFactor,
           hex: t.hex, rgb: t.rgb, name: t.name, ti, used: false };
}

function pickTypeIdx() {
  // [small, medium, large] weights grow more balanced at higher difficulty
  const w = runTime < 15  ? [5,  80, 15]
          : runTime < 45  ? [25, 50, 25]
                          : [35, 35, 30];
  let r = rng() * (w[0] + w[1] + w[2]);
  for (let i = 0; i < 3; i++) { r -= w[i]; if (r <= 0) return i; }
  return 1;
}

// Spawn one anchor from a single stream, respecting visual non-overlap.
function spawnFromStream(def, stream) {
  const H     = canvas.height;
  const dx    = CFG.anchorDxMin + rng() * (CFG.anchorDxMax - CFG.anchorDxMin);
  const baseX = stream.lastSpawnX + dx;
  const ti    = pickTypeIdx();
  const newR  = AT[ti].r;

  // Try up to 10 positions to avoid visual overlap with existing anchors.
  let chosenX = baseX, chosenY = 0;
  let placed  = false;

  for (let attempt = 0; attempt < 10; attempt++) {
    const cx   = baseX + (attempt === 0 ? 0 : (rng() - 0.5) * 90);
    const rawY = def.yBias * H + (rng() - 0.5) * 2.0 * def.yRange * H;
    const cy   = Math.max(H * CFG.anchorYMin, Math.min(H * CFG.anchorYMax, rawY));

    const overlaps = anchors.some(a => {
      const ex = cx - a.x, ey = cy - a.y;
      return Math.sqrt(ex * ex + ey * ey) < a.r + newR + CFG.minAnchorSep;
    });

    if (!overlaps) { chosenX = cx; chosenY = cy; placed = true; break; }
  }

  if (!placed) {
    // Fall back: place at baseX with stream bias, ignoring overlap (rare)
    chosenX = baseX;
    chosenY = Math.max(H * CFG.anchorYMin,
              Math.min(H * CFG.anchorYMax, def.yBias * H + (rng() - 0.5) * 60));
  }

  anchors.push(mkAnchor(chosenX, chosenY, ti));
  stream.lastSpawnX = chosenX;
}

function maintainAnchors() {
  // Cull anchors well off the left edge (never cull the currently-orbited anchor)
  const cullX = cameraX - 280;
  anchors = anchors.filter(a => a === player.orbitAnchor || a.x > cullX);

  // Each stream spawns independently until it has anchors far enough ahead
  const aheadX = cameraX + canvas.width + 620;
  STREAM_DEFS.forEach((def, i) => {
    while (streams[i].lastSpawnX < aheadX) spawnFromStream(def, streams[i]);
  });
}

// ── PHYSICS ──────────────────────────────────────────────────────────────────
function initRun() {
  rng             = mkRng(Date.now() ^ (Math.random() * 0xFFFFFFFF | 0));
  scrollSpeed     = CFG.scrollSpeedInit;
  runTime         = score = crashTimer = 0;
  lastColorName   = null;
  colorComboCount = 0;
  comboMultiplier = 1.0;
  maxComboReached = 0;
  bestBonusTaken  = 1.0;
  comboPulseTimer = playerBurstTimer = 0;
  hasDetached = false;
  redFlashTimer = 0;
  detachFlashTimer = 0;
  explosionCoreTimer = 0;
  crashZoom = 1; crashFade = 0;
  shakeX = shakeY = 0;
  trail = []; particles = []; floatingTexts = [];

  const W = canvas.width, H = canvas.height;
  player = {
    x: 0, y: H * 0.5,
    vx: CFG.scrollSpeedInit, vy: 0,
    orbiting: false, orbitAnchor: null, orbitAngle: 0,
  };
  cameraX = player.x - W * CFG.playerScreenXRatio;

  // Stagger stream spawn cursors so anchors are naturally spread out
  streams = STREAM_DEFS.map((_, i) => ({
    lastSpawnX: player.x - 80 + i * 110,
  }));

  // Guaranteed starter anchor — blue, vertically centred, always reachable at run start
  const st = AT[1];
  anchors = [{
    x: player.x + 230, y: player.y,
    r: st.r, grabR: st.grabR, bonusMult: st.bonusMult,
    attachBonus: st.attachBonus, speedFactor: 1.0,
    hex: st.hex, rgb: st.rgb, name: st.name, ti: 1, used: false,
  }];
  maintainAnchors();
}

function toSX(wx) { return wx - cameraX; } // world X → screen X

function physics(dt) {
  // Base survival score — always accrues regardless of orbit state
  score += scrollSpeed * dt;

  // Variable-speed anchors: each anchor has a speedFactor that offsets its world position
  // relative to the camera, making green anchors appear faster, red ones slower.
  for (const a of anchors) {
    a.x += (1 - a.speedFactor) * scrollSpeed * dt;
  }

  if (player.orbiting) {
    // Clockwise orbit: angle increases in y-down screen coords
    player.orbitAngle += CFG.omega * dt;
    const a = player.orbitAnchor;
    // Player follows anchor's (possibly moving) world position
    player.x = a.x + CFG.orbitRadius * Math.cos(player.orbitAngle);
    player.y = a.y + CFG.orbitRadius * Math.sin(player.orbitAngle);
    // Camera still scrolls — orbiting pushes player toward left edge intentionally
    if (!inputHeld) detach();
    // Orbital scoring: green/blue add bonus; red drains score (tactical survival, not reward)
    if (a.ti === 2) {
      score -= CFG.redOrbitDrain * dt;
    } else {
      score += scrollSpeed * dt * a.bonusMult * comboMultiplier;
    }
  } else {
    // Free flight
    player.x += player.vx * dt;
    player.y += player.vy * dt;
    if (inputHeld) tryAttach();

    // X: decay toward driftTarget = scrollSpeed × (1 − driftRatio)
    // Equilibrium screen vx = −scrollSpeed × driftRatio (scales with difficulty)
    const driftTarget = scrollSpeed * (1 - CFG.driftRatio);
    const xDecay = Math.exp(-CFG.velDamping * dt);
    player.vx = driftTarget + (player.vx - driftTarget) * xDecay;

    // Y: slower decay than X + subtle gravity (only after first detach — never at game start)
    const yDecay = Math.exp(-CFG.velDampingY * dt);
    player.vy = player.vy * yDecay + (hasDetached ? CFG.gravity * dt : 0);
  }

  // World scroll (independent of player movement)
  cameraX    += scrollSpeed * dt;
  scrollSpeed = Math.min(CFG.scrollSpeedMax, scrollSpeed + CFG.scrollAccel * dt);

  if (comboPulseTimer   > 0) comboPulseTimer   -= dt;
  if (playerBurstTimer  > 0) playerBurstTimer  -= dt;
  if (redFlashTimer     > 0) redFlashTimer     -= dt;
  if (detachFlashTimer  > 0) detachFlashTimer  -= dt;

  // Floating texts: drift upward and fade
  for (const ft of floatingTexts) { ft.wy -= 50 * dt; ft.life -= 1.7 * dt; }
  floatingTexts = floatingTexts.filter(ft => ft.life > 0);

  // Trail
  trail.push({ x: player.x, y: player.y });
  if (trail.length > CFG.trailMax) trail.shift();

  // Death conditions
  if (toSX(player.x) < 0)                                 { die(); return; }
  if (player.y < -120 || player.y > canvas.height + 120)  { die(); return; }

  maintainAnchors();
}

// Grab the closest unused anchor within its individual grabR
function tryAttach() {
  const px = player.x, py = player.y;
  let best = null, bestD2 = Infinity;
  for (const a of anchors) {
    if (a.used) continue;
    const dx = px - a.x, dy = py - a.y;
    const d2 = dx * dx + dy * dy;
    if (d2 <= a.grabR * a.grabR && d2 < bestD2) { best = a; bestD2 = d2; }
  }
  if (best) attach(best);
}

function attach(a) {
  const dx = player.x - a.x, dy = player.y - a.y;
  player.orbitAngle  = Math.atan2(dy, dx);
  player.orbiting    = true;
  player.orbitAnchor = a;
  // Snap to orbit circle
  player.x = a.x + CFG.orbitRadius * Math.cos(player.orbitAngle);
  player.y = a.y + CFG.orbitRadius * Math.sin(player.orbitAngle);

  // ── Color combo ──────────────────────────────────────────────────────────
  const prevCount = colorComboCount;
  colorComboCount = (a.name === lastColorName) ? colorComboCount + 1 : 1;
  lastColorName   = a.name;
  comboMultiplier = Math.min(CFG.comboMax, 1 + (colorComboCount - 1) * CFG.comboStep);
  if (colorComboCount > maxComboReached) maxComboReached = colorComboCount;
  if (a.bonusMult    > bestBonusTaken)   bestBonusTaken  = a.bonusMult;

  if (colorComboCount > prevCount || prevCount === 0) {
    comboPulseTimer  = 0.38;
    playerBurstTimer = 0.30;
  }

  // Instant attach bonus — combo-scaled for green/blue, flat penalty for red
  const scaledBonus = (a.ti === 2)
    ? a.attachBonus                       // red: -1000 (penalty, no combo)
    : a.attachBonus * colorComboCount;    // green/blue: base × comboCount
  score += scaledBonus;

  // Floating attach value (anchored to the anchor, drifts up)
  floatingTexts.push({
    wx: a.x, wy: a.y - a.r - 14,
    text: a.ti === 2 ? `-1,000` : `+${scaledBonus.toLocaleString()}`,
    color: a.hex, life: 1.0,
  });

  // Combo milestone float (large, near player) — green/blue chain ≥ 2
  if (a.ti !== 2 && colorComboCount >= 2) {
    floatingTexts.push({
      wx: player.x, wy: player.y - 32,
      text: `COMBO ×${colorComboCount}`,
      color: a.hex, life: 1.4, large: true,
    });
  }

  // Red anchor penalty: brief screen flash
  if (a.ti === 2) redFlashTimer = 0.35;
}

function detach() {
  hasDetached = true; // unlock gravity for curved free-flight trajectories
  const θ  = player.orbitAngle;
  const tx = -Math.sin(θ);  // clockwise tangent X (unit vector)
  const ty =  Math.cos(θ);  // clockwise tangent Y (unit vector)

  // Launch: scroll base + full tangent velocity + boost along tangent direction.
  // Boost is direction-aware — detach early = forward, detach late = backward.
  const launchSpeed = CFG.orbitSpeed + CFG.surgeBoost;
  player.vx = scrollSpeed + tx * launchSpeed;
  player.vy = ty * launchSpeed;

  // Soft clamp on backward screen-relative speed to prevent instant left-edge death
  player.vx = Math.max(scrollSpeed - CFG.maxBackwardScreenV, player.vx);
  player.orbitAnchor.used = true;
  player.orbiting    = false;
  player.orbitAnchor = null;

  // Detach sound — reset position to allow rapid replays without overlap buildup
  try {
    swooshAudio.currentTime = 0;
    swooshAudio.play();
  } catch (_) { /* blocked by browser autoplay policy — silent fail */ }

  // White flash feedback on detach
  detachFlashTimer = 0.12;
}

// ── DEATH / CRASH ─────────────────────────────────────────────────────────────
function die() {
  if (STATE === 'crash') return;
  STATE = 'crash';
  musicFadeOut();
  try { deathAudio.currentTime = 0; deathAudio.play(); } catch (_) { /* autoplay blocked */ }

  goScore     = score;
  goMaxCombo  = maxComboReached;
  goBestBonus = bestBonusTaken;

  if (score > highScore) {
    highScore = score;
    localStorage.setItem('ob_hs', Math.floor(highScore));
  }

  crashTimer = 0; crashZoom = 1; crashFade = 0;
  shakeX = shakeY = CFG.shakeAmplitude;
  explosionCoreTimer = 0.55;  // bright flash lasts half a second

  const SHARD_COLORS = ['#00ccff', '#ffffff', '#39ff6a', '#00ffff', '#cc44ff', '#ff6600', '#00d4ff', '#ff00aa'];

  particles = [];
  for (let i = 0; i < CFG.particleCount; i++) {
    const a   = rng() * Math.PI * 2;
    const col = SHARD_COLORS[Math.floor(rng() * SHARD_COLORS.length)];
    const tier = rng();
    let spd, decay, r;

    if (tier < 0.35) {
      // Tier 1 — fast shards: rocket to viewport edges, fade over 2–4s
      spd   = 220 + rng() * 560;
      decay = 0.18 + rng() * 0.25;   // life ~2.5–5.5s
      r     = 1.5 + rng() * 3.5;
    } else if (tier < 0.70) {
      // Tier 2 — medium drifters: linger in mid-field, fat glowing blobs
      spd   = 50 + rng() * 180;
      decay = 0.10 + rng() * 0.12;   // life ~5–10s (outlast the 5s window)
      r     = 4 + rng() * 8;
    } else {
      // Tier 3 — slow lingering glows: huge orbs that bloom near the centre
      spd   = 10 + rng() * 55;
      decay = 0.07 + rng() * 0.08;   // life ~7–14s — still alive at 5s cutoff
      r     = 8 + rng() * 14;
    }

    particles.push({
      x: player.x, y: player.y,
      vx: Math.cos(a) * spd,
      vy: Math.sin(a) * spd,
      life: 1.0, decay, r, color: col,
    });
  }
}

function updateCrash(dt) {
  crashTimer += dt;
  const t = Math.min(1, crashTimer / CFG.crashDuration);

  // Zoom peaks quickly then holds
  crashZoom = 1 + (CFG.zoomTarget - 1) * Math.min(1, t * 3);

  // Dark fade starts at 85% (4.25s) — full 4s of unobstructed explosion
  const fadeT = Math.max(0, (t - 0.85) / 0.15);
  crashFade = fadeT * 0.92;

  shakeX *= Math.exp(-CFG.shakeDecay * dt);
  shakeY *= Math.exp(-CFG.shakeDecay * dt);

  if (explosionCoreTimer > 0) explosionCoreTimer -= dt;

  // Particles run real-time (not slow-mo) for energetic explosion feel
  for (const p of particles) {
    p.x  += p.vx * dt;
    p.y  += p.vy * dt;
    p.vy += 18 * dt;  // very gentle gravity — lets fast shards reach the viewport edges
    p.life -= p.decay * dt;
  }

  if (crashTimer >= CFG.crashDuration) {
    STATE = 'gameover';
    particles = []; shakeX = shakeY = 0;
    gameOverMusicStart();
  }
}

// ── RENDER ────────────────────────────────────────────────────────────────────
function render() {
  const W = canvas.width, H = canvas.height;
  ctx.clearRect(0, 0, W, H);

  if (STATE === 'boot')     { renderBoot(W, H);     renderMuteButton(W, H); return; }
  if (STATE === 'gameover') { renderGameOver(W, H); renderMuteButton(W, H); return; }

  renderBackground(W, H);

  // Danger zone: drawn after background, before world elements (correct z-order)
  renderDangerZone(W, H);

  ctx.save();
  if (STATE === 'crash') {
    const px = toSX(player.x), py = player.y;
    const ox = (Math.random() - 0.5) * 2 * shakeX;
    const oy = (Math.random() - 0.5) * 2 * shakeY;
    ctx.translate(px + ox, py + oy);
    ctx.scale(crashZoom, crashZoom);
    ctx.translate(-px, -py);
  } else if (STATE === 'running' && toSX(player.x) < DANGER_ZONE_WIDTH) {
    // Very subtle world-shake when orbiter enters danger zone
    const depth  = Math.max(0, (DANGER_ZONE_WIDTH - toSX(player.x)) / DANGER_ZONE_WIDTH);
    const dShake = depth * Math.sin(performance.now() / 1000 * 15);
    ctx.translate(dShake, dShake * 0.5);
  }

  renderAnchors(W, H);
  renderTrail();
  renderPlayer();
  renderParticles();
  renderFloatingTexts();
  ctx.restore();

  if (STATE === 'crash' && crashFade > 0) {
    ctx.fillStyle = `rgba(7,7,15,${crashFade})`;
    ctx.fillRect(0, 0, W, H);
  }

  // Explosion core flash — expands to fill most of the viewport
  if (STATE === 'crash' && explosionCoreTimer > 0) {
    const t   = Math.max(0, explosionCoreTimer / 0.55);
    const cx  = toSX(player.x), cy = player.y;
    // Expands from 40px up to 55% of the smaller viewport dimension
    const rMax = Math.min(W, H) * 0.55;
    const r    = 40 + (1 - t) * rMax;
    const g    = ctx.createRadialGradient(cx, cy, 0, cx, cy, r);
    g.addColorStop(0,    `rgba(255,255,255,${t * 0.98})`);
    g.addColorStop(0.15, `rgba(160,240,255,${t * 0.85})`);
    g.addColorStop(0.40, `rgba(0,160,255,${t * 0.55})`);
    g.addColorStop(0.70, `rgba(80,0,200,${t * 0.25})`);
    g.addColorStop(1,    'rgba(0,0,0,0)');
    ctx.fillStyle = g;
    ctx.beginPath();
    ctx.arc(cx, cy, r, 0, Math.PI * 2);
    ctx.fill();
  }

  // White flash on detach — tactile surge feedback
  if (detachFlashTimer > 0) {
    const alpha = (detachFlashTimer / 0.12) * 0.18;
    ctx.fillStyle = `rgba(255,255,255,${alpha})`;
    ctx.fillRect(0, 0, W, H);
  }

  // Red anchor attach flash — brief crimson screen tint
  if (redFlashTimer > 0) {
    const alpha = (redFlashTimer / 0.35) * 0.10;
    ctx.fillStyle = `rgba(255,20,20,${alpha})`;
    ctx.fillRect(0, 0, W, H);
  }

  renderHUD(W, H);
  renderOffScreenIndicator(W, H);
  renderMuteButton(W, H);
}

// ── BOOT SCREEN ───────────────────────────────────────────────────────────────
function renderBoot(W, H) {
  renderBackground(W, H);

  const ts = Math.min(W * 0.07, 56), ss = Math.min(W * 0.033, 21);
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';

  // Layered neon title — outer bloom, mid colour, bright core
  ctx.font = `bold ${ts}px monospace`;
  ctx.shadowColor = '#0066cc'; ctx.shadowBlur = 52;
  ctx.fillStyle = '#003366';
  ctx.fillText('NEON DRIFT', W / 2, H * 0.43);
  ctx.shadowBlur = 22;
  ctx.fillStyle = '#00d4ff';
  ctx.fillText('NEON DRIFT', W / 2, H * 0.43);
  ctx.shadowBlur = 8;
  ctx.fillStyle = '#ffffff';
  ctx.fillText('NEON DRIFT', W / 2, H * 0.43);
  ctx.shadowBlur = 0;

  ctx.fillStyle = '#3a6688'; ctx.font = `${ss}px monospace`;
  ctx.fillText('SPACE  ·  CLICK  ·  TAP  to start', W / 2, H * 0.53);
  if (highScore > 0) {
    ctx.fillStyle = '#1a3040'; ctx.font = `${ss * 0.85}px monospace`;
    ctx.fillText(`Best: ${Math.floor(highScore)}`, W / 2, H * 0.61);
  }
  ctx.textBaseline = 'alphabetic';
}

// ── GAME OVER SCREEN ──────────────────────────────────────────────────────────
function renderGameOver(W, H) {
  ctx.fillStyle = 'rgba(7,7,15,0.97)';
  ctx.fillRect(0, 0, W, H);

  // Slow pulsing vignette — distinguishes this state visually, breathes with the music
  const vigPulse = 0.5 + 0.5 * Math.sin(performance.now() / 1800);
  const vg = ctx.createRadialGradient(W / 2, H / 2, H * 0.18, W / 2, H / 2, H * 0.78);
  vg.addColorStop(0, 'rgba(0,0,0,0)');
  vg.addColorStop(1, `rgba(0,0,20,${0.28 + vigPulse * 0.14})`);
  ctx.fillStyle = vg;
  ctx.fillRect(0, 0, W, H);

  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';

  // ── GAME OVER title ──────────────────────────────────────────────────────
  const ts = Math.min(W * 0.075, 58);
  ctx.shadowColor = '#ee3333'; ctx.shadowBlur = 24;
  ctx.fillStyle   = '#ff5555'; ctx.font = `bold ${ts}px monospace`;
  ctx.fillText('GAME OVER', W / 2, H * 0.17);
  ctx.shadowBlur  = 0;

  // ── Dominant score number ────────────────────────────────────────────────
  const scoreFs  = Math.min(W * 0.19, 148);
  const pulse    = 0.5 + 0.5 * Math.sin(performance.now() / 420);
  const glowBlur = 30 + pulse * 26;

  // Small "FINAL SCORE" label above the number
  const labelFs = Math.min(W * 0.026, 19);
  ctx.fillStyle = '#3a5070'; ctx.font = `${labelFs}px monospace`;
  ctx.fillText('FINAL SCORE', W / 2, H * 0.40 - scoreFs * 0.56);

  ctx.shadowColor = '#44aaff'; ctx.shadowBlur = glowBlur;
  ctx.fillStyle   = '#ffffff'; ctx.font = `bold ${scoreFs}px monospace`;
  ctx.fillText(Math.floor(goScore), W / 2, H * 0.42);
  ctx.shadowBlur  = 0;

  // ── Stats row ────────────────────────────────────────────────────────────
  const ss     = Math.min(W * 0.030, 21);
  const lineH  = ss * 1.75;
  const startY = H * 0.64;
  const stats  = [
    ['Best Score', `${Math.floor(highScore)}`],
    ['Max Combo',  `×${goMaxCombo}`],
  ];
  stats.forEach(([label, val], i) => {
    const y = startY + i * lineH;
    ctx.textAlign = 'right';
    ctx.fillStyle = '#3d5265'; ctx.font = `${ss * 0.82}px monospace`;
    ctx.fillText(label + ':', W / 2 - 8, y);
    ctx.textAlign = 'left';
    ctx.fillStyle = '#c8ddf0'; ctx.font = `bold ${ss * 0.82}px monospace`;
    ctx.fillText(val, W / 2 + 8, y);
  });

  // ── Restart prompt ───────────────────────────────────────────────────────
  const blink = (performance.now() % 950) < 580;
  ctx.textAlign = 'center';
  ctx.fillStyle = blink ? '#99aacc' : '#2a3a4a';
  ctx.font      = `${Math.min(W * 0.026, 19)}px monospace`;
  ctx.fillText('SPACE  ·  CLICK  ·  TAP  to restart', W / 2, H * 0.84);
  ctx.textBaseline = 'alphabetic';
}

// ── CYBERPUNK BACKGROUND ──────────────────────────────────────────────────────
function renderBackground(W, H) {
  // Clear canvas — background video shows through the transparent canvas
  ctx.clearRect(0, 0, W, H);

  // Grid lines — vertical scroll with camera, horizontal static
  const sp  = 90;
  const cam = cameraX || 0;
  const ox  = -((cam % sp + sp) % sp);
  ctx.lineWidth   = 0.5;
  ctx.strokeStyle = 'rgba(0,180,255,0.045)';
  for (let gx = ox; gx < W + sp; gx += sp) {
    ctx.beginPath(); ctx.moveTo(gx, 0); ctx.lineTo(gx, H); ctx.stroke();
  }
  for (let gy = sp; gy < H; gy += sp) {
    ctx.beginPath(); ctx.moveTo(0, gy); ctx.lineTo(W, gy); ctx.stroke();
  }

  // Scanline overlay
  ctx.fillStyle = 'rgba(0,0,0,0.028)';
  for (let sy = 0; sy < H; sy += 5) {
    ctx.fillRect(0, sy, W, 2);
  }
}

// ── DANGER ZONE ───────────────────────────────────────────────────────────────
function renderDangerZone(W, H) {
  const now      = performance.now() / 1000;
  const playerSX = toSX(player.x);
  const inZone   = playerSX < DANGER_ZONE_WIDTH;

  // Opacity: base 0.5, smooth pulse to 0.7 when player enters zone
  const baseA = inZone
    ? 0.60 + 0.10 * Math.sin(now * 10)   // 0.5 ↔ 0.7 smooth pulse
    : 0.50;

  // Gradient strip: full opacity at left edge, fades to transparent at DANGER_ZONE_WIDTH px
  const grad = ctx.createLinearGradient(0, 0, DANGER_ZONE_WIDTH, 0);
  grad.addColorStop(0, `rgba(220,0,0,${baseA})`);
  grad.addColorStop(1, 'rgba(220,0,0,0)');
  ctx.fillStyle = grad;
  ctx.fillRect(0, 0, DANGER_ZONE_WIDTH, H);

  // Red screen vignette when orbiter is inside the zone
  if (inZone) {
    const vigA = 0.07 + 0.04 * Math.sin(now * 10);
    const vg   = ctx.createRadialGradient(W * 0.1, H / 2, 0, W / 2, H / 2, W * 0.65);
    vg.addColorStop(0, `rgba(180,0,0,${vigA})`);
    vg.addColorStop(1, 'rgba(180,0,0,0)');
    ctx.fillStyle = vg;
    ctx.fillRect(0, 0, W, H);
  }
}

// ── ANCHORS ───────────────────────────────────────────────────────────────────
function renderAnchors(W, H) {
  const now = performance.now() / 1000;

  // Primary highlight target: nearest upcoming unused anchor by world X
  let primaryAnchor = null, primaryDx = Infinity;
  for (const a of anchors) {
    if (!a.used && a.x > player.x) {
      const dx = a.x - player.x;
      if (dx < primaryDx) { primaryDx = dx; primaryAnchor = a; }
    }
  }

  for (const a of anchors) {
    const asx     = toSX(a.x);
    if (asx < -190 || asx > W + 190) continue;
    const asy       = a.y;
    const isPrimary = a === primaryAnchor;
    const isOrbit   = player.orbiting && player.orbitAnchor === a;

    // Per-anchor phase offset so they pulse out of sync
    const phaseOff = (a.x * 0.019 + a.y * 0.013) % (Math.PI * 2);
    const pulse    = 0.5 + 0.5 * Math.sin(now * 2.6 + phaseOff);

    // Faint orbit ring while attached
    if (isOrbit) {
      ctx.strokeStyle = `rgba(${a.rgb},0.10)`;
      ctx.lineWidth   = 1.5;
      ctx.beginPath();
      ctx.arc(asx, asy, CFG.orbitRadius, 0, Math.PI * 2);
      ctx.stroke();
    }

    if (!a.used) {
      // ── Layer 1: Outer Glow (additive blend) ──────────────────────────────
      let gr, ga;
      if (isPrimary) {
        const dist = Math.sqrt((a.x - player.x) ** 2 + (a.y - player.y) ** 2);
        const hf   = Math.max(0, 1 - dist / (W * 0.55));
        gr = 30 + hf * 30 + pulse * 14;
        ga = 0.20 + hf * 0.35;
      } else {
        gr = 22 + pulse * 8;
        ga = 0.14 + pulse * 0.09;
      }
      ctx.save();
      ctx.globalCompositeOperation = 'lighter';
      const gg = ctx.createRadialGradient(asx, asy, 0, asx, asy, gr);
      gg.addColorStop(0, `rgba(${a.rgb},${ga})`);
      gg.addColorStop(1, `rgba(${a.rgb},0)`);
      ctx.fillStyle = gg;
      ctx.beginPath();
      ctx.arc(asx, asy, gr, 0, Math.PI * 2);
      ctx.fill();
      ctx.restore();

      // ── Layer 2: Rotating Energy Ring ─────────────────────────────────────
      const rotSpeed = a.ti === 0 ? 2.4 : a.ti === 1 ? 1.4 : 0.9;

      // Primary ring — rotates clockwise
      ctx.save();
      ctx.translate(asx, asy);
      ctx.rotate(now * rotSpeed + phaseOff);
      ctx.setLineDash([4, 7]);
      ctx.strokeStyle = `rgba(${a.rgb},${0.28 + pulse * 0.42})`;
      ctx.lineWidth   = 1.3;
      ctx.shadowColor = a.hex;
      ctx.shadowBlur  = 3 + pulse * 7;
      ctx.beginPath();
      ctx.arc(0, 0, a.r + 3 + pulse * 3, 0, Math.PI * 2);
      ctx.stroke();
      ctx.setLineDash([]);
      ctx.shadowBlur = 0;
      ctx.restore();

      // Counter-rotating outer ring — only on primary anchor for extra flair
      if (isPrimary) {
        ctx.save();
        ctx.translate(asx, asy);
        ctx.rotate(-(now * rotSpeed * 0.55) + phaseOff);
        ctx.setLineDash([2, 11]);
        ctx.strokeStyle = `rgba(${a.rgb},${0.12 + pulse * 0.16})`;
        ctx.lineWidth   = 0.8;
        ctx.shadowColor = a.hex;
        ctx.shadowBlur  = 2;
        ctx.beginPath();
        ctx.arc(0, 0, a.r + 8 + pulse * 4, 0, Math.PI * 2);
        ctx.stroke();
        ctx.setLineDash([]);
        ctx.shadowBlur = 0;
        ctx.restore();
      }

      // ── Layer 3: Core Gradient (centre→bright, mid→saturated, edge→dark) ──
      const hx    = asx - a.r * 0.28;
      const hy    = asy - a.r * 0.28;
      const coreG = ctx.createRadialGradient(hx, hy, 0, asx, asy, a.r);
      if (a.ti === 0) {
        // Neon lime — vibrant, high-risk
        coreG.addColorStop(0,    '#d0ffe8');
        coreG.addColorStop(0.28, '#39ff6a');
        coreG.addColorStop(0.65, '#0c7028');
        coreG.addColorStop(1,    '#030f06');
      } else if (a.ti === 1) {
        // Electric cyan — standard
        coreG.addColorStop(0,    '#d0f6ff');
        coreG.addColorStop(0.28, '#00d4ff');
        coreG.addColorStop(0.65, '#004e70');
        coreG.addColorStop(1,    '#00090e');
      } else {
        // Neon crimson — safe but heavy
        coreG.addColorStop(0,    '#ffd0dc');
        coreG.addColorStop(0.28, '#ff1a4e');
        coreG.addColorStop(0.65, '#6e001a');
        coreG.addColorStop(1,    '#0f0003');
      }
      ctx.fillStyle = coreG;
      ctx.beginPath();
      ctx.arc(asx, asy, a.r, 0, Math.PI * 2);
      ctx.fill();

      // Subtle pulsing centre highlight (very slight brightness breath)
      const cf = ctx.createRadialGradient(asx, asy, 0, asx, asy, a.r * 0.55);
      cf.addColorStop(0, `rgba(255,255,255,${0.04 + pulse * 0.13})`);
      cf.addColorStop(1, 'rgba(255,255,255,0)');
      ctx.fillStyle = cf;
      ctx.beginPath();
      ctx.arc(asx, asy, a.r * 0.55, 0, Math.PI * 2);
      ctx.fill();

      // ── Inner Spark Particles ──────────────────────────────────────────────
      ctx.shadowColor = a.hex;
      ctx.shadowBlur  = 5;
      ctx.fillStyle   = 'rgba(255,255,255,0.95)';
      const sc = a.ti === 0 ? 2 : a.ti === 1 ? 3 : 4;
      for (let s = 0; s < sc; s++) {
        const sa = now * 4.2 * (s % 2 === 0 ? 1 : -1.4) + (s * Math.PI * 2 / sc) + phaseOff;
        const sr = a.r * (0.22 + 0.14 * Math.sin(now * 3.1 + s * 1.9));
        ctx.beginPath();
        ctx.arc(asx + Math.cos(sa) * sr, asy + Math.sin(sa) * sr, 0.9, 0, Math.PI * 2);
        ctx.fill();
      }
      ctx.shadowBlur = 0;

    } else {
      // ── Used / spent anchor ────────────────────────────────────────────────
      const ug = ctx.createRadialGradient(asx, asy, 0, asx, asy, 14);
      ug.addColorStop(0, 'rgba(55,55,90,0.06)');
      ug.addColorStop(1, 'rgba(55,55,90,0)');
      ctx.fillStyle = ug;
      ctx.beginPath();
      ctx.arc(asx, asy, 14, 0, Math.PI * 2);
      ctx.fill();

      ctx.fillStyle = '#0c0c1a';
      ctx.beginPath();
      ctx.arc(asx, asy, a.r, 0, Math.PI * 2);
      ctx.fill();
    }
  }
}

// ── TRAIL ─────────────────────────────────────────────────────────────────────
function renderTrail() {
  if (trail.length < 2) return;
  for (let i = 1; i < trail.length; i++) {
    const p = i / trail.length;
    ctx.strokeStyle = `rgba(0,210,255,${p * 0.55})`;
    ctx.lineWidth   = p * 2.8;
    ctx.beginPath();
    ctx.moveTo(toSX(trail[i - 1].x), trail[i - 1].y);
    ctx.lineTo(toSX(trail[i    ].x), trail[i    ].y);
    ctx.stroke();
  }
}

// ── PLAYER ────────────────────────────────────────────────────────────────────
function renderPlayer() {
  if (STATE === 'crash') return; // orbiter has shattered — explosion takes over
  const px = toSX(player.x), py = player.y;

  // Combo burst ring — expands outward on combo gain
  if (playerBurstTimer > 0) {
    const t   = playerBurstTimer / 0.30;
    const bR  = CFG.playerGlowR + (1 - t) * 40;
    const col = lastColorName === 'GREEN' ? '57,255,106'
              : lastColorName === 'RED'   ? '255,26,78'
                                         : '0,212,255';
    const bg  = ctx.createRadialGradient(px, py, 0, px, py, bR);
    bg.addColorStop(0, `rgba(${col},${t * 0.45})`);
    bg.addColorStop(1, `rgba(${col},0)`);
    ctx.fillStyle = bg;
    ctx.beginPath(); ctx.arc(px, py, bR, 0, Math.PI * 2); ctx.fill();
  }

  // Outer wide energy aura
  const aura = ctx.createRadialGradient(px, py, 0, px, py, CFG.playerGlowR * 2.2);
  aura.addColorStop(0,   'rgba(0,200,255,0.20)');
  aura.addColorStop(0.5, 'rgba(0,140,220,0.08)');
  aura.addColorStop(1,   'rgba(0,0,0,0)');
  ctx.fillStyle = aura;
  ctx.beginPath(); ctx.arc(px, py, CFG.playerGlowR * 2.2, 0, Math.PI * 2); ctx.fill();

  // Inner core glow
  const g = ctx.createRadialGradient(px, py, 0, px, py, CFG.playerGlowR);
  g.addColorStop(0,    'rgba(130,235,255,0.90)');
  g.addColorStop(0.38, 'rgba(60,185,255,0.55)');
  g.addColorStop(1,    'rgba(0,0,0,0)');
  ctx.fillStyle = g;
  ctx.beginPath(); ctx.arc(px, py, CFG.playerGlowR, 0, Math.PI * 2); ctx.fill();

  // Core dot with neon shadow
  ctx.shadowColor = '#00ccff';
  ctx.shadowBlur  = 14;
  ctx.fillStyle   = '#ffffff';
  ctx.beginPath(); ctx.arc(px, py, CFG.playerR, 0, Math.PI * 2); ctx.fill();
  ctx.shadowBlur  = 0;
}

// ── PARTICLES ─────────────────────────────────────────────────────────────────
function renderParticles() {
  if (particles.length === 0) return;
  // Additive blending during explosion — neon shards bloom against the dark
  ctx.globalCompositeOperation = 'lighter';
  for (const p of particles) {
    if (p.life <= 0) continue;
    const a = Math.max(0, p.life);
    ctx.globalAlpha  = a * a;  // quadratic fade — bright mid-life, sharp fade-out
    ctx.shadowColor  = p.color || '#ffffff';
    ctx.shadowBlur   = 12;
    ctx.fillStyle    = p.color || `hsl(${p.hue ?? 30},100%,70%)`;
    ctx.beginPath();
    ctx.arc(toSX(p.x), p.y, Math.max(0.4, p.r * (0.4 + p.life * 0.6)), 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.globalAlpha              = 1;
  ctx.shadowBlur               = 0;
  ctx.globalCompositeOperation = 'source-over';
}

// ── FLOATING TEXTS ────────────────────────────────────────────────────────────
function renderFloatingTexts() {
  const fsNorm  = Math.min(canvas.width * 0.028, 17);
  const fsLarge = Math.min(canvas.width * 0.044, 28);
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  for (const ft of floatingTexts) {
    if (ft.life <= 0) continue;
    const fs = ft.large ? fsLarge : fsNorm;
    ctx.globalAlpha = Math.min(1, ft.life * 1.8);
    ctx.shadowColor = ft.color;
    ctx.shadowBlur  = ft.large ? 14 : 7;
    ctx.fillStyle   = ft.color;
    ctx.font        = `bold ${fs}px monospace`;
    ctx.fillText(ft.text, toSX(ft.wx), ft.wy);
  }
  ctx.shadowBlur   = 0;
  ctx.globalAlpha  = 1;
  ctx.textBaseline = 'alphabetic';
  ctx.textAlign    = 'left';
}

// ── HUD ───────────────────────────────────────────────────────────────────────
function renderHUD(W, H) {
  const f = Math.min(W * 0.04, 25);
  ctx.textBaseline = 'top';

  // Score (top-left) — holographic glow always; stronger tint when orbiting
  ctx.textAlign   = 'left';
  const orbiting  = player.orbiting;
  const scoreCol  = orbiting ? player.orbitAnchor.hex : '#a0d8f0';
  ctx.shadowColor = orbiting ? player.orbitAnchor.hex : '#00aacc';
  ctx.shadowBlur  = orbiting ? 14 : 6;
  ctx.fillStyle   = scoreCol;
  ctx.font        = `bold ${f}px monospace`;
  ctx.fillText(Math.floor(score), 16, 14);
  ctx.shadowBlur  = 0;

  // Color combo (top-right) — only shown when count ≥ 2
  ctx.textAlign = 'right';
  if (colorComboCount >= 2) {
    const comboCol = lastColorName === 'GREEN' ? '#39ff6a'
                   : lastColorName === 'RED'   ? '#ff1a4e'
                                               : '#00d4ff';
    const pulse = comboPulseTimer > 0 ? comboPulseTimer / 0.38 : 0;
    if (pulse > 0) { ctx.shadowColor = comboCol; ctx.shadowBlur = 8 + pulse * 18; }
    ctx.fillStyle = comboCol;
    ctx.font      = `bold ${f}px monospace`;
    ctx.fillText(`COMBO: ${lastColorName} ×${colorComboCount}`, W - 16, 14);
    ctx.shadowBlur = 0;
  }

  // Best score (smaller, below combo)
  if (highScore > 0) {
    ctx.fillStyle = '#1a3040';
    ctx.font      = `${f * 0.6}px monospace`;
    ctx.fillText(`Best ${Math.floor(highScore)}`, W - 16, f + 22);
  }

  renderLegend(W, H);
  ctx.textBaseline = 'alphabetic';
}

// ── OFF-SCREEN INDICATOR (right / top / bottom edges) ────────────────────────
// Base shape: right-pointing triangle with tip at origin.
// ctx.rotate() orients it for each edge without duplicating draw code.
//   angle =       0  → tip points →  (right edge)
//   angle = -PI/2    → tip points ↓  (top edge, into screen)
//   angle = +PI/2    → tip points ↑  (bottom edge, into screen)
// Priority: right > top > bottom  (horizontal exit shown exclusively if both apply)
function renderOffScreenIndicator(W, H) {
  if (STATE !== 'running') return;

  const px  = toSX(player.x);
  const py  = player.y;
  const PAD = 14;
  const MGN = 20;

  let arrowX, arrowY, angle, dist;

  if (px > W) {
    // Player exited right
    dist   = px - W;
    arrowX = W - MGN;
    arrowY = Math.max(PAD, Math.min(H - PAD, py));
    angle  = 0;
  } else if (py < 0) {
    // Player exited top — arrow at top edge pointing ↓ into screen
    dist   = -py;
    arrowX = Math.max(PAD, Math.min(W - PAD, px));
    arrowY = MGN;
    angle  = -Math.PI / 2;
  } else if (py > H) {
    // Player exited bottom — arrow at bottom edge pointing ↑ into screen
    dist   = py - H;
    arrowX = Math.max(PAD, Math.min(W - PAD, px));
    arrowY = H - MGN;
    angle  = Math.PI / 2;
  } else {
    return;  // on-screen (or off left = death zone, no indicator)
  }

  const fadeIn    = Math.min(1, dist / 60);
  const pulse     = 1 + 0.05 * Math.sin(runTime * 5.5);
  const distScale = 1 + Math.min(dist / 900, 0.25);
  const size      = 12 * pulse * distScale;

  ctx.save();
  ctx.translate(arrowX, arrowY);
  ctx.rotate(angle);

  // Soft aura — sits between tip and base in local space
  ctx.globalAlpha = 0.22 * fadeIn;
  ctx.shadowColor = '#00d4ff';
  ctx.shadowBlur  = 24;
  ctx.fillStyle   = '#00d4ff';
  ctx.beginPath();
  ctx.arc(-size * 0.5, 0, size * 1.2, 0, Math.PI * 2);
  ctx.fill();

  // Arrow triangle — tip at local origin, base extends in −X direction
  ctx.globalAlpha = 0.88 * fadeIn;
  ctx.shadowBlur  = 16;
  ctx.fillStyle   = '#00d4ff';
  ctx.beginPath();
  ctx.moveTo(0,             0);             // tip
  ctx.lineTo(-size * 1.6,  -size * 0.85);  // base top corner
  ctx.lineTo(-size * 1.6,   size * 0.85);  // base bottom corner
  ctx.closePath();
  ctx.fill();

  ctx.restore();
}

// ── ANCHOR LEGEND (bottom-right) ──────────────────────────────────────────────
function renderLegend(W, H) {
  const ITEMS = [
    { hex: '#39ff6a', rgb: '57,255,106', label: 'High Risk', mult: '×10' },
    { hex: '#00d4ff', rgb: '0,212,255',  label: 'Standard',  mult: '×3'  },
    { hex: '#ff1a4e', rgb: '255,26,78',  label: 'Penalty',   mult: '×1'  },
  ];
  const fs   = Math.min(W * 0.029, 21);
  const padX = 16, padY = 13;
  const rowH = fs * 1.75;
  const boxW = Math.min(W * 0.23, 210);
  const boxH = padY * 2 + fs * 1.5 + rowH * 3;
  const bx   = W - boxW - 14;
  const by   = H - boxH - 14;

  // Semi-transparent panel
  ctx.fillStyle   = 'rgba(2,10,26,0.72)';
  ctx.strokeStyle = 'rgba(0,180,255,0.14)';
  ctx.lineWidth   = 1;
  ctx.beginPath();
  if (ctx.roundRect) ctx.roundRect(bx, by, boxW, boxH, 4);
  else               ctx.rect(bx, by, boxW, boxH);
  ctx.fill(); ctx.stroke();

  // "ANCHORS" header
  ctx.textAlign    = 'left';
  ctx.textBaseline = 'top';
  ctx.fillStyle    = 'rgba(0,190,255,0.42)';
  ctx.font         = `${fs * 0.80}px monospace`;
  ctx.fillText('ANCHORS', bx + padX, by + padY);

  ITEMS.forEach((item, i) => {
    const ry = by + padY + fs * 1.5 + i * rowH;
    // Coloured dot with stronger glow
    ctx.shadowColor = item.hex; ctx.shadowBlur = 8;
    ctx.fillStyle   = item.hex;
    ctx.beginPath();
    ctx.arc(bx + padX + fs * 0.55, ry + fs * 0.52, fs * 0.42, 0, Math.PI * 2);
    ctx.fill();
    ctx.shadowBlur = 0;
    // Label
    ctx.fillStyle = 'rgba(165,205,230,0.65)';
    ctx.font      = `${fs}px monospace`;
    ctx.fillText(item.label, bx + padX + fs * 1.45, ry);
    // Multiplier right-aligned, coloured
    ctx.shadowColor = item.hex; ctx.shadowBlur = 5;
    ctx.fillStyle   = item.hex;
    ctx.textAlign   = 'right';
    ctx.fillText(item.mult, bx + boxW - padX, ry);
    ctx.shadowBlur = 0;
    ctx.textAlign  = 'left';
  });
  ctx.textBaseline = 'alphabetic';
}

// ── MUTE BUTTON ───────────────────────────────────────────────────────────────
function renderMuteButton(W, H) {
  const size = Math.min(W * 0.04, 28);
  const bx   = size;
  const by   = H-50;
  MUTE_BTN.x = bx; MUTE_BTN.y = by; MUTE_BTN.size = size;

  ctx.save();

  // Button background
  ctx.fillStyle   = isMuted ? 'rgba(70,0,0,0.70)' : 'rgba(0,15,42,0.60)';
  ctx.strokeStyle = isMuted ? 'rgba(255,60,60,0.55)' : 'rgba(0,160,255,0.35)';
  ctx.lineWidth   = 1;
  if (ctx.roundRect) ctx.roundRect(bx, by, size, size, 5);
  else               ctx.rect(bx, by, size, size);
  ctx.fill(); ctx.stroke();

  // Glow ring
  ctx.shadowColor = isMuted ? '#ff3333' : '#3399ff';
  ctx.shadowBlur  = isMuted ? 10 : 4;

  // Icon
  ctx.textAlign    = 'center';
  ctx.textBaseline = 'middle';
  ctx.fillStyle    = isMuted ? '#ff7777' : '#88ccff';
  ctx.font         = `${Math.floor(size * 0.66)}px serif`;
  ctx.fillText(isMuted ? '🔇' : '🔊', bx + size * 0.5, by + size * 0.5);

  ctx.shadowBlur   = 0;
  ctx.textBaseline = 'alphabetic';
  ctx.restore();
}

// ── INPUT ─────────────────────────────────────────────────────────────────────
function onDown() {
  inputHeld = true;
  if (STATE === 'boot' || STATE === 'gameover') {
    gameOverMusicStop();
    introMusicStop();
    initRun();
    STATE = 'running';
    musicStart();
  }
}
function onUp() { inputHeld = false; }

document.addEventListener('keydown', e => {
  if (e.code === 'Space') { e.preventDefault(); onDown(); return; }
  if (e.code === 'Escape' && STATE !== 'boot') {
    e.preventDefault();
    inputHeld = false;
    musicFadeOut();
    gameOverMusicStop();
    introMusicStop();
    STATE = 'boot';
  }
});
document.addEventListener('keyup',   e => { if (e.code === 'Space') onUp(); });
document.addEventListener('mousedown', e => {
  if (e.button !== 0) return;
  if (isMuteButtonClick(e.clientX, e.clientY)) { setMute(!isMuted); return; }
  onDown();
});
document.addEventListener('mouseup',   e => { if (e.button === 0) onUp(); });
document.addEventListener('touchstart', e => {
  e.preventDefault();
  const t = e.touches[0];
  if (t && isMuteButtonClick(t.clientX, t.clientY)) { setMute(!isMuted); return; }
  onDown();
}, { passive: false });
document.addEventListener('touchend',    e => { e.preventDefault(); if (!e.touches.length) onUp(); }, { passive: false });
document.addEventListener('touchcancel', () => onUp());

// ── GAME LOOP ─────────────────────────────────────────────────────────────────
let prevTs = 0;

function loop(ts) {
  const dt = Math.min((ts - prevTs) / 1000, 0.05);
  prevTs = ts;
  if (dt > 0) {
    if      (STATE === 'running') { runTime += dt; physics(dt); }
    else if (STATE === 'crash'  ) updateCrash(dt);
  }
  render();
  requestAnimationFrame(loop);
}

requestAnimationFrame(ts => { prevTs = ts; requestAnimationFrame(loop); });
