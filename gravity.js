// ============================================================
// Gravity Simulator – N-body with collision merging
// ============================================================

const canvas = document.getElementById('sim');
const ctx = canvas.getContext('2d');

// ---- Constants ----
// G_BASE is tuned below (after the AU/Sun constants) so Earth at 1 AU around
// the Sun (mass 1000) completes one orbit in exactly 1 sim year (= 12 sim
// months = 720 physics-dt units at 1× speed). All other planets get real-world
// orbital periods automatically via Kepler's third law since their distances
// are real AU multiples. Declared with `let` because the value is computed
// once at startup from those constants.
let G_BASE = 0.5;
const SOFTENING = 4;
// Trail length in physics-step samples. Earth at 1 AU records ~1440 samples per
// orbit (720 physics-dt × 2 steps/dt) so 8000 covers ~5 full Earth orbits at
// any time-warp setting (trail fill rate scales with speed, so it doesn't change
// what fraction of an orbit is visible).
const TRAIL_LEN = 8000;
// How many trail points to actually render per body. 1 = draw every sample
// (smoothest, but more line segments). The expensive part was the old per-step
// .shift() — with that gone, rendering every sample is cheap enough.
const TRAIL_RENDER_STRIDE = 1;
const STAR_COUNT = 160;
// Rendering resolution cap. Many displays advertise DPR 2-3, which means the
// canvas internally rasterizes 4-9× as many pixels per frame. Capping at 1.5
// keeps the image sharp without paying the full HD/retina cost.
const RENDER_DPR = Math.min(window.devicePixelRatio || 1, 1.5);
const MERGE_PARTICLE_COUNT = 18;
const VEL_ARROW_SCALE = 12; // pixels per velocity unit

// ---- State ----
let bodies = [];
let stars = [];
let mergeEffects = [];
let rockets = [];
let galaxies = []; // visual-only galaxies, each { x, y, radius, rotation, centerBodyId }
let paused = false;
let showTrails = true;
let showVectors = false;
let starAfterlifeEnabled = true;
let facesEnabled = false;
let speedMul = 1;
let nextPlanetId = 1;
let nextSunId = 1;
let nextAsteroidId = 1;
let nextCometId = 1;
let frameCount = 0;
let lastFpsTime = performance.now();
let fps = 60;
let initialState = null;
let selectedBodyAId = null;
let selectedBodyBId = null;
let simTime = 0;       // accumulated simulation time in ms
let lastLoopTime = 0;  // last frame timestamp for dt calculation
let animTime = 0;      // monotonic time fed to draw functions; frozen on pause
let sizeExaggeration = 1;  // visual-only radius multiplier (does NOT affect mass/physics/collision)
let asteroidTrailsEnabled = false; // optional opt-in: record trails for asteroids too (perf-heavy)
let realisticMode = false; // when on, planets named Mercury/Venus/Earth/.../Pluto + Sun get textured rendering

// ---- Planet color palette ----
const PALETTE = [
  '#b0b0b0','#e8c56d','#4da6ff','#e85d3a','#d4a574',
  '#a78bfa','#f472b6','#34d399','#fbbf24','#f87171',
  '#60a5fa','#c084fc','#fb923c','#2dd4bf','#e879f9'
];

// ---- Named supermassive black holes ----
// Used both at spawn-time (Add Sun modal) and at rename-time.
// Sgr A* is sized so its event-horizon disc matches the realistic solar system
// (Pluto's orbital radius = 39.48 AU). Every other named black hole below is
// expressed as a multiple of Sgr A so the original size ratios are preserved.
const _AU_IN_EARTH_DIAMETERS = 11727.399231907132727670392677483;
const _EARTH_RADIUS_BASE = 3 + Math.cbrt(3) * 2.2;
const _EARTH_DIAMETER_BASE = _EARTH_RADIUS_BASE * 2;
// AU and the named-BH radii are mutable so the admin can rescale the whole
// simulation. NAMED_BHS gets rebuilt by rebuildAuDerived() whenever AU changes.
let _AU_SIM_UNITS = _AU_IN_EARTH_DIAMETERS * _EARTH_DIAMETER_BASE;
let SGR_A_RADIUS  = 39.48 * _AU_SIM_UNITS; // ≈ 5.72 million sim units
let NAMED_BHS = {};
function rebuildNamedBhs() {
  NAMED_BHS = {
    'sagittarius a': { mass: 1e15,   radius: SGR_A_RADIUS                 },
    'ton 618':       { mass: 6.6e13, radius: SGR_A_RADIUS * 27000         },
    // Phoenix A: Sgr A mass, 51 11/39 % bigger than TON 618 (= ×59/39)
    'phoenix a':     { mass: 1e15,   radius: SGR_A_RADIUS * 27000 * 59/39 },
    // M31* — Andromeda's central black hole; 25× Sagittarius A's radius.
    // Mass scales with the real M31*/Sgr A solar-mass ratio (~35×).
    'm31*':          { mass: 3.5e16, radius: SGR_A_RADIUS * 25            }
  };
}
rebuildNamedBhs();

// ---- Orbital tuning ----
// We want Earth (at 1 AU around the Sun = 1000 sim mass) to complete one orbit
// in exactly 1 sim year. 1 sim year = 12 sim months. At 1× speed each real
// second yields 60 physics-dt units AND 1 sim month of simTime, so 1 sim year
// = 720 physics-dt. From Kepler's third law T² = 4π²r³ / (G·M):
//   G = (2π/T)² · r³ / M
// All other planets inherit real-world periods (Mercury 88 d, Mars 687 d, …)
// because their orbital radii are real AU multiples.
const _EARTH_ORBIT_PERIOD_DT = 720;
const _SUN_MASS_SIM = 1000;
function recomputeGBase() {
  G_BASE = ((2 * Math.PI) / _EARTH_ORBIT_PERIOD_DT) ** 2 * Math.pow(_AU_SIM_UNITS, 3) / _SUN_MASS_SIM;
}
recomputeGBase();

// Rescale the whole simulation when the admin changes the AU constant. The
// scale factor k multiplies positions, velocities, radii (so visual size
// keeps up with the new distances), and trail samples. G_BASE is recomputed
// from the new AU so orbital periods stay the same in sim months — orbits
// look the same on screen, just at a different sim-unit scale.
function setAuMultiplier(k) {
  if (!isFinite(k) || k <= 0) return;
  const oldAU = _AU_SIM_UNITS;
  _AU_SIM_UNITS = _AU_SIM_UNITS * k;
  SGR_A_RADIUS  = 39.48 * _AU_SIM_UNITS;
  rebuildNamedBhs();
  recomputeGBase();
  // Velocity has to scale linearly with k (not 1/sqrt) because G also scales
  // as k³ — combined that keeps v_circular = sqrt(G·M/r) proportional to k.
  for (const b of bodies) {
    b.x  *= k; b.y  *= k; if (b.z !== undefined) b.z *= k;
    b.vx *= k; b.vy *= k; if (b.vz !== undefined) b.vz *= k;
    b.radius *= k;
    if (b.trail) {
      for (const p of b.trail) { p.x *= k; p.y *= k; if (p.z !== undefined) p.z *= k; }
    }
  }
  // Camera follow point + zoom — keep the view roughly the same on screen.
  viewX *= k; viewY *= k;
  viewZoom /= k;
  if (typeof render === 'function') {/* nothing to do — next frame redraws */}
}

// Real-world planet/Sun radius ratios. Multiplied by the Sun's sim radius (28)
// to give each default planet its true relative size — Earth ends up ≈ 0.26
// sim units (kept visible at zoom-out by the min-screen-radius logic in
// drawBody).
const REAL_PLANET_RADIUS_RATIOS = {
  'Mercury': 2439.7 / 695700,    // 0.003507
  'Venus':   6051.8 / 695700,    // 0.008700
  'Earth':   6371.0 / 695700,    // 0.009158
  'Mars':    3389.5 / 695700,    // 0.004872
  'Jupiter': 69911  / 695700,    // 0.10049
  'Saturn':  58232  / 695700,    // 0.08370
  'Uranus':  25362  / 695700,    // 0.03646
  'Neptune': 24622  / 695700,    // 0.03539
  'Pluto':   1188.3 / 695700     // 0.001708
};

// ---- Resize ----
function resize() {
  const newW = canvas.clientWidth, newH = canvas.clientHeight;
  if (newW === 0 || newH === 0) return;
  canvas.width = newW * RENDER_DPR;
  canvas.height = newH * RENDER_DPR;
  ctx.setTransform(RENDER_DPR, 0, 0, RENDER_DPR, 0, 0);
}
// Use ResizeObserver for reliable post-layout resize
const resizeObserver = new ResizeObserver(() => resize());
resizeObserver.observe(canvas);
resize();

// ---- Star field ----
function initStars() {
  stars = [];
  for (let i = 0; i < STAR_COUNT; i++) {
    stars.push({
      x: Math.random(), y: Math.random(),
      r: Math.random() * 1.2 + 0.3,
      phase: Math.random() * Math.PI * 2,
      speed: Math.random() * 0.02 + 0.005
    });
  }
}
initStars();

// ---- Default bodies ----
function createDefaultBodies() {
  const w = canvas.clientWidth, h = canvas.clientHeight;
  const cx = w / 2, cy = h / 2;
  nextPlanetId = 1;
  nextSunId = 2; // first sun is id 1
  bodies = [];

  // Sun
  bodies.push({
    id: 'sun-1', name: 'Sun', isSun: true,
    x: cx, y: cy, vx: 0, vy: 0,
    mass: 1000, radius: 28,
    color: getStarColor(1000), trail: [], velMul: 1,
    createdAtSim: simTime
  });

  // Earth sits at exactly 1 AU = 11,727.399231907132727670392677483 × Earth's
  // (reference) diameter away from the Sun. Other planet distances follow real
  // AU multiples. Planet MASSES now use real Sun:planet ratios — Sun = 1000
  // sim units, so e.g. Earth = 1000 / 333000 ≈ 3.0e-3. The AU constant is
  // anchored to a fixed reference Earth diameter (mass-3 radius) so distances
  // don't shrink alongside the real-ratio masses.
  const AU_IN_EARTH_DIAMETERS = 11727.399231907132727670392677483;
  const EARTH_RADIUS_REF = 3 + Math.cbrt(3) * 2.2;
  const AU = AU_IN_EARTH_DIAMETERS * EARTH_RADIUS_REF * 2;
  // Sun:planet mass ratios (IAU values, rounded). Sun mass = 1000 sim units.
  const SUN_MASS = 1000;
  const planets = [
    { name: 'Mercury', dist: AU * 0.387, mass: SUN_MASS / 6_023_600,   color: '#b0b0b0' }, // 1:6.02M
    { name: 'Venus',   dist: AU * 0.723, mass: SUN_MASS / 408_524,     color: '#e8c56d' }, // 1:408k
    { name: 'Earth',   dist: AU,         mass: SUN_MASS / 333_000,     color: '#4da6ff' }, // 1:333k
    { name: 'Mars',    dist: AU * 1.524, mass: SUN_MASS / 3_098_710,   color: '#e85d3a' }, // 1:3.1M
    { name: 'Jupiter', dist: AU * 5.203, mass: SUN_MASS / 1047.35,     color: '#d4a574' }, // 1:1047
    { name: 'Saturn',  dist: AU * 9.537, mass: SUN_MASS / 3498.5,      color: '#e8d090' }, // 1:3499
    { name: 'Uranus',  dist: AU * 19.19, mass: SUN_MASS / 22_903,      color: '#a8dde0' }, // 1:22.9k
    { name: 'Neptune', dist: AU * 30.07, mass: SUN_MASS / 19_412,      color: '#3158d4' }, // 1:19.4k
    { name: 'Pluto',   dist: AU * 39.48, mass: SUN_MASS / 145_000_000, color: '#a89080' }  // 1:145M
  ];

  for (const p of planets) {
    const angle = Math.random() * Math.PI * 2;
    const orbitalV = Math.sqrt(G_BASE * 1000 / p.dist);
    const planet = {
      id: 'planet-' + (nextPlanetId++),
      name: p.name, isSun: false,
      x: cx + Math.cos(angle) * p.dist,
      y: cy + Math.sin(angle) * p.dist,
      vx: -Math.sin(angle) * orbitalV,
      vy: Math.cos(angle) * orbitalV,
      mass: p.mass,
      // Real Sun:planet radius ratio × Sun's sim radius. Falls back to the
      // mass-based formula for any planet name not in the lookup.
      radius: REAL_PLANET_RADIUS_RATIOS[p.name] != null
        ? 28 * REAL_PLANET_RADIUS_RATIOS[p.name]
        : 3 + Math.cbrt(p.mass) * 2.2,
      color: p.color, trail: [],
      velMul: 1
    };
    bodies.push(planet);
    applyEarthFeatures(planet);
  }
}

function deepCopy(arr) {
  return arr.map(b => ({ ...b, trail: [] }));
}

let needsInit = true;

// ---- Physics ----
function computeAccel(bodies) {
  const n = bodies.length;
  const ax = new Float64Array(n);
  const ay = new Float64Array(n);
  const az = new Float64Array(n);
  for (let i = 0; i < n; i++) {
    const bi = bodies[i];
    const zi = bi.z || 0;
    const biAst = bi.isAsteroid;
    const biComet = bi.isComet;
    for (let j = i + 1; j < n; j++) {
      const bj = bodies[j];
      // Tiny-body pairs (asteroid↔asteroid, comet↔comet, comet↔asteroid) are
      // skipped — both bodies are essentially massless, so the mutual pull is
      // unobservable and dropping these pairs takes the inner loop from O(N²)
      // back to O(N · planets+suns). With 500 asteroids that's a ~25× speedup.
      const bjAst = bj.isAsteroid, bjComet = bj.isComet;
      if ((biAst || biComet) && (bjAst || bjComet)) continue;
      const dx = bj.x - bi.x;
      const dy = bj.y - bi.y;
      const dz = (bj.z || 0) - zi;
      const distSq = dx * dx + dy * dy + dz * dz + SOFTENING * SOFTENING;
      const dist = Math.sqrt(distSq);
      const force = G_BASE / (distSq * dist);
      ax[i] += dx * force * bj.mass;
      ay[i] += dy * force * bj.mass;
      az[i] += dz * force * bj.mass;
      ax[j] -= dx * force * bi.mass;
      ay[j] -= dy * force * bi.mass;
      az[j] -= dz * force * bi.mass;
    }
  }
  return { ax, ay, az };
}

function step(dt) {
  const n = bodies.length;
  if (n === 0) return;

  // Velocity Verlet
  let { ax, ay, az } = computeAccel(bodies);

  // Half-step velocity & full-step position (locked bodies don't move)
  for (let i = 0; i < n; i++) {
    const b = bodies[i];
    if (b.locked) continue;
    if (b.vz === undefined) b.vz = 0;
    if (b.z === undefined) b.z = 0;
    b.vx += ax[i] * dt * 0.5;
    b.vy += ay[i] * dt * 0.5;
    b.vz += az[i] * dt * 0.5;
    b.x += b.vx * dt;
    b.y += b.vy * dt;
    b.z += b.vz * dt;
  }

  // Recompute accel at new positions
  const a2 = computeAccel(bodies);

  // Complete velocity step
  for (let i = 0; i < n; i++) {
    if (bodies[i].locked) continue;
    bodies[i].vx += a2.ax[i] * dt * 0.5;
    bodies[i].vy += a2.ay[i] * dt * 0.5;
    bodies[i].vz += a2.az[i] * dt * 0.5;
  }

  // Record trails (locked bodies aren't moving so we skip them).
  // We push every step but only trim when the array grows past 2× the cap —
  // amortized O(1) per push instead of the O(n) per-step .shift() the loop
  // used to do, which became a major cost at high time-warp where step() runs
  // 100×/frame. Asteroids are skipped by default — hundreds of trails would
  // cost both memory and per-frame stroke time — but can be opted in via
  // the Asteroid Trails toggle.
  for (const b of bodies) {
    if (b.locked) continue;
    if (b.isAsteroid && !asteroidTrailsEnabled) continue;
    b.trail.push({ x: b.x, y: b.y, z: b.z || 0 });
    if (b.trail.length > TRAIL_LEN * 2) {
      b.trail = b.trail.slice(b.trail.length - TRAIL_LEN);
    }
  }

  // Collision detection & merging
  checkCollisions();
}

function checkCollisions() {
  const toRemove = new Set();
  for (let i = 0; i < bodies.length; i++) {
    if (toRemove.has(i)) continue;
    const biAst = bodies[i].isAsteroid || bodies[i].isComet;
    for (let j = i + 1; j < bodies.length; j++) {
      if (toRemove.has(j)) continue;
      // Same optimisation as in computeAccel — drop tiny-body pair checks
      // (asteroid↔asteroid, comet↔comet, comet↔asteroid). They dominated
      // the per-step cost and have no visible effect.
      if (biAst && (bodies[j].isAsteroid || bodies[j].isComet)) continue;
      const dx = bodies[j].x - bodies[i].x;
      const dy = bodies[j].y - bodies[i].y;
      const dz = (bodies[j].z || 0) - (bodies[i].z || 0);
      const dist = Math.sqrt(dx * dx + dy * dy + dz * dz);
      const r_i = getEffectiveRadius(bodies[i]);
      const r_j = getEffectiveRadius(bodies[j]);
      const minDist = r_i + r_j;
      if (dist < minDist) {
        // Merge: priority for "keep" is black-hole > locked > more massive
        const bi = bodies[i], bj = bodies[j];
        const iBH = bi.stellarPhase === 'black-hole' || bi.stellarPhase === 'evaporating';
        const jBH = bj.stellarPhase === 'black-hole' || bj.stellarPhase === 'evaporating';
        let keep, lose;
        if (iBH !== jBH) { keep = iBH ? i : j; lose = iBH ? j : i; }
        else if (bi.locked !== bj.locked) { keep = bi.locked ? i : j; lose = bi.locked ? j : i; }
        else if (bi.mass >= bj.mass) { keep = i; lose = j; }
        else { keep = j; lose = i; }
        const a = bodies[keep], b = bodies[lose];

        // Black hole capture: absorb into accretion ring
        if (a.stellarPhase === 'black-hole' || a.stellarPhase === 'evaporating') {
          if (!a.accretionRing) a.accretionRing = [];
          const angle = Math.atan2(b.y - a.y, b.x - a.x);
          const orbitR = a.radius * (1.5 + Math.random() * 2.5);
          const speed = 0.08 + Math.random() * 0.1;
          a.accretionRing.push({
            angle: angle, orbitR: orbitR, speed: speed,
            color: b.color || '#ff8844', size: Math.min(8, 3 + b.mass * 0.5),
            life: 1
          });
          a.mass += b.mass;
          a.radius = 12 + Math.cbrt(a.mass / 1000) * 3;
          toRemove.add(lose);
          continue;
        }

        const totalMass = a.mass + b.mass;

        // Locked bodies stay exactly where they are; otherwise mass-weighted blend
        if (!a.locked) {
          a.x = (a.x * a.mass + b.x * b.mass) / totalMass;
          a.y = (a.y * a.mass + b.y * b.mass) / totalMass;
          a.z = ((a.z || 0) * a.mass + (b.z || 0) * b.mass) / totalMass;
          a.vx = (a.vx * a.mass + b.vx * b.mass) / totalMass;
          a.vy = (a.vy * a.mass + b.vy * b.mass) / totalMass;
          a.vz = ((a.vz || 0) * a.mass + (b.vz || 0) * b.mass) / totalMass;
        }
        a.mass = totalMass;
        // Dwarf star crossing the ignition threshold becomes a real star
        if (!a.isSun && a.mass > 79) {
          a.isSun = true;
          a.stellarPhase = 'main-sequence';
          a.createdAtSim = simTime;
          a.radius = 28 + Math.cbrt(a.mass / 1000) * 4;
          triggerMergeFlash();
        } else {
          a.radius = a.isSun ? 28 + Math.cbrt(a.mass / 1000) * 4 : 3 + Math.cbrt(a.mass) * 2.2;
        }
        // Restate color from mass (suns follow the red→blue mass gradient)
        if (a.isSun) a.color = getStarColor(a.mass);

        // Spawn merge effect
        spawnMergeEffect((a.x + b.x) / 2, (a.y + b.y) / 2, a.color);

        toRemove.add(lose);
      }
    }
  }

  if (toRemove.size > 0) {
    const removed = [...toRemove].sort((a, b) => b - a);
    for (const idx of removed) bodies.splice(idx, 1);
    buildControls();

    // Flash
    const flash = document.getElementById('merge-flash');
    flash.classList.add('active');
    setTimeout(() => flash.classList.remove('active'), 150);
  }
}

// Capture nearby objects into black hole accretion ring
function checkBlackHoleCapture() {
  const blackHoles = bodies.filter(b => b.isSun && (b.stellarPhase === 'black-hole' || b.stellarPhase === 'evaporating'));
  if (blackHoles.length === 0) return;
  const toRemove = new Set();
  for (const bh of blackHoles) {
    const captureR = bh.radius * 5;
    for (let i = 0; i < bodies.length; i++) {
      if (bodies[i] === bh || toRemove.has(i)) continue;
      if (bodies[i].stellarPhase === 'black-hole' || bodies[i].stellarPhase === 'evaporating') continue;
      if (bodies[i].locked) continue; // anchored bodies resist capture
      const b = bodies[i];
      const dx = b.x - bh.x, dy = b.y - bh.y;
      const dz = (b.z || 0) - (bh.z || 0);
      const dist = Math.sqrt(dx * dx + dy * dy + dz * dz);
      if (dist < captureR && dist > bh.radius) {
        if (!bh.accretionRing) bh.accretionRing = [];
        const angle = Math.atan2(dy, dx);
        const orbitR = dist;
        const speed = 0.06 + Math.random() * 0.1;
        bh.accretionRing.push({
          angle: angle, orbitR: orbitR, speed: speed,
          color: b.color || '#ff8844', size: Math.min(8, 3 + b.mass * 0.5),
          life: 1
        });
        bh.mass += b.mass;
        bh.radius = 12 + Math.cbrt(bh.mass / 1000) * 3;
        toRemove.add(i);
      }
    }
  }
  if (toRemove.size > 0) {
    const removed = [...toRemove].sort((a, b) => b - a);
    for (const idx of removed) bodies.splice(idx, 1);
    buildControls();
  }
}

function spawnMergeEffect(x, y, color) {
  const particles = [];
  for (let i = 0; i < MERGE_PARTICLE_COUNT; i++) {
    const angle = (Math.PI * 2 * i) / MERGE_PARTICLE_COUNT;
    const speed = Math.random() * 3 + 1.5;
    particles.push({
      x, y,
      vx: Math.cos(angle) * speed,
      vy: Math.sin(angle) * speed,
      life: 1
    });
  }
  mergeEffects.push({ particles, color, age: 0 });
}

// ---- Earth-like planets (named "earth", "terra", or "gaia") ----
const EARTH_NAMES = new Set(['earth', 'terra', 'gaia']);

function isSaturnLike(planet) {
  if (!planet || planet.isSun) return false;
  const name = (planet.name || '').trim().toLowerCase();
  return name === 'saturn';
}

// Naming a planet "J1407b" gives it the same ring system as Saturn, but
// 200× larger — matching real exoplanet 1SWASP J1407b's hypothesized rings.
function isJ1407bLike(planet) {
  if (!planet || planet.isSun) return false;
  const name = (planet.name || '').trim().toLowerCase();
  return name === 'j1407b';
}

// Naming a planet "ROXs 42Bb" makes it render and collide at 2.5× Jupiter's
// nominal radius, matching the real exoplanet's measured size.
function isRoxsLike(planet) {
  if (!planet || planet.isSun) return false;
  const name = (planet.name || '').trim().toLowerCase();
  return name === 'roxs 42bb';
}

// Naming a planet "HD 100546b" makes it 7× Jupiter's nominal radius,
// matching that real protoplanet's measured size.
function isHD100546bLike(planet) {
  if (!planet || planet.isSun) return false;
  const name = (planet.name || '').trim().toLowerCase();
  return name === 'hd 100546b';
}

// The visible/collision radius for a planet body, applying any name-based
// size overrides. (`JUPITER_RADIUS` is defined further down — JS hoists the
// constant declaration but its value is `undefined` until that line runs.
// In practice this helper is only called at draw/physics time, well after
// module load, so the constant is fully resolved.)
function planetDisplayRadius(b) {
  if (isRoxsLike(b))      return JUPITER_RADIUS * 2.5;
  if (isHD100546bLike(b)) return JUPITER_RADIUS * 7;
  return b.radius;
}

// Pick the ring-scale multiplier: 1 for Saturn, 200 for J1407b, 0 otherwise.
function ringScaleFor(planet) {
  if (isSaturnLike(planet)) return 1;
  if (isJ1407bLike(planet)) return 200;
  return 0;
}

// J1407b ring pattern: many thin grey concentric bands separated by clear
// gaps, modelled on the 1SWASP J1407b artist's-rendering shape.
// Each entry is [fracStart, fracEnd, alpha] across the inner→outer disc.
const J1407B_BANDS = [
  [0.00, 0.04, 0.55],
  [0.05, 0.08, 0.78],
  [0.09, 0.11, 0.90],
  [0.13, 0.16, 0.60],
  [0.17, 0.20, 0.85],
  [0.22, 0.25, 0.65],
  [0.27, 0.30, 0.92],
  [0.32, 0.34, 0.45],
  [0.36, 0.39, 0.78],
  [0.41, 0.44, 0.68],
  [0.46, 0.49, 0.88],
  [0.51, 0.54, 0.55],
  [0.56, 0.59, 0.72],
  [0.62, 0.65, 0.50],
  [0.67, 0.70, 0.62],
  [0.72, 0.75, 0.42],
  [0.77, 0.80, 0.55],
  [0.82, 0.85, 0.35],
  [0.87, 0.90, 0.45],
  [0.93, 0.96, 0.25]
];

// Mix of near-black, tan, and brown — cycled across the bands so adjacent
// rings contrast and the whole disc reads as banded earth tones.
const J1407B_COLORS = [
  '30, 22, 18',    // near-black
  '170,140,100',   // tan
  '95, 70, 48',    // brown
  '50, 38, 30',    // dark brown
  '155,125, 88',   // muted tan
  '70, 50, 35'     // brown
];

function drawJ1407bRings(b, backHalf) {
  const scale = 200;
  // Inner edge pushed well out from the planet so the rings can never
  // overlap the planet's body. Also leaves a clean dark central gap.
  const innerR = b.radius * 5 * scale;
  const outerR = b.radius * 28 * scale;
  const tilt = 0.22;
  ctx.save();
  for (let i = 0; i < J1407B_BANDS.length; i++) {
    const [s, e, a] = J1407B_BANDS[i];
    const rMid = innerR + (outerR - innerR) * (s + e) / 2;
    const ry = rMid * tilt;
    const rawWidth = (outerR - innerR) * (e - s);
    // Stroke width is uniform but the ellipse is flattened, so a width
    // exceeding `ry` causes the top of the band to sweep through the
    // planet area. Cap at 0.8 × ry to keep all bands clear of the centre.
    const lineW = Math.min(rawWidth, ry * 0.8);
    ctx.strokeStyle = `rgba(${J1407B_COLORS[i % J1407B_COLORS.length]},${a})`;
    ctx.lineWidth = lineW;
    ctx.beginPath();
    ctx.ellipse(b.x, b.y, rMid, ry, 0,
      backHalf ? Math.PI : 0,
      backHalf ? 2 * Math.PI : Math.PI);
    ctx.stroke();
  }
  ctx.restore();
}

function isJupiterLike(planet) {
  if (!planet || planet.isSun) return false;
  const name = (planet.name || '').trim().toLowerCase();
  return name === 'jupiter';
}

function isPlutoLike(planet) {
  if (!planet || planet.isSun) return false;
  const name = (planet.name || '').trim().toLowerCase();
  return name === 'pluto';
}

// Tombaugh Regio — the light-brown heart-shaped feature on Pluto's surface.
function drawPlutoHeart(b) {
  const r = b.radius;
  ctx.save();
  // Clip to the planet disc so the heart can't overflow
  ctx.beginPath();
  ctx.arc(b.x, b.y, r, 0, Math.PI * 2);
  ctx.clip();
  // Heart center sits slightly south of the planet center
  const hx = b.x;
  const hy = b.y + r * 0.10;
  const s  = r * 0.55; // overall heart size
  ctx.fillStyle = '#8e6843';
  ctx.beginPath();
  // Bottom point
  ctx.moveTo(hx, hy + s * 0.70);
  // Right lobe up to center-top
  ctx.bezierCurveTo(
    hx + s,      hy + s * 0.20,
    hx + s,      hy - s * 0.55,
    hx,          hy - s * 0.20
  );
  // Left lobe back down to bottom
  ctx.bezierCurveTo(
    hx - s,      hy - s * 0.55,
    hx - s,      hy + s * 0.20,
    hx,          hy + s * 0.70
  );
  ctx.closePath();
  ctx.fill();
  ctx.restore();
}

// Nominal Jupiter render radius in this sim: mass 15 → 3 + ∛15·2.2 ≈ 8.43.
const JUPITER_RADIUS = 3 + Math.cbrt(15) * 2.2;

// Betelgeuse animation: a sun named "Betelgeuse" is a Red Super Giant that
// exponentially grows from its natural radius up to a visible disc 700,000×
// the sun's nominal size, over BETELGEUSE_GROW_SEC seconds of sim time.
// The red-super-giant rendering multiplies the disc by (1 + rgFactor·2.5)·10
// = 35 at full expansion, so b.radius itself only needs to reach ~20,000×
// for the visible disc to hit 700,000×.
const BETELGEUSE_GROW_SEC = 15;
const BETELGEUSE_MAX_MUL = 20000;

function isBetelgeuseLike(sun) {
  if (!sun || !sun.isSun) return false;
  const name = (sun.name || '').trim().toLowerCase();
  return name === 'betelgeuse';
}

// A sun named "Rigel" is locked to a 80× nominal-sun radius and cyan color.
// Zooming in on it has a 10 % chance to blind the viewer for 10 real seconds.
const RIGEL_SIZE_MUL = 80;
const RIGEL_COLOR = '#4dd4ff';

function isRigelLike(sun) {
  if (!sun || !sun.isSun) return false;
  const name = (sun.name || '').trim().toLowerCase();
  return name === 'rigel';
}

function updateRigelStars() {
  for (const b of bodies) {
    if (!isRigelLike(b)) continue;
    const baseRadius = 28 + Math.cbrt(b.mass / 1000) * 4;
    b.radius = baseRadius * RIGEL_SIZE_MUL;
    b.color = RIGEL_COLOR;
    // Lock the body into the Blue Super Giant phase. Resetting phaseAtSim
    // every frame keeps the 180-s BSG collapse timer from ever triggering,
    // so Rigel stays in BSG form forever.
    b.stellarPhase = 'blue-super-giant';
    b.phaseAtSim = simTime;
  }
}

// Naming a star "2MASS J0523-1403" shrinks it to 8.6 % of a normal sun's
// nominal radius — matching the real ultracool dwarf, the smallest known star.
const SMALLSTAR_SIZE_MUL = 0.086;
function is2MASSJ05231403Like(sun) {
  if (!sun || !sun.isSun) return false;
  const name = (sun.name || '').trim().toLowerCase();
  return name === '2mass j0523-1403';
}
function updateSmallStars() {
  for (const b of bodies) {
    if (!is2MASSJ05231403Like(b)) continue;
    const baseRadius = 28 + Math.cbrt(b.mass / 1000) * 4;
    b.radius = baseRadius * SMALLSTAR_SIZE_MUL;
  }
}

// B-type stars: mass 2,000-18,000, radius 2-7× the Sun (linear in mass).
// O-type (mass 16k-100k) takes priority in the overlap so B-types are
// effectively 2k-15999 here.
const SUN_NOMINAL_RADIUS = 28 + Math.cbrt(1000 / 1000) * 4; // = 32

// Spectral-class color stops — linearly interpolated by mass so a star
// gradually shifts hue as its mass changes (no discrete jumps at class
// boundaries).
const SPECTRAL_COLOR_STOPS = [
  [80,     [255, 130,  80]], // M red
  [450,    [255, 200, 130]], // K orange
  [800,    [255, 240, 160]], // G yellow
  [1040,   [255, 245, 214]], // F yellow-white
  [1400,   [230, 236, 255]], // A blueish white
  [2000,   [168, 200, 255]], // B light blue
  [16000,  [130, 170, 255]], // O start
  [100000, [100, 140, 255]]  // O deep blue
];
function getSpectralColor(mass) {
  const s = SPECTRAL_COLOR_STOPS;
  if (mass <= s[0][0]) return rgbToHex(s[0][1]);
  if (mass >= s[s.length - 1][0]) return rgbToHex(s[s.length - 1][1]);
  for (let i = 0; i < s.length - 1; i++) {
    const m0 = s[i][0], m1 = s[i + 1][0];
    if (mass >= m0 && mass <= m1) {
      const t = (mass - m0) / (m1 - m0);
      const c0 = s[i][1], c1 = s[i + 1][1];
      return rgbToHex([
        Math.round(c0[0] + (c1[0] - c0[0]) * t),
        Math.round(c0[1] + (c1[1] - c0[1]) * t),
        Math.round(c0[2] + (c1[2] - c0[2]) * t)
      ]);
    }
  }
  return rgbToHex(s[0][1]);
}
const B_TYPE_COLOR = '#a8c8ff'; // light blue
function updateBTypeStars() {
  for (const b of bodies) {
    if (!b.isSun) continue;
    const isOType = b.mass >= 16000 && b.mass <= 100000;
    if (isOType) continue;
    if (b.mass < 2000 || b.mass > 18000) continue;
    const t = (b.mass - 2000) / (18000 - 2000);
    const mul = 2 + t * 5; // 2× at low end → 7× at high end
    b.radius = SUN_NOMINAL_RADIUS * mul;
    b.color = getSpectralColor(b.mass);
  }
}

// O-type stars: mass 16,000-100,000, radius 8-16× the Sun (linear in mass).
function updateOTypeStars() {
  for (const b of bodies) {
    if (!b.isSun) continue;
    if (b.mass < 16000 || b.mass > 100000) continue;
    const t = (b.mass - 16000) / (100000 - 16000);
    const mul = 8 + t * 8; // 8× at low end → 16× at high end
    b.radius = SUN_NOMINAL_RADIUS * mul;
    b.color = getSpectralColor(b.mass);
  }
}

// K super giant — temporary stalled-expansion phase. 100-150× the Sun's
// radius (lerped by mass within Path B's 501-2500 range), orange.
const K_SUPER_COLOR = '#ff9a45';
function updateKSuperGiantStars() {
  for (const b of bodies) {
    if (!b.isSun || b.stellarPhase !== 'k-super-giant') continue;
    const mClamped = Math.min(2500, Math.max(501, b.mass));
    const t = (mClamped - 501) / (2500 - 501);
    const mul = 100 + t * 50; // 100× at low end → 150× at high end
    b.radius = SUN_NOMINAL_RADIUS * mul;
    b.color = K_SUPER_COLOR;
  }
}

// M-type stars: mass 80-600, radius 0.08-0.7× the Sun, red dwarfs.
// K-type wins the 450-600 overlap so M is effectively 80-449.
function updateMTypeStars() {
  for (const b of bodies) {
    if (!b.isSun) continue;
    const isOType = b.mass >= 16000 && b.mass <= 100000;
    const isBType = !isOType && b.mass >= 2000 && b.mass <= 18000;
    const isAType = !isOType && !isBType && b.mass >= 1400 && b.mass <= 2100;
    const isFType = !isOType && !isBType && !isAType && b.mass >= 1040 && b.mass <= 1400;
    const isGType = !isOType && !isBType && !isAType && !isFType && b.mass >= 800 && b.mass <= 1400;
    const isKType = !isOType && !isBType && !isAType && !isFType && !isGType && b.mass >= 450 && b.mass <= 800;
    if (isOType || isBType || isAType || isFType || isGType || isKType) continue;
    if (b.mass < 80 || b.mass > 600) continue;
    const t = (b.mass - 80) / (600 - 80);
    const mul = 0.08 + t * 0.62; // 0.08× at low end → 0.70× at high end
    b.radius = SUN_NOMINAL_RADIUS * mul;
    b.color = getSpectralColor(b.mass);
  }
}

// K-type stars: mass 450-800, radius 0.7-0.96× the Sun, orange.
// G-type wins the 800 overlap so K is effectively 450-799.
function updateKTypeStars() {
  for (const b of bodies) {
    if (!b.isSun) continue;
    const isOType = b.mass >= 16000 && b.mass <= 100000;
    const isBType = !isOType && b.mass >= 2000 && b.mass <= 18000;
    const isAType = !isOType && !isBType && b.mass >= 1400 && b.mass <= 2100;
    const isFType = !isOType && !isBType && !isAType && b.mass >= 1040 && b.mass <= 1400;
    const isGType = !isOType && !isBType && !isAType && !isFType && b.mass >= 800 && b.mass <= 1400;
    if (isOType || isBType || isAType || isFType || isGType) continue;
    if (b.mass < 450 || b.mass > 800) continue;
    const t = (b.mass - 450) / (800 - 450);
    const mul = 0.7 + t * 0.26; // 0.7× at low end → 0.96× at high end
    b.radius = SUN_NOMINAL_RADIUS * mul;
    b.color = getSpectralColor(b.mass);
  }
}

// G-type stars: mass 800-1,400, radius 0.8-1.4× the Sun, warm yellow.
// F-type wins in the 1,040-1,400 overlap, so G is effectively 800-1,039.
const G_TYPE_COLOR = '#fff0a0';
function updateGTypeStars() {
  for (const b of bodies) {
    if (!b.isSun) continue;
    const isOType = b.mass >= 16000 && b.mass <= 100000;
    const isBType = !isOType && b.mass >= 2000 && b.mass <= 18000;
    const isAType = !isOType && !isBType && b.mass >= 1400 && b.mass <= 2100;
    const isFType = !isOType && !isBType && !isAType && b.mass >= 1040 && b.mass <= 1400;
    if (isOType || isBType || isAType || isFType) continue;
    if (b.mass < 800 || b.mass > 1400) continue;
    const t = (b.mass - 800) / (1400 - 800);
    const mul = 0.8 + t * 0.6; // 0.8× at low end → 1.4× at high end
    b.radius = SUN_NOMINAL_RADIUS * mul;
    b.color = getSpectralColor(b.mass);
  }
}

// F-type stars: mass 1,040-1,400, radius 1.15-1.4× the Sun, yellow-white
// color. A-type wins in the overlap at mass 1,400.
const F_TYPE_COLOR = '#fff5d6';
function updateFTypeStars() {
  for (const b of bodies) {
    if (!b.isSun) continue;
    const isOType = b.mass >= 16000 && b.mass <= 100000;
    const isBType = !isOType && b.mass >= 2000 && b.mass <= 18000;
    const isAType = !isOType && !isBType && b.mass >= 1400 && b.mass <= 2100;
    if (isOType || isBType || isAType) continue;
    if (b.mass < 1040 || b.mass > 1400) continue;
    const t = (b.mass - 1040) / (1400 - 1040);
    const mul = 1.15 + t * 0.25; // 1.15× at low end → 1.4× at high end
    b.radius = SUN_NOMINAL_RADIUS * mul;
    b.color = getSpectralColor(b.mass);
  }
}

// A-type stars: mass 1,400-2,100, radius 1.4-1.9× the Sun, white / blueish-
// white color. B-type wins in the 2,000-2,100 overlap.
const A_TYPE_COLOR = '#e6ecff';
function updateATypeStars() {
  for (const b of bodies) {
    if (!b.isSun) continue;
    const isOType = b.mass >= 16000 && b.mass <= 100000;
    const isBType = !isOType && b.mass >= 2000 && b.mass <= 18000;
    if (isOType || isBType) continue;
    if (b.mass < 1400 || b.mass > 2100) continue;
    const t = (b.mass - 1400) / (2100 - 1400);
    const mul = 1.4 + t * 0.5; // 1.4× at low end → 1.9× at high end
    b.radius = SUN_NOMINAL_RADIUS * mul;
    b.color = getSpectralColor(b.mass);
  }
}

// Blind-the-viewer state — uses wall-clock so the timer can't be evaded by
// pausing the sim.
let blindUntilMs = 0;
function isBlind() { return performance.now() < blindUntilMs; }
function startBlind(ms) { blindUntilMs = Math.max(blindUntilMs, performance.now() + ms); }

function checkRigelBlind() {
  if (isBlind()) return;
  const w = canvas.clientWidth, h = canvas.clientHeight;
  const screenMin = Math.min(w, h);
  for (const b of bodies) {
    if (!isRigelLike(b)) continue;
    // Is Rigel's centre roughly on-screen?
    const sx = (b.x - viewX) * viewZoom + w / 2;
    const sy = (b.y - viewY) * viewZoom + h / 2;
    const onScreen = sx > -screenMin && sx < w + screenMin && sy > -screenMin && sy < h + screenMin;
    // Are we zoomed in enough that Rigel takes up most of the view?
    const screenR = b.radius * viewZoom;
    const zoomedIn = screenR > screenMin * 0.4;
    if (zoomedIn && onScreen) {
      // Edge-trigger: only roll on the transition from "not zoomed in" to "zoomed in"
      if (!b._rigelZoomFlag) {
        b._rigelZoomFlag = true;
        if (Math.random() < 0.1) startBlind(10000);
      }
    } else {
      b._rigelZoomFlag = false;
    }
  }
}

function drawBlindOverlay() {
  if (!isBlind()) return;
  const remaining = blindUntilMs - performance.now();
  // Fade in over 150 ms, fade out over the last 800 ms
  const fadeIn  = Math.min(1, (10000 - remaining) / 150);
  const fadeOut = Math.min(1, remaining / 800);
  const alpha = Math.max(0, Math.min(fadeIn, fadeOut, 1));
  ctx.save();
  ctx.fillStyle = `rgba(255,255,255,${alpha})`;
  ctx.fillRect(0, 0, canvas.clientWidth, canvas.clientHeight);
  ctx.restore();
}

const BETELGEUSE_COLOR = '#d94032';

function updateBetelgeuseRadii() {
  // Defensive: don't advance Betelgeuse state when time is stopped, even
  // if some caller invokes us outside the !paused gate.
  if (paused) return;
  for (const b of bodies) {
    if (!isBetelgeuseLike(b)) continue;
    if (b.betelgeuseStartSim == null) b.betelgeuseStartSim = simTime;
    // Lock the body into the Red Super Giant phase. We reset redGiantAtSim
    // to 10 s in the past so rgFactor is permanently 1 (full expansion) and
    // the natural 178-s collapse timer can never reach its trigger.
    b.stellarPhase = 'red-giant';
    b.redSuperGiant = true;
    b.redGiantAtSim = simTime - 10000;
    const elapsed = (simTime - b.betelgeuseStartSim) / 1000;
    const t = Math.min(elapsed / BETELGEUSE_GROW_SEC, 1);
    // Exponential growth: mul goes 1 → BETELGEUSE_MAX_MUL over the duration
    const mul = Math.pow(BETELGEUSE_MAX_MUL, t);
    const baseRadius = 28 + Math.cbrt(b.mass / 1000) * 4;
    b.radius = baseRadius * mul;
    b.color = BETELGEUSE_COLOR;
  }
}

// =====================================================================
// Realistic-mode renderers
// =====================================================================
// When `realisticMode` is on, any body named after a real solar-system
// object gets a textured, photo-inspired rendering instead of the default
// cartoon-with-face look. Features (craters, swirls, etc.) are randomized
// once and cached on the body so frame-to-frame they don't twinkle.

const REALISTIC_NAMES = new Set([
  'sun', 'mercury', 'venus', 'earth', 'mars',
  'jupiter', 'saturn', 'uranus', 'neptune', 'pluto'
]);

function _seedFeatures(b, name) {
  if (b._realFeatName === name && b._realFeat) return b._realFeat;
  b._realFeatName = name;
  const rng = () => Math.random();
  const f = {};
  if (name === 'mercury') {
    f.craters = [];
    for (let i = 0; i < 24; i++) f.craters.push({
      ang: rng() * Math.PI * 2,
      dist: rng() * 0.88,
      size: 0.04 + rng() * 0.10,
      darkness: 0.18 + rng() * 0.28
    });
  } else if (name === 'venus') {
    f.swirls = [];
    for (let i = 0; i < 7; i++) f.swirls.push({
      yFrac: -0.7 + (i / 6) * 1.4,
      phase: rng() * Math.PI * 2,
      amp: 0.06 + rng() * 0.10,
      thick: 0.08 + rng() * 0.10
    });
  } else if (name === 'mars') {
    f.patches = [];
    for (let i = 0; i < 12; i++) f.patches.push({
      ang: rng() * Math.PI * 2,
      dist: rng() * 0.7,
      size: 0.10 + rng() * 0.16,
      darkness: 0.12 + rng() * 0.22
    });
  } else if (name === 'jupiter') {
    f.bands = [
      { y: -0.85, w: 0.10, c: '#cdb088' },
      { y: -0.65, w: 0.14, c: '#a8845c' },
      { y: -0.42, w: 0.16, c: '#e2cda4' },
      { y: -0.18, w: 0.14, c: '#9c7448' },
      { y:  0.08, w: 0.16, c: '#dbc69a' },
      { y:  0.33, w: 0.14, c: '#a8845c' },
      { y:  0.58, w: 0.16, c: '#e2cda4' },
      { y:  0.83, w: 0.10, c: '#8e6840' }
    ];
  } else if (name === 'saturn') {
    f.bands = [
      { y: -0.80, w: 0.16, c: '#e8d090' },
      { y: -0.45, w: 0.20, c: '#d0b070' },
      { y: -0.10, w: 0.20, c: '#e8d090' },
      { y:  0.25, w: 0.20, c: '#c8a868' },
      { y:  0.60, w: 0.18, c: '#dec078' },
      { y:  0.88, w: 0.10, c: '#a88858' }
    ];
  } else if (name === 'uranus') {
    f.bands = [
      { y: -0.55, w: 0.20, c: '#bbe4e1' },
      { y:  0.15, w: 0.30, c: '#9ed3ce' }
    ];
  } else if (name === 'neptune') {
    f.wisps = [];
    for (let i = 0; i < 7; i++) f.wisps.push({
      xFrac: -0.7 + rng() * 1.4,
      yFrac: -0.6 + rng() * 1.2,
      w: 0.25 + rng() * 0.30,
      thick: 0.04 + rng() * 0.05,
      opacity: 0.22 + rng() * 0.28
    });
    f.spot = { x: -0.05, y: 0.10, w: 0.32, h: 0.16 };
  } else if (name === 'sun') {
    // Cumulus-cloud mottling: a mix of broad shadow swirls and bright
    // highlight patches at random positions. Sizes are stratified into two
    // layers so the eye reads "big puffy shapes overlaid with fine granules".
    f.cells = [];
    // Broad cells
    for (let i = 0; i < 22; i++) f.cells.push({
      ang: rng() * Math.PI * 2,
      dist: rng() * 0.92,
      size: 0.18 + rng() * 0.22,
      type: rng() < 0.55 ? 'dark' : 'bright',
      intensity: 0.18 + rng() * 0.30
    });
    // Fine granules
    for (let i = 0; i < 50; i++) f.cells.push({
      ang: rng() * Math.PI * 2,
      dist: rng() * 0.95,
      size: 0.04 + rng() * 0.10,
      type: rng() < 0.45 ? 'dark' : 'bright',
      intensity: 0.15 + rng() * 0.35
    });
  }
  b._realFeat = f;
  return f;
}

function _clipDisc(b, r) {
  ctx.beginPath();
  ctx.arc(b.x, b.y, r, 0, Math.PI * 2);
  ctx.clip();
}

function _limbShade(b, r) {
  const g = ctx.createRadialGradient(b.x - r * 0.4, b.y - r * 0.4, 0, b.x, b.y, r);
  g.addColorStop(0,   'rgba(255,255,255,0.28)');
  g.addColorStop(0.7, 'rgba(255,255,255,0)');
  g.addColorStop(1,   'rgba(0,0,0,0.55)');
  ctx.fillStyle = g;
  ctx.beginPath();
  ctx.arc(b.x, b.y, r, 0, Math.PI * 2);
  ctx.fill();
}

function drawRealisticMercury(b, r) {
  const f = _seedFeatures(b, 'mercury');
  ctx.save();
  _clipDisc(b, r);
  const g = ctx.createRadialGradient(b.x - r*0.3, b.y - r*0.3, 0, b.x, b.y, r);
  g.addColorStop(0, '#cdb594'); g.addColorStop(0.5, '#9a8870'); g.addColorStop(1, '#5b4d3a');
  ctx.fillStyle = g; ctx.fillRect(b.x - r, b.y - r, r * 2, r * 2);
  for (const c of f.craters) {
    const cx = b.x + Math.cos(c.ang) * r * c.dist;
    const cy = b.y + Math.sin(c.ang) * r * c.dist;
    const cr = r * c.size;
    ctx.fillStyle = `rgba(40,30,20,${c.darkness})`;
    ctx.beginPath(); ctx.arc(cx, cy, cr, 0, Math.PI*2); ctx.fill();
    ctx.fillStyle = 'rgba(220,200,170,0.25)';
    ctx.beginPath(); ctx.arc(cx - cr * 0.25, cy - cr * 0.3, cr * 0.55, 0, Math.PI*2); ctx.fill();
  }
  ctx.restore();
  _limbShade(b, r);
}

function drawRealisticVenus(b, r) {
  const f = _seedFeatures(b, 'venus');
  ctx.save();
  _clipDisc(b, r);
  const g = ctx.createRadialGradient(b.x - r*0.3, b.y - r*0.3, 0, b.x, b.y, r);
  g.addColorStop(0, '#ffdc8a'); g.addColorStop(0.55, '#e09a48'); g.addColorStop(1, '#7a3a10');
  ctx.fillStyle = g; ctx.fillRect(b.x - r, b.y - r, r * 2, r * 2);
  // Cloud bands as sinuous horizontal strokes
  for (const s of f.swirls) {
    ctx.strokeStyle = `rgba(255, 220, 160, 0.40)`;
    ctx.lineWidth = r * s.thick;
    ctx.lineCap = 'round';
    ctx.beginPath();
    const yC = b.y + r * s.yFrac;
    const xL = b.x - r;
    const xR = b.x + r;
    for (let x = xL; x <= xR; x += r * 0.05) {
      const yy = yC + Math.sin((x - b.x) / r * Math.PI * (s.amp * 14 + 2) + s.phase) * r * s.amp;
      if (x === xL) ctx.moveTo(x, yy); else ctx.lineTo(x, yy);
    }
    ctx.stroke();
  }
  ctx.restore();
  _limbShade(b, r);
}

function drawRealisticEarth(b, r) {
  ctx.save();
  _clipDisc(b, r);
  // Ocean
  const g = ctx.createRadialGradient(b.x - r*0.3, b.y - r*0.3, 0, b.x, b.y, r);
  g.addColorStop(0, '#5fa8e8'); g.addColorStop(0.55, '#1f4f9a'); g.addColorStop(1, '#0a2454');
  ctx.fillStyle = g; ctx.fillRect(b.x - r, b.y - r, r * 2, r * 2);
  // Continents — reuse the procedural continents (applyEarthFeatures) if any,
  // otherwise generate green blobs deterministically.
  if (!b.continents) {
    b.continents = [];
    for (let i = 0; i < 5; i++) {
      b.continents.push({
        angle: Math.random() * Math.PI * 2,
        distFrac: Math.random() * 0.55,
        sizeFrac: 0.20 + Math.random() * 0.16,
        shade: Math.random()
      });
    }
  }
  for (const c of b.continents) {
    const cx = b.x + Math.cos(c.angle) * c.distFrac * r;
    const cy = b.y + Math.sin(c.angle) * c.distFrac * r;
    const cr = c.sizeFrac * r;
    const gShade = Math.round(120 + c.shade * 80);
    ctx.fillStyle = `rgb(40, ${gShade}, 50)`;
    ctx.beginPath(); ctx.arc(cx, cy, cr, 0, Math.PI*2); ctx.fill();
    // Brown coastline
    ctx.strokeStyle = 'rgba(120,90,55,0.5)';
    ctx.lineWidth = r * 0.02;
    ctx.stroke();
  }
  // Cloud wisps
  ctx.fillStyle = 'rgba(255,255,255,0.45)';
  for (let i = 0; i < 4; i++) {
    const cx = b.x + Math.cos(i * 1.7 + 0.4) * r * 0.6;
    const cy = b.y + Math.sin(i * 1.3 + 0.9) * r * 0.55;
    ctx.beginPath();
    ctx.ellipse(cx, cy, r * 0.25, r * 0.08, i * 0.7, 0, Math.PI*2);
    ctx.fill();
  }
  ctx.restore();
  _limbShade(b, r);
}

function drawRealisticMars(b, r) {
  const f = _seedFeatures(b, 'mars');
  ctx.save();
  _clipDisc(b, r);
  const g = ctx.createRadialGradient(b.x - r*0.3, b.y - r*0.3, 0, b.x, b.y, r);
  g.addColorStop(0, '#e08858'); g.addColorStop(0.5, '#b8512a'); g.addColorStop(1, '#5e2010');
  ctx.fillStyle = g; ctx.fillRect(b.x - r, b.y - r, r * 2, r * 2);
  // Dark surface patches
  for (const p of f.patches) {
    const cx = b.x + Math.cos(p.ang) * r * p.dist;
    const cy = b.y + Math.sin(p.ang) * r * p.dist;
    const cr = r * p.size;
    ctx.fillStyle = `rgba(80, 30, 10, ${p.darkness})`;
    ctx.beginPath(); ctx.arc(cx, cy, cr, 0, Math.PI*2); ctx.fill();
  }
  // North polar ice cap
  ctx.fillStyle = 'rgba(255,255,255,0.85)';
  ctx.beginPath();
  ctx.ellipse(b.x, b.y - r * 0.75, r * 0.55, r * 0.20, 0, 0, Math.PI*2);
  ctx.fill();
  ctx.restore();
  _limbShade(b, r);
}

function drawRealisticJupiter(b, r) {
  const f = _seedFeatures(b, 'jupiter');
  ctx.save();
  _clipDisc(b, r);
  // Base cream gradient
  const g = ctx.createRadialGradient(b.x - r*0.3, b.y - r*0.3, 0, b.x, b.y, r);
  g.addColorStop(0, '#f0d8a8'); g.addColorStop(0.6, '#c89858'); g.addColorStop(1, '#604018');
  ctx.fillStyle = g; ctx.fillRect(b.x - r, b.y - r, r * 2, r * 2);
  // Horizontal bands
  for (const band of f.bands) {
    ctx.fillStyle = band.c;
    ctx.globalAlpha = 0.75;
    ctx.fillRect(b.x - r, b.y + r * band.y - r * band.w * 0.5, r * 2, r * band.w);
  }
  ctx.globalAlpha = 1;
  // Great Red Spot
  ctx.fillStyle = '#b04020';
  ctx.beginPath();
  ctx.ellipse(b.x + r * 0.25, b.y + r * 0.25, r * 0.20, r * 0.10, 0, 0, Math.PI*2);
  ctx.fill();
  ctx.restore();
  _limbShade(b, r);
}

function drawRealisticSaturn(b, r) {
  const f = _seedFeatures(b, 'saturn');
  ctx.save();
  _clipDisc(b, r);
  const g = ctx.createRadialGradient(b.x - r*0.3, b.y - r*0.3, 0, b.x, b.y, r);
  g.addColorStop(0, '#f5dca5'); g.addColorStop(0.6, '#c8a058'); g.addColorStop(1, '#604018');
  ctx.fillStyle = g; ctx.fillRect(b.x - r, b.y - r, r * 2, r * 2);
  for (const band of f.bands) {
    ctx.fillStyle = band.c;
    ctx.globalAlpha = 0.6;
    ctx.fillRect(b.x - r, b.y + r * band.y - r * band.w * 0.5, r * 2, r * band.w);
  }
  ctx.globalAlpha = 1;
  ctx.restore();
  _limbShade(b, r);
}

function drawRealisticUranus(b, r) {
  const f = _seedFeatures(b, 'uranus');
  ctx.save();
  _clipDisc(b, r);
  const g = ctx.createRadialGradient(b.x - r*0.3, b.y - r*0.3, 0, b.x, b.y, r);
  g.addColorStop(0, '#cef0ec'); g.addColorStop(0.55, '#7ec7be'); g.addColorStop(1, '#2c5c58');
  ctx.fillStyle = g; ctx.fillRect(b.x - r, b.y - r, r * 2, r * 2);
  for (const band of f.bands) {
    ctx.fillStyle = band.c;
    ctx.globalAlpha = 0.35;
    ctx.fillRect(b.x - r, b.y + r * band.y - r * band.w * 0.5, r * 2, r * band.w);
  }
  ctx.globalAlpha = 1;
  ctx.restore();
  _limbShade(b, r);
}

function drawRealisticNeptune(b, r) {
  const f = _seedFeatures(b, 'neptune');
  ctx.save();
  _clipDisc(b, r);
  const g = ctx.createRadialGradient(b.x - r*0.3, b.y - r*0.3, 0, b.x, b.y, r);
  g.addColorStop(0, '#5a8bff'); g.addColorStop(0.5, '#1f48d8'); g.addColorStop(1, '#08183c');
  ctx.fillStyle = g; ctx.fillRect(b.x - r, b.y - r, r * 2, r * 2);
  // Great Dark Spot
  ctx.fillStyle = 'rgba(10, 20, 60, 0.85)';
  ctx.beginPath();
  ctx.ellipse(b.x + r * f.spot.x, b.y + r * f.spot.y, r * f.spot.w, r * f.spot.h, 0, 0, Math.PI*2);
  ctx.fill();
  // White wisps
  for (const w of f.wisps) {
    const wx = b.x + r * w.xFrac;
    const wy = b.y + r * w.yFrac;
    ctx.fillStyle = `rgba(255,255,255,${w.opacity})`;
    ctx.beginPath();
    ctx.ellipse(wx, wy, r * w.w, r * w.thick, 0, 0, Math.PI*2);
    ctx.fill();
  }
  ctx.restore();
  _limbShade(b, r);
}

function drawRealisticPluto(b, r) {
  ctx.save();
  _clipDisc(b, r);
  const g = ctx.createRadialGradient(b.x - r*0.3, b.y - r*0.3, 0, b.x, b.y, r);
  g.addColorStop(0, '#d8c8b0'); g.addColorStop(0.55, '#8a7a64'); g.addColorStop(1, '#3a2e22');
  ctx.fillStyle = g; ctx.fillRect(b.x - r, b.y - r, r * 2, r * 2);
  // Tombaugh Regio — light tan heart on the lower-right
  ctx.fillStyle = 'rgba(245,225,190,0.85)';
  const hx = b.x + r * 0.15, hy = b.y + r * 0.10, hr = r * 0.45;
  ctx.beginPath();
  ctx.arc(hx - hr * 0.3, hy - hr * 0.15, hr * 0.5, 0, Math.PI * 2);
  ctx.arc(hx + hr * 0.3, hy - hr * 0.15, hr * 0.5, 0, Math.PI * 2);
  ctx.moveTo(hx - hr * 0.55, hy);
  ctx.quadraticCurveTo(hx, hy + hr, hx + hr * 0.55, hy);
  ctx.lineTo(hx - hr * 0.55, hy);
  ctx.fill();
  ctx.restore();
  _limbShade(b, r);
}

// ---- Procedural Sun surface ----
// fBm value-noise texture with a 4-stop hot-plasma colour ramp, ported from
// the user's dad's Three.js SDO-304-Å shader. Generated once and cached so
// we only pay the per-pixel cost on first use.
function _makeValueNoise3D(seed) {
  const hash = (x, y, z) => {
    let h = (x | 0) * 374761393 + (y | 0) * 668265263 + (z | 0) * 1274126177 + seed * 2654435761;
    h ^= h >>> 13;
    h = Math.imul(h, 1274126177);
    h ^= h >>> 16;
    return ((h >>> 0) & 0xFFFFFF) / 0xFFFFFF;
  };
  const smooth = (t) => t * t * (3 - 2 * t);
  return (x, y, z) => {
    const ix = Math.floor(x), iy = Math.floor(y), iz = Math.floor(z);
    const u = smooth(x - ix), v = smooth(y - iy), w = smooth(z - iz);
    const c000 = hash(ix,   iy,   iz);
    const c100 = hash(ix+1, iy,   iz);
    const c010 = hash(ix,   iy+1, iz);
    const c110 = hash(ix+1, iy+1, iz);
    const c001 = hash(ix,   iy,   iz+1);
    const c101 = hash(ix+1, iy,   iz+1);
    const c011 = hash(ix,   iy+1, iz+1);
    const c111 = hash(ix+1, iy+1, iz+1);
    const x00 = c000 + (c100 - c000) * u;
    const x10 = c010 + (c110 - c010) * u;
    const x01 = c001 + (c101 - c001) * u;
    const x11 = c011 + (c111 - c011) * u;
    const y0  = x00  + (x10  - x00)  * v;
    const y1  = x01  + (x11  - x01)  * v;
    return y0 + (y1 - y0) * w;
  };
}

let _sunTextureCanvas = null;
function getSunTextureCanvas() {
  if (_sunTextureCanvas) return _sunTextureCanvas;
  const S = 512;
  const cnv = document.createElement('canvas');
  cnv.width = cnv.height = S;
  const cx = cnv.getContext('2d');
  const n1 = _makeValueNoise3D(7);
  const n2 = _makeValueNoise3D(19);
  const img = cx.createImageData(S, S);
  const data = img.data;
  // Cylindrical x ↔ angle mapping so the texture wraps seamlessly when applied
  // to a sphere (and reads correctly even on the flat 2D disc here).
  for (let y = 0; y < S; y++) {
    const yN = y / S;
    for (let x = 0; x < S; x++) {
      const theta = (x / S) * Math.PI * 2;
      const cx0 = Math.cos(theta), sx0 = Math.sin(theta);
      // fBm — 6 octaves
      let v = 0, amp = 1, freq = 1, total = 0;
      for (let k = 0; k < 6; k++) {
        const f = 2.5 * freq;
        v += amp * n1(cx0 * f, sx0 * f, yN * f * 2.5);
        total += amp;
        amp  *= 0.55;
        freq *= 2;
      }
      let n = v / total;
      // Domain warp — second noise stretches & breaks up the features
      const warp = (n2(cx0 * 4, sx0 * 4, yN * 10) - 0.5) * 0.5;
      n = Math.max(0, Math.min(1, n + warp));
      // 4-stop colour ramp: dark filaments → red-orange → orange-yellow → near white
      let R, G, B;
      if (n < 0.30) {
        const t = n / 0.30;
        R = 150 + t * 105; G = 30  + t * 50;  B = 5;
      } else if (n < 0.62) {
        const t = (n - 0.30) / 0.32;
        R = 255;            G = 80  + t * 80;  B = 5  + t * 25;
      } else if (n < 0.85) {
        const t = (n - 0.62) / 0.23;
        R = 255;            G = 160 + t * 75;  B = 30 + t * 80;
      } else {
        const t = (n - 0.85) / 0.15;
        R = 255;            G = 235 + t * 20;  B = 110 + t * 130;
      }
      const i = (y * S + x) * 4;
      data[i] = R; data[i+1] = G; data[i+2] = B; data[i+3] = 255;
    }
  }
  cx.putImageData(img, 0, 0);
  _sunTextureCanvas = cnv;
  return cnv;
}

function drawRealisticSun(b, t) {
  // Procedural plasma sun: drawImage the cached fBm texture, clipped to the
  // disc, then add limb darkening for a sphere read and an outer halo.
  const r = b.radius;
  ctx.save();
  _clipDisc(b, r);
  const tex = getSunTextureCanvas();
  ctx.drawImage(tex, b.x - r, b.y - r, r * 2, r * 2);
  // Limb darkening — soft black gradient at the rim so the disc reads spherical.
  const dg = ctx.createRadialGradient(b.x, b.y, r * 0.55, b.x, b.y, r);
  dg.addColorStop(0, 'rgba(0,0,0,0)');
  dg.addColorStop(1, 'rgba(0,0,0,0.45)');
  ctx.fillStyle = dg;
  ctx.fillRect(b.x - r, b.y - r, r * 2, r * 2);
  ctx.restore();
  // Bright limb glow outside the disc — the hot edge from the reference photo.
  const lg = ctx.createRadialGradient(b.x, b.y, r * 0.97, b.x, b.y, r * 1.22);
  lg.addColorStop(0, 'rgba(255, 180, 70, 0.55)');
  lg.addColorStop(1, 'rgba(255, 100, 20, 0)');
  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  ctx.fillStyle = lg;
  ctx.beginPath();
  ctx.arc(b.x, b.y, r * 1.22, 0, Math.PI * 2);
  ctx.fill();
  ctx.restore();
}

// Old cumulus-blob implementation, replaced by the procedural texture above.
function drawRealisticSun_OLD(b, t) {
  // Cumulus-textured Sun matching the reference photo: smooth yellow-orange
  // base + many overlapping translucent blobs (some shadow, some highlight)
  // that read as cloud-like granulation. No coronal loops or sunspots —
  // those broke the soft mottled look.
  const r = b.radius;
  const f = _seedFeatures(b, 'sun');
  ctx.save();
  _clipDisc(b, r);
  // Smooth base gradient — bright yellow center, warm orange edge.
  const g = ctx.createRadialGradient(b.x, b.y, r * 0.05, b.x, b.y, r);
  g.addColorStop(0,    '#ffe888');   // bright yellow core
  g.addColorStop(0.45, '#ffb04a');   // orange
  g.addColorStop(0.85, '#ee7820');   // deep orange
  g.addColorStop(1,    '#d8550e');   // warm rim
  ctx.fillStyle = g; ctx.fillRect(b.x - r, b.y - r, r * 2, r * 2);

  // Cumulus mottling — each cached cell is a soft radial gradient blob.
  // Dark cells use normal alpha (deeper orange/red shadows); bright cells
  // use 'lighter' so the yellow highlights glow rather than wash out.
  for (const c of f.cells) {
    const cx = b.x + Math.cos(c.ang) * r * c.dist;
    const cy = b.y + Math.sin(c.ang) * r * c.dist;
    const cr = r * c.size;
    const cg = ctx.createRadialGradient(cx, cy, 0, cx, cy, cr);
    if (c.type === 'dark') {
      cg.addColorStop(0, `rgba(190, 60, 15, ${c.intensity})`);
      cg.addColorStop(1, 'rgba(190, 60, 15, 0)');
      ctx.globalCompositeOperation = 'source-over';
    } else {
      cg.addColorStop(0, `rgba(255, 230, 130, ${c.intensity * 0.75})`);
      cg.addColorStop(1, 'rgba(255, 230, 130, 0)');
      ctx.globalCompositeOperation = 'lighter';
    }
    ctx.fillStyle = cg;
    ctx.beginPath();
    ctx.arc(cx, cy, cr, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.globalCompositeOperation = 'source-over';
  ctx.restore();

  // Soft outer glow — gentle warm halo just past the disc edge.
  const lg = ctx.createRadialGradient(b.x, b.y, r * 0.96, b.x, b.y, r * 1.18);
  lg.addColorStop(0, 'rgba(255, 170, 60, 0.45)');
  lg.addColorStop(1, 'rgba(255, 100, 20, 0)');
  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  ctx.fillStyle = lg;
  ctx.beginPath();
  ctx.arc(b.x, b.y, r * 1.18, 0, Math.PI * 2);
  ctx.fill();
  ctx.restore();
}

function drawRealisticBody(b, t) {
  if (!realisticMode) return false;
  const name = (b.name || '').toLowerCase();
  if (!REALISTIC_NAMES.has(name)) return false;
  const r = b.radius;
  if (name === 'sun') {
    drawRealisticSun(b, t);
    return true;
  }
  // Saturn back-half rings before the disc
  if (name === 'saturn') drawSaturnRings(b, true, 1);
  switch (name) {
    case 'mercury': drawRealisticMercury(b, r); break;
    case 'venus':   drawRealisticVenus(b, r);   break;
    case 'earth':   drawRealisticEarth(b, r);   break;
    case 'mars':    drawRealisticMars(b, r);    break;
    case 'jupiter': drawRealisticJupiter(b, r); break;
    case 'saturn':  drawRealisticSaturn(b, r);  break;
    case 'uranus':  drawRealisticUranus(b, r);  break;
    case 'neptune': drawRealisticNeptune(b, r); break;
    case 'pluto':   drawRealisticPluto(b, r);   break;
  }
  if (name === 'saturn') drawSaturnRings(b, false, 1);
  return true;
}

function toggleRealisticMode() {
  realisticMode = !realisticMode;
  const btn = document.getElementById('btn-realistic');
  if (btn) btn.classList.toggle('active', realisticMode);
}

// The Great Red Spot — a fixed-position oval of stormy reds clipped to the
// planet's disc, on the lower-right hemisphere in our top-down view.
function drawJupiterSpot(b) {
  ctx.save();
  ctx.beginPath();
  ctx.arc(b.x, b.y, b.radius, 0, Math.PI * 2);
  ctx.clip();
  const angle = Math.PI / 5;          // ~36° below the +x axis
  const dist  = b.radius * 0.4;
  const sx = b.x + Math.cos(angle) * dist;
  const sy = b.y + Math.sin(angle) * dist;
  const rx = b.radius * 0.34;
  const ry = b.radius * 0.20;
  const g = ctx.createRadialGradient(sx - rx * 0.25, sy - ry * 0.25, 0, sx, sy, rx);
  g.addColorStop(0,   'rgba(235, 120, 80, 1)');
  g.addColorStop(0.6, 'rgba(180, 60, 40, 0.95)');
  g.addColorStop(1,   'rgba(110, 35, 25, 0.25)');
  ctx.fillStyle = g;
  ctx.beginPath();
  ctx.ellipse(sx, sy, rx, ry, 0, 0, Math.PI * 2);
  ctx.fill();
  ctx.restore();
}

// ---- Galaxies: parametric spiral, type-driven ----
// Visual only — no gravity, no collisions. Drawn before bodies so they sit
// on top. The galaxy center can be locked to a body (e.g. Sagittarius A).
//
// Types:
//   - 'milkyway'  : nearly face-on barred spiral, 4 arms, warm yellow bar
//   - 'andromeda' : steeply tilted spiral, 5 arms, cooler blue-white palette
//   - 'universe'  : huge CMB-style noise sphere (everything sits inside it)
//   - 'laniakea'  : orange filament-web supercluster

// CMB-like noise texture for the universe. Generated once on demand and
// reused at any size via drawImage scaling, so we never iterate per-frame
// over the ~6e23 px sphere.
let _universeImg = null;
function getUniverseImage() {
  if (_universeImg) return _universeImg;
  const N = 512, cx = 256, cy = 256, r = 256;
  const c = document.createElement('canvas');
  c.width = N; c.height = N;
  const cctx = c.getContext('2d');
  cctx.fillStyle = '#04060f';
  cctx.fillRect(0, 0, N, N);
  // WMAP-style false-color palette: deep navy ↔ blue ↔ cyan ↔ green ↔ yellow ↔ red
  const palette = [
    [10, 25,  80], // deep navy (cold spots)
    [30, 80, 180], // mid blue
    [60,150, 200], // cyan
    [80, 200,120], // green (mean)
    [230,230, 80], // yellow
    [230,100, 60]  // red (hot spots)
  ];
  // Three overlapping noise scales gives the speckled / filamentary look.
  const scales = [
    { count: 4500, rMin: 2.5, rMax:  6, alpha: 0.30 },
    { count: 1400, rMin:  8,  rMax: 22, alpha: 0.18 },
    { count:  220, rMin: 30,  rMax: 70, alpha: 0.10 }
  ];
  for (const s of scales) {
    for (let i = 0; i < s.count; i++) {
      const a = Math.random() * Math.PI * 2;
      const d = Math.sqrt(Math.random()) * r;
      const x = cx + Math.cos(a) * d;
      const y = cy + Math.sin(a) * d;
      // Weighting biases toward blue/green (the "typical" CMB temperature)
      const w = Math.random();
      const p = w < 0.10 ? palette[0]
              : w < 0.40 ? palette[1]
              : w < 0.62 ? palette[2]
              : w < 0.85 ? palette[3]
              : w < 0.95 ? palette[4]
                         : palette[5];
      const blobR = s.rMin + Math.random() * (s.rMax - s.rMin);
      cctx.fillStyle = `rgba(${p[0]},${p[1]},${p[2]},${s.alpha})`;
      cctx.beginPath();
      cctx.arc(x, y, blobR, 0, Math.PI * 2);
      cctx.fill();
    }
  }
  // Circular alpha mask so the texture is a sphere, not a square.
  cctx.globalCompositeOperation = 'destination-in';
  cctx.fillStyle = '#fff';
  cctx.beginPath();
  cctx.arc(cx, cy, r, 0, Math.PI * 2);
  cctx.fill();
  _universeImg = c;
  return c;
}

// Laniakea supercluster: orange/gold filament web with bright cluster nodes.
// Drawn procedurally because the structure is simpler than the CMB.
function drawLaniakea(g) {
  const cx = g.x, cy = g.y, r = g.radius;
  // Seeded jitter so the structure is stable per spawn
  const seed = g._seed || (g._seed = Math.random() * 1000);
  const rand = (i, j) => {
    const x = Math.sin(seed * 12.9898 + i * 78.233 + j * 37.719) * 43758.5453;
    return x - Math.floor(x);
  };

  // Asymmetric blob outline: 64 perturbed radii around the center give the
  // supercluster the lopsided, organic shape from the Laniakea map (not a
  // perfect circle). Three layers of low-frequency noise make it look natural.
  const segments = 64;
  const outline = new Array(segments);
  for (let k = 0; k < segments; k++) {
    const a = (k / segments) * Math.PI * 2;
    const n = 0.62
      + 0.22 * Math.sin(a * 1 + seed * 0.013)
      + 0.14 * Math.sin(a * 2 + seed * 0.029 + 1.3)
      + 0.08 * Math.sin(a * 3 + seed * 0.041 + 2.7);
    outline[k] = Math.max(0.45, Math.min(1.05, n)) * r;
  }
  const blobRadiusAt = (angle) => {
    let a = ((angle % (Math.PI * 2)) + Math.PI * 2) % (Math.PI * 2);
    const idx = (a / (Math.PI * 2)) * segments;
    const i0 = Math.floor(idx) % segments;
    const i1 = (i0 + 1) % segments;
    const t = idx - Math.floor(idx);
    return outline[i0] * (1 - t) + outline[i1] * t;
  };
  // Pick a point inside the blob given a uniform random angle/radius pair.
  const pointInBlob = (rngA, rngR, edgeBias) => {
    const a = rngA * Math.PI * 2;
    const rFrac = edgeBias ? rngR : Math.sqrt(rngR);
    const localR = blobRadiusAt(a) * rFrac;
    return { x: cx + Math.cos(a) * localR, y: cy + Math.sin(a) * localR };
  };

  ctx.save();

  // 1. Subtle dark navy tint inside the blob — a hint that this region is
  //    "the supercluster" against the black background.
  ctx.fillStyle = 'rgba(20, 28, 55, 0.55)';
  ctx.beginPath();
  for (let k = 0; k <= segments; k++) {
    const a = (k % segments) / segments * Math.PI * 2;
    const localR = outline[k % segments];
    const x = cx + Math.cos(a) * localR;
    const y = cy + Math.sin(a) * localR;
    if (k === 0) ctx.moveTo(x, y); else ctx.lineTo(x, y);
  }
  ctx.closePath();
  ctx.fill();

  // (Purple fog removed by request.)

  // 2. Primary "Great Attractor" — off-center; nearly all streamlines flow
  //    toward this point.
  // Deterministic V orientation, rotated 180° from previous: attractor now
  // sits to the LEFT of center, so the V opens to the RIGHT.
  const primAng = Math.PI + 24 * Math.PI / 180; // 180° + 24° clockwise tilt
  const primDist = r * 0.22;
  const primX = cx + Math.cos(primAng) * primDist;
  const primY = cy + Math.sin(primAng) * primDist;
  //    Secondary smaller cluster (the bright knot on the right side of the
  //    photo) — its own convergence point with fewer streamlines.
  const secAng = primAng + Math.PI + (rand(0, 60) - 0.5) * 0.5;
  const secDist = r * (0.55 + rand(0, 61) * 0.12);
  const secX = cx + Math.cos(secAng) * secDist;
  const secY = cy + Math.sin(secAng) * secDist;

  // A flowing streamline from an outer point to an attractor. Multi-frequency
  // perpendicular sine wave displacement gives the line an S-shape with
  // multiple gentle bends along its length (matches the user's sketch).
  const drawFlow = (sx, sy, ax, ay, idx, lineMul, alphaMul) => {
    const vx = ax - sx, vy = ay - sy;
    const dist = Math.hypot(vx, vy) || 1;
    const ux = vx / dist, uy = vy / dist;
    const perpX = -uy, perpY = ux;
    // Consistent S-shape: one full sine cycle (freq=1), small variations
    // in amplitude/phase per line so each looks similar but not identical.
    const amp = dist * (0.11 + rand(idx, 32) * 0.05);     // 0.11–0.16 of length
    const freq = 0.95 + rand(idx, 33) * 0.15;             // 0.95–1.10 cycles
    const phase = (rand(idx, 34) - 0.5) * 0.4;            // tiny phase jitter
    // Build polyline of ~36 sample points along the curve.
    const steps = 36;
    const pts = new Array(steps + 1);
    for (let i = 0; i <= steps; i++) {
      const t = i / steps;
      // Fade displacement at the endpoints so the curve anchors cleanly.
      const fade = Math.sin(t * Math.PI);
      // Single sine — pure S-shape, no second harmonic clutter.
      const wave = Math.sin(t * freq * Math.PI * 2 + phase);
      const off = amp * fade * wave;
      pts[i] = {
        x: sx + ux * dist * t + perpX * off,
        y: sy + uy * dist * t + perpY * off
      };
    }
    const baseAlpha = (0.45 + rand(idx, 38) * 0.55) * alphaMul;
    const grad = ctx.createLinearGradient(sx, sy, ax, ay);
    grad.addColorStop(0,    'rgba(255,220,140,0)');
    grad.addColorStop(0.18, `rgba(255,225,150,${baseAlpha * 0.55})`);
    grad.addColorStop(0.6,  `rgba(255,240,190,${baseAlpha})`);
    grad.addColorStop(0.92, `rgba(255,250,220,${baseAlpha * 0.6})`);
    grad.addColorStop(1,    'rgba(255,255,235,0)');
    ctx.strokeStyle = grad;
    ctx.lineWidth = r * lineMul * (0.0008 + rand(idx, 39) * 0.0022);
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    // Draw the polyline using midpoint-smoothed quadratic curves so it reads
    // as a single continuous flowing line, not a chain of straight segments.
    ctx.beginPath();
    ctx.moveTo(pts[0].x, pts[0].y);
    for (let i = 1; i < pts.length - 1; i++) {
      const mx = (pts[i].x + pts[i + 1].x) / 2;
      const my = (pts[i].y + pts[i + 1].y) / 2;
      ctx.quadraticCurveTo(pts[i].x, pts[i].y, mx, my);
    }
    ctx.lineTo(pts[pts.length - 1].x, pts[pts.length - 1].y);
    ctx.stroke();
  };

  ctx.globalCompositeOperation = 'lighter';

  // 3. Primary attractor flow: ~420 streamlines, MOSTLY concentrated along a
  //    "V"-shaped wedge of two beams emanating from the attractor (matches
  //    the user's sketch of where the filaments gather in the Laniakea map).
  //    Only ~10% are scattered everywhere else as stragglers.
  const wedgeAxis = primAng + Math.PI;        // direction opposite the attractor offset
  const upperBeamCenter = wedgeAxis - 0.70;    // upper arm of the V (~40° above axis)
  const lowerBeamCenter = wedgeAxis + 0.80;    // lower arm — slightly more open
  const beamSpread = 0.035;                    // ~2° half-width per beam (pencil-tight)

  // Vertex-centric arm geometry. The V arms emanate from the vertex with
  // explicit lengths so the lower-arm length is exactly 80% of the upper
  // arm's length (independent of the asymmetric blob outline).
  const upperTipBlobR = blobRadiusAt(upperBeamCenter);
  const upperTipX = cx + Math.cos(upperBeamCenter) * upperTipBlobR;
  const upperTipY = cy + Math.sin(upperBeamCenter) * upperTipBlobR;
  const upperArmLen = Math.hypot(upperTipX - primX, upperTipY - primY);
  const upperArmAng = Math.atan2(upperTipY - primY, upperTipX - primX);

  // Lower arm direction: from vertex toward the blob-outline point along
  // `lowerBeamCenter` (from center). Length is fixed at 0.80 × upper-arm length.
  const lowerDirRefR = blobRadiusAt(lowerBeamCenter);
  const lowerDirRefX = cx + Math.cos(lowerBeamCenter) * lowerDirRefR;
  const lowerDirRefY = cy + Math.sin(lowerBeamCenter) * lowerDirRefR;
  const lowerArmAng = Math.atan2(lowerDirRefY - primY, lowerDirRefX - primX);
  const lowerArmLen = upperArmLen * 0.80;
  const lowerTipX = primX + Math.cos(lowerArmAng) * lowerArmLen;
  const lowerTipY = primY + Math.sin(lowerArmAng) * lowerArmLen;

  const N_PRIM = 420;
  for (let i = 0; i < N_PRIM; i++) {
    const roll = rand(i, 30);
    let armAng, armLen, fracMin, fracMax, jitterKey;
    if (roll < 0.50) {
      // Upper beam — full-length lines.
      armAng = upperArmAng;
      armLen = upperArmLen;
      fracMin = 0.55; fracMax = 1.00;
      jitterKey = 35;
    } else {
      // Lower beam — 80% of the upper arm length.
      armAng = lowerArmAng;
      armLen = lowerArmLen;
      fracMin = 0.25; fracMax = 1.00;
      jitterKey = 36;
    }
    const frac = fracMin + Math.sqrt(rand(i, 31)) * (fracMax - fracMin);
    const ang = armAng + (rand(i, jitterKey) - 0.5) * beamSpread * 2;
    const sx = primX + Math.cos(ang) * armLen * frac;
    const sy = primY + Math.sin(ang) * armLen * frac;
    drawFlow(sx, sy, primX, primY, i, 1.0, 1.0);
  }

  // (Secondary attractor flow removed — only one V-shaped convergence now.)

  // 5. White-purple star points scattered through the blob (the dotted
  //    background of galaxies visible in the picture).
  ctx.globalCompositeOperation = 'source-over';
  const numStars = 850;
  for (let i = 0; i < numStars; i++) {
    const p = pointInBlob(rand(i, 40), rand(i, 41), false);
    const alpha = 0.35 + rand(i, 42) * 0.55;
    const dotR = r * (0.0006 + rand(i, 43) * 0.0014);
    // Slight purple tint variation so the star field doesn't look uniform.
    const tint = rand(i, 44);
    const cr = Math.round(220 + tint * 25);
    const cg = Math.round(220 + tint * 15);
    const cb = Math.round(240 + tint * 15);
    ctx.fillStyle = `rgba(${cr},${cg},${cb},${alpha})`;
    ctx.beginPath();
    ctx.arc(p.x, p.y, dotR, 0, Math.PI * 2);
    ctx.fill();
  }

  // 6. Bright cores — one at the vertex of the V (the Great Attractor) and
  //    one at the far tip of each V arm (where the streamlines originate).
  ctx.globalCompositeOperation = 'lighter';
  const drawCore = (px, py, coreR) => {
    const g1 = ctx.createRadialGradient(px, py, 0, px, py, coreR);
    g1.addColorStop(0,   'rgba(255,255,235,1)');
    g1.addColorStop(0.3, 'rgba(255,235,170,0.85)');
    g1.addColorStop(0.7, 'rgba(255,200,100,0.35)');
    g1.addColorStop(1,   'rgba(255,150, 60,0)');
    ctx.fillStyle = g1;
    ctx.beginPath();
    ctx.arc(px, py, coreR, 0, Math.PI * 2);
    ctx.fill();
  };
  // Vertex of the V (primary attractor, brightest)
  drawCore(primX, primY, r * 0.07);
  // Tip of each V arm — placed at the explicit arm endpoints computed
  // earlier (upper at the blob outline; lower at exactly 80% of upper).
  drawCore(upperTipX, upperTipY, r * 0.045);
  drawCore(lowerTipX, lowerTipY, r * 0.045);

  ctx.restore();
}

function drawUniverse(g) {
  const cx = g.x, cy = g.y, r = g.radius;
  const img = getUniverseImage();
  const d = r * 2;
  // imageSmoothingEnabled stays on (default) so the noise stays continuous
  // when scaled up over many orders of magnitude.
  ctx.drawImage(img, cx - r, cy - r, d, d);
  // Faint outer rim so the edge of the observable universe is visible.
  ctx.save();
  ctx.strokeStyle = 'rgba(120,160,220,0.25)';
  ctx.lineWidth = Math.max(r * 0.002, 1);
  ctx.beginPath();
  ctx.arc(cx, cy, r, 0, Math.PI * 2);
  ctx.stroke();
  ctx.restore();
}

function drawGalaxy(g) {
  if (g.type === 'universe') { drawUniverse(g); return; }
  if (g.type === 'laniakea') { drawLaniakea(g); return; }
  // If this galaxy is anchored to a body, follow that body's position
  if (g.centerBodyId) {
    const c = bodies.find(b => b.id === g.centerBodyId);
    if (c) { g.x = c.x; g.y = c.y; }
  }
  const cx = g.x, cy = g.y, r = g.radius;
  const isAndromeda   = g.type === 'andromeda';
  const isMilkdromeda = g.type === 'milkdromeda';
  // Per-type styling
  const tilt    = isMilkdromeda ? 0.62 : isAndromeda ? 0.27 : 0.92;
  const numArms = isMilkdromeda ? 3    : isAndromeda ? 6    : 4;
  const turns   = isMilkdromeda ? 2.4  : isAndromeda ? 1.7  : 1.55;
  const armCenterTone = isMilkdromeda
    ? '255,230,200,0.32'                       // dispersed warm starlight
    : isAndromeda ? '210,225,255,0.50' : '220,220,240,0.55';
  const armDustTone = isMilkdromeda
    ? '150,100, 90,0.22'
    : isAndromeda ? '120,80,90,0.35' : '170,170,210,0.30';
  const hiiCoreColor = isMilkdromeda
    ? 'rgba(255,170,150,0.6)'
    : isAndromeda ? 'rgba(255,140,170,0.85)' : 'rgba(255,110,170,0.85)';
  const hiiGlowColor = isMilkdromeda
    ? 'rgba(255,200,180,0.22)'
    : isAndromeda ? 'rgba(255,180,190,0.32)' : 'rgba(255,140,190,0.30)';
  const barTones = isMilkdromeda
    ? ['255,230,180,0.95', '255,200,140,0.70', '220,160, 90,0']
    : isAndromeda
      ? ['255,235,200,0.95', '255,205,150,0.65', '210,150, 90,0']
      : ['255,235,180,0.95', '255,200,130,0.75', '220,160, 80,0'];
  const nucTones = isMilkdromeda
    ? ['255,250,225,1', '255,220,160,0.85', '230,180,110,0']
    : isAndromeda
      ? ['255,250,225,1', '255,225,170,0.85', '230,180,110,0']
      : ['255,250,225,1', '255,220,150,0.85', '220,170, 90,0'];
  const rot  = g.rotation || 0;
  ctx.save();

  // 1. Outer halo of dim starlight, deep-blue at the rim
  ctx.save();
  ctx.translate(cx, cy);
  ctx.scale(1, tilt);
  const haloGrad = ctx.createRadialGradient(0, 0, r * 0.05, 0, 0, r * 1.05);
  haloGrad.addColorStop(0,   'rgba(200,210,235,0.55)');
  haloGrad.addColorStop(0.4, 'rgba(140,150,200,0.22)');
  haloGrad.addColorStop(0.8, 'rgba(70,80,150,0.07)');
  haloGrad.addColorStop(1,   'rgba(20,30,80,0)');
  ctx.fillStyle = haloGrad;
  ctx.beginPath();
  ctx.arc(0, 0, r * 1.05, 0, Math.PI * 2);
  ctx.fill();
  ctx.restore();

  // 2. Spiral arms — three parallel sub-bands per arm: a bright core band
  //    flanked by two dimmer dust bands.
  for (let a = 0; a < numArms; a++) {
    const baseAngle = (a / numArms) * Math.PI * 2 + rot;
    const offsets = [-0.18, 0, 0.18];
    const widths  = [0.025, 0.045, 0.025];
    const tones   = [armDustTone, armCenterTone, armDustTone];
    for (let s = 0; s < offsets.length; s++) {
      ctx.beginPath();
      const steps = 90;
      for (let i = 0; i <= steps; i++) {
        const t = i / steps;
        const ang = baseAngle + offsets[s] + t * turns * Math.PI * 2;
        const rad = r * (0.08 + t * 0.95);
        const x = cx + Math.cos(ang) * rad;
        const y = cy + Math.sin(ang) * rad * tilt;
        if (i === 0) ctx.moveTo(x, y);
        else ctx.lineTo(x, y);
      }
      ctx.strokeStyle = `rgba(${tones[s]})`;
      ctx.lineWidth = r * widths[s];
      ctx.lineCap = 'round';
      ctx.lineJoin = 'round';
      ctx.stroke();
    }
  }

  // 3. HII star-forming regions sprinkled along each arm with deterministic
  //    seeded jitter so the pattern is stable per galaxy.
  for (let a = 0; a < numArms; a++) {
    const baseAngle = (a / numArms) * Math.PI * 2 + rot;
    const spots = 26;
    for (let p = 0; p < spots; p++) {
      const t = (p + 0.5) / spots;
      const j1 = Math.sin(a * 73.1 + p * 41.3);
      const j2 = Math.cos(a * 19.7 + p * 7.4);
      const ang = baseAngle + t * turns * Math.PI * 2 + j1 * 0.12;
      const rad = r * (0.12 + t * 0.85) + j2 * r * 0.015;
      const x = cx + Math.cos(ang) * rad;
      const y = cy + Math.sin(ang) * rad * tilt;
      const spotR = r * (0.005 + 0.004 * Math.abs(j1 * j2));
      ctx.fillStyle = hiiGlowColor;
      ctx.beginPath();
      ctx.arc(x, y, spotR * 2.6, 0, Math.PI * 2);
      ctx.fill();
      ctx.fillStyle = hiiCoreColor;
      ctx.beginPath();
      ctx.arc(x, y, spotR, 0, Math.PI * 2);
      ctx.fill();
    }
  }

  // 4. Central bulge — Andromeda gets a much larger soft glow (no bar
  //    rotation), Milkdromeda an even bigger diffuse bulge (post-merger
  //    elliptical remnant), Milky Way keeps its tilted bar shape.
  const barLen = isMilkdromeda ? r * 0.55 : isAndromeda ? r * 0.42 : r * 0.22;
  const barHt  = isMilkdromeda ? r * 0.55 : isAndromeda ? r * 0.42 : r * 0.07;
  const barRot = isMilkdromeda || isAndromeda ? rot : rot + Math.PI / 7;
  ctx.save();
  ctx.translate(cx, cy);
  ctx.rotate(barRot);
  ctx.scale(1, tilt);
  const barGrad = ctx.createRadialGradient(0, 0, 0, 0, 0, barLen);
  barGrad.addColorStop(0,    `rgba(${barTones[0]})`);
  barGrad.addColorStop(0.45, `rgba(${barTones[1]})`);
  barGrad.addColorStop(1,    `rgba(${barTones[2]})`);
  ctx.fillStyle = barGrad;
  ctx.beginPath();
  ctx.ellipse(0, 0, barLen, barHt, 0, 0, Math.PI * 2);
  ctx.fill();
  ctx.restore();

  // 5. Bright central nucleus on top of the bulge
  const nucR = isMilkdromeda ? r * 0.12 : isAndromeda ? r * 0.09 : r * 0.05;
  const nucGrad = ctx.createRadialGradient(cx, cy, 0, cx, cy, nucR);
  nucGrad.addColorStop(0,   `rgba(${nucTones[0]})`);
  nucGrad.addColorStop(0.5, `rgba(${nucTones[1]})`);
  nucGrad.addColorStop(1,   `rgba(${nucTones[2]})`);
  ctx.fillStyle = nucGrad;
  ctx.beginPath();
  ctx.arc(cx, cy, nucR, 0, Math.PI * 2);
  ctx.fill();

  ctx.restore();
}

function drawGalaxies() {
  // Background-to-foreground order so the universe sits behind everything,
  // Laniakea between the universe and the individual galaxies, and spiral
  // galaxies on top.
  const order = { universe: 0, laniakea: 1 };
  const sorted = galaxies.slice().sort((a, b) => (order[a.type] ?? 2) - (order[b.type] ?? 2));
  for (const g of sorted) drawGalaxy(g);
}

// When the Milky Way and Andromeda discs overlap, fuse them into the
// elliptical "Milkdromeda" remnant. Both central BHs are removed and
// replaced by a single 200-million-solar-mass black hole at the mass-
// weighted center.
function checkGalaxyMerges() {
  const mw = galaxies.find(g => g.type === 'milkyway');
  const an = galaxies.find(g => g.type === 'andromeda');
  if (!mw || !an) return;
  const dx = an.x - mw.x, dy = an.y - mw.y;
  const dist = Math.sqrt(dx * dx + dy * dy);
  // Merge when the disc edges first touch (sum of radii).
  if (dist >= mw.radius + an.radius) return;

  const sgrA = mw.centerBodyId ? bodies.find(b => b.id === mw.centerBodyId) : null;
  const m31  = an.centerBodyId ? bodies.find(b => b.id === an.centerBodyId) : null;

  // Mass-weighted center of the two central BHs (falls back to galaxy
  // centers if either is missing for any reason).
  let cx, cy;
  if (sgrA && m31) {
    const mt = sgrA.mass + m31.mass;
    cx = (sgrA.x * sgrA.mass + m31.x * m31.mass) / mt;
    cy = (sgrA.y * sgrA.mass + m31.y * m31.mass) / mt;
  } else {
    cx = (mw.x + an.x) / 2;
    cy = (mw.y + an.y) / 2;
  }

  // Remove the two original supermassive BHs
  if (sgrA) {
    const i = bodies.indexOf(sgrA);
    if (i >= 0) bodies.splice(i, 1);
  }
  if (m31) {
    const i = bodies.indexOf(m31);
    if (i >= 0) bodies.splice(i, 1);
  }

  // Spawn the merged BH — 200 million × the Sun's mass (sim mass: ×1000)
  // 3 trillion × the Sun's mass (sim mass × 1000 per solar mass) = 3e15
  const mergedMass = 3_000_000_000_000 * 1000;
  const mergedRadius = 12 + Math.cbrt(mergedMass / 1000) * 3;
  const merged = {
    id: 'sun-' + nextSunId,
    name: 'Milkdromeda',
    isSun: true,
    x: cx, y: cy, vx: 0, vy: 0,
    mass: mergedMass,
    radius: Math.max(mergedRadius, 10000),
    color: '#000000',
    trail: [], velMul: 1,
    createdAtSim: simTime,
    stellarPhase: 'black-hole',
    phaseAtSim: simTime,
    accretionRing: []
  };
  bodies.push(merged);
  nextSunId++;

  // Remove the two original galaxies and add the merged elliptical
  galaxies = galaxies.filter(g => g !== mw && g !== an);
  galaxies.push({
    type: 'milkdromeda',
    x: cx, y: cy,
    radius: an.radius, // matches Andromeda's size
    rotation: 0,
    centerBodyId: merged.id
  });

  buildControls();
  triggerMergeFlash();
}

// Draw Saturn-style rings around a planet. `backHalf=true` draws the half
// behind the planet body (above the equator line in canvas), `false` draws
// the half in front (below it). `scale` multiplies the ring radii — 1 for
// Saturn, 200 for J1407b.
function drawSaturnRings(b, backHalf, scale) {
  const innerR = b.radius * 1.6 * scale;
  const outerR = b.radius * 2.8 * scale;
  const tilt = 0.28;
  ctx.save();
  const rings = [
    { frac: 0.10, alpha: 0.85, color: '230,210,180' },
    { frac: 0.35, alpha: 0.45, color: '180,160,130' },
    { frac: 0.55, alpha: 0.90, color: '240,220,190' },
    { frac: 0.80, alpha: 0.70, color: '210,180,140' }
  ];
  for (const ring of rings) {
    const r = innerR + (outerR - innerR) * ring.frac;
    const ry = r * tilt;
    ctx.strokeStyle = `rgba(${ring.color},${ring.alpha})`;
    ctx.lineWidth = (outerR - innerR) * 0.18;
    ctx.beginPath();
    ctx.ellipse(b.x, b.y, r, ry, 0,
      backHalf ? Math.PI : 0,
      backHalf ? 2 * Math.PI : Math.PI);
    ctx.stroke();
  }
  ctx.restore();
}

function isEarthLike(planet) {
  if (!planet || planet.isSun) return false;
  const name = (planet.name || '').trim().toLowerCase();
  return EARTH_NAMES.has(name);
}

// While a strange-matter neutron star (or magnetar) exists, the system stops
// celebrating life — no yearly fireworks, no rocket launches.
function hasLifeKillerStar() {
  for (const b of bodies) {
    if (b.isSun && (b.strangeMatter || b.magnetar) && b.stellarPhase === 'neutron-star') return true;
  }
  return false;
}

function applyEarthFeatures(planet) {
  if (!isEarthLike(planet)) return;
  // Green continents on the surface
  if (!planet.continents) {
    const n = 3 + Math.floor(Math.random() * 3);
    planet.continents = [];
    for (let i = 0; i < n; i++) {
      planet.continents.push({
        angle: Math.random() * Math.PI * 2,
        distFrac: Math.random() * 0.5,
        sizeFrac: 0.18 + Math.random() * 0.14,
        shade: Math.random()
      });
    }
  }
  // 10% chance to launch an exploration rocket (suppressed while a strange
  // neutron star is wiping out life across the system)
  if (!hasLifeKillerStar() && Math.random() < 0.1) spawnRocket(planet);
}

// One-shot pulse fired when a strange-matter neutron star is born — its
// massive magnetic field wipes life off any planet and vaporizes any rocket
// within the destroyRadius.
function strangeMatterBurst(sun) {
  const destroyRadius = 400;
  const r2 = destroyRadius * destroyRadius;
  for (const b of bodies) {
    if (b === sun) continue;
    const dx = b.x - sun.x, dy = b.y - sun.y;
    if (dx * dx + dy * dy > r2) continue;
    if (b.continents) {
      // Quick sparkle on each lost continent so the player sees life dying
      for (const c of b.continents) {
        const cx = b.x + Math.cos(c.angle) * c.distFrac * b.radius;
        const cy = b.y + Math.sin(c.angle) * c.distFrac * b.radius;
        spawnMergeEffect(cx, cy, '#88ff88');
      }
      delete b.continents;
    }
  }
  for (let i = rockets.length - 1; i >= 0; i--) {
    const r = rockets[i];
    const dx = r.x - sun.x, dy = r.y - sun.y;
    if (dx * dx + dy * dy <= r2) {
      spawnMergeEffect(r.x, r.y, '#cc88ff');
      rockets.splice(i, 1);
    }
  }
  triggerMergeFlash();
}

// Fired when a neutron star converts to a magnetar (next to a black hole, 50%).
// The magnetar's field is so extreme it stains every planet a deep black-brown
// and vaporizes every rocket regardless of distance.
function magnetarBurst(sun) {
  for (const b of bodies) {
    if (b.isSun) continue;
    if (b.continents) {
      for (const c of b.continents) {
        const cx = b.x + Math.cos(c.angle) * c.distFrac * b.radius;
        const cy = b.y + Math.sin(c.angle) * c.distFrac * b.radius;
        spawnMergeEffect(cx, cy, '#88ff88');
      }
      delete b.continents;
    }
    b.color = '#2d1a0d'; // deep black-brown
  }
  for (let i = rockets.length - 1; i >= 0; i--) {
    const r = rockets[i];
    spawnMergeEffect(r.x, r.y, '#cc88ff');
    rockets.splice(i, 1);
  }
  triggerMergeFlash();
}

// Each frame: if a neutron star is sitting next to a black hole, give it a
// one-shot 50% roll to become a magnetar.
function checkMagnetarConversion() {
  let hasBH = false;
  for (const b of bodies) {
    if (b.isSun && (b.stellarPhase === 'black-hole' || b.stellarPhase === 'evaporating')) {
      hasBH = true; break;
    }
  }
  if (!hasBH) return;
  const PROX2 = 150 * 150;
  for (const ns of bodies) {
    if (!ns.isSun || ns.stellarPhase !== 'neutron-star') continue;
    if (ns.magnetarRolled) continue;
    for (const bh of bodies) {
      if (bh === ns) continue;
      if (!bh.isSun) continue;
      if (bh.stellarPhase !== 'black-hole' && bh.stellarPhase !== 'evaporating') continue;
      const dx = bh.x - ns.x, dy = bh.y - ns.y;
      if (dx * dx + dy * dy < PROX2) {
        ns.magnetarRolled = true;
        if (Math.random() < 0.5) {
          ns.magnetar = true;
          magnetarBurst(ns);
        }
        break;
      }
    }
  }
}

// Colorful firework burst at (x, y), inheriting (vx, vy) for in-orbit drift
function spawnFireworks(x, y, originVx, originVy) {
  const colors = ['#ff4466', '#ffcc44', '#44ff66', '#44ccff', '#cc66ff', '#ff66cc', '#ffffff'];
  const numBursts = 2 + Math.floor(Math.random() * 3);
  for (let b = 0; b < numBursts; b++) {
    const color = colors[Math.floor(Math.random() * colors.length)];
    const particles = [];
    const n = 20 + Math.floor(Math.random() * 10);
    const ox = (Math.random() - 0.5) * 10;
    const oy = (Math.random() - 0.5) * 10;
    for (let i = 0; i < n; i++) {
      const angle = (Math.PI * 2 * i) / n + Math.random() * 0.3;
      const speed = 1.8 + Math.random() * 2.5;
      particles.push({
        x: x + ox,
        y: y + oy,
        vx: (originVx || 0) + Math.cos(angle) * speed,
        vy: (originVy || 0) + Math.sin(angle) * speed,
        life: 1
      });
    }
    mergeEffects.push({ particles, color, age: 0 });
  }
}

// Track each earth-like planet's orbital progress around the heaviest sun
// and fire colorful fireworks every full revolution ("year").
function trackEarthOrbits() {
  let primarySun = null;
  let bestMass = 0;
  for (const s of bodies) {
    if (s.isSun && s.mass > bestMass) { primarySun = s; bestMass = s.mass; }
  }
  if (!primarySun) return;
  for (const b of bodies) {
    if (!isEarthLike(b)) continue;
    const ang = Math.atan2(b.y - primarySun.y, b.x - primarySun.x);
    if (b._orbitSunId !== primarySun.id) {
      b._lastOrbitAng = ang;
      b._orbitAccum = 0;
      b._orbitSunId = primarySun.id;
      continue;
    }
    let delta = ang - b._lastOrbitAng;
    while (delta > Math.PI) delta -= 2 * Math.PI;
    while (delta < -Math.PI) delta += 2 * Math.PI;
    b._orbitAccum += delta;
    b._lastOrbitAng = ang;
    if (Math.abs(b._orbitAccum) >= 2 * Math.PI) {
      if (!hasLifeKillerStar()) spawnFireworks(b.x, b.y, b.vx, b.vy);
      b._orbitAccum = 0;
    }
  }
}

function spawnRocket(home) {
  const angle = Math.random() * Math.PI * 2;
  const startOffset = home.radius + 6;
  rockets.push({
    x: home.x + Math.cos(angle) * startOffset,
    y: home.y + Math.sin(angle) * startOffset,
    vx: (home.vx || 0) + Math.cos(angle) * 0.6,
    vy: (home.vy || 0) + Math.sin(angle) * 0.6,
    heading: angle,
    state: 'launching',
    stateAtSim: simTime,
    spawnedAtSim: simTime,
    home: home,
    returning: false,
    target: null,
    visited: new Set([home.id]),
    landOffsetX: 0,
    landOffsetY: 0
  });
}

function pickRocketTarget(rocket) {
  const candidates = bodies.filter(b =>
    !rocket.visited.has(b.id) &&
    b.stellarPhase !== 'black-hole' &&
    b.stellarPhase !== 'evaporating' &&
    b.stellarPhase !== 'nebula' &&
    b.stellarPhase !== 'supernova'
  );
  if (candidates.length === 0) return null;
  let best = null, bestDist = Infinity;
  for (const c of candidates) {
    const dx = c.x - rocket.x, dy = c.y - rocket.y;
    const d = dx * dx + dy * dy;
    if (d < bestDist) { bestDist = d; best = c; }
  }
  return best;
}

// Begin the return-home journey. Lifts off if currently landed.
function rocketReturnHome(r) {
  r.returning = true;
  if (bodies.includes(r.home)) {
    r.target = r.home;
    if (r.state === 'landed') {
      r.vx += Math.cos(r.heading) * 1.4;
      r.vy += Math.sin(r.heading) * 1.4;
    }
    r.state = 'cruising';
  } else {
    r.target = null;
    if (r.state === 'landed') {
      r.vx += Math.cos(r.heading) * 1.8;
      r.vy += Math.sin(r.heading) * 1.8;
    }
    r.state = 'departing';
  }
  r.stateAtSim = simTime;
}

function updateRockets(dtUnits) {
  // Magnetic-field kill zone: any rocket within MAGNETAR_KILL_R of a magnetar
  // is shredded by the 10¹¹-T field. Check once per frame for efficiency.
  const MAGNETAR_KILL_R = 1500;
  const magnetars = bodies.filter(b =>
    b.isSun && b.magnetar && b.stellarPhase === 'neutron-star'
  );
  const killR2 = MAGNETAR_KILL_R * MAGNETAR_KILL_R;

  for (let i = rockets.length - 1; i >= 0; i--) {
    const r = rockets[i];

    // Magnetar proximity blast — destroy the rocket if any magnetar is near
    let killed = false;
    for (const m of magnetars) {
      const dx = r.x - m.x, dy = r.y - m.y;
      if (dx * dx + dy * dy < killR2) {
        spawnMergeEffect(r.x, r.y, '#cc88ff');
        rockets.splice(i, 1);
        killed = true;
        break;
      }
    }
    if (killed) continue;

    // 4-minute deadline: head home (or depart if home is gone)
    if (!r.returning && (simTime - r.spawnedAtSim) / 1000 > 240) {
      rocketReturnHome(r);
    }

    // If our target was destroyed, drop it (and lift off if we were landed)
    if (r.target && !bodies.includes(r.target)) {
      r.target = null;
      if (r.state === 'landed') {
        r.state = 'cruising';
        r.stateAtSim = simTime;
      }
    }

    if (r.state === 'launching') {
      const since = (simTime - r.stateAtSim) / 1000;
      if (since < 1.5) {
        r.vx += Math.cos(r.heading) * 0.15 * dtUnits;
        r.vy += Math.sin(r.heading) * 0.15 * dtUnits;
      } else {
        r.state = 'cruising';
        r.target = pickRocketTarget(r);
        r.stateAtSim = simTime;
      }
    } else if (r.state === 'cruising') {
      if (!r.target) {
        // Returning rockets always aim for home; otherwise pick the next world to explore
        r.target = r.returning && bodies.includes(r.home) ? r.home : pickRocketTarget(r);
      }
      if (r.target) {
        const dx = r.target.x - r.x;
        const dy = r.target.y - r.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        const targetAngle = Math.atan2(dy, dx);
        let diff = targetAngle - r.heading;
        while (diff > Math.PI) diff -= 2 * Math.PI;
        while (diff < -Math.PI) diff += 2 * Math.PI;
        r.heading += diff * 0.08 * dtUnits;

        const speed = Math.sqrt(r.vx * r.vx + r.vy * r.vy);
        // Brake when close to the target so the rocket can touch down softly
        const brakeDist = Math.max(r.target.radius + 50, 70);
        if (dist < brakeDist) {
          const tvx = r.target.vx || 0, tvy = r.target.vy || 0;
          r.vx += (tvx - r.vx) * 0.12 * dtUnits;
          r.vy += (tvy - r.vy) * 0.12 * dtUnits;
          r.vx += Math.cos(r.heading) * 0.04 * dtUnits;
          r.vy += Math.sin(r.heading) * 0.04 * dtUnits;
        } else if (speed < 5) {
          r.vx += Math.cos(r.heading) * 0.1 * dtUnits;
          r.vy += Math.sin(r.heading) * 0.1 * dtUnits;
        }
        r.vx *= Math.pow(0.99, dtUnits);
        r.vy *= Math.pow(0.99, dtUnits);

        // Touchdown: snap to the surface
        const landDist = r.target.radius + 4;
        if (dist < landDist) {
          const ang = Math.atan2(r.y - r.target.y, r.x - r.target.x);
          const surfDist = r.target.radius + 4;
          r.landOffsetX = Math.cos(ang) * surfDist;
          r.landOffsetY = Math.sin(ang) * surfDist;
          r.x = r.target.x + r.landOffsetX;
          r.y = r.target.y + r.landOffsetY;
          r.heading = ang;
          r.vx = r.target.vx || 0;
          r.vy = r.target.vy || 0;
          r.state = 'landed';
          r.stateAtSim = simTime;
          r.visited.add(r.target.id);
          // 10% chance to seed life on a barren planet on touchdown.
          // Name is intentionally left alone.
          if (!r.target.isSun && !r.target.continents && Math.random() < 0.1) {
            r.target.continents = makeContinents();
          }
        }
      } else {
        // No target to cruise toward — go home if possible, else depart
        if (!r.returning && bodies.includes(r.home)) {
          r.returning = true;
          r.target = r.home;
          r.stateAtSim = simTime;
        } else {
          r.state = 'departing';
          r.stateAtSim = simTime;
        }
      }
    } else if (r.state === 'landed' && r.target) {
      // Stick to the planet surface, riding along with its motion
      r.x = r.target.x + r.landOffsetX;
      r.y = r.target.y + r.landOffsetY;
      r.heading = Math.atan2(r.landOffsetY, r.landOffsetX);
      r.vx = r.target.vx || 0;
      r.vy = r.target.vy || 0;

      const sinceLanded = (simTime - r.stateAtSim) / 1000;
      if (sinceLanded > 2.5) {
        // Mission complete: we made it back home
        if (r.returning && r.target === r.home) {
          rockets.splice(i, 1);
          continue;
        }
        const next = pickRocketTarget(r);
        if (next) {
          r.state = 'cruising';
          r.target = next;
          r.stateAtSim = simTime;
          // Liftoff kick along the surface normal
          r.vx += Math.cos(r.heading) * 1.4;
          r.vy += Math.sin(r.heading) * 1.4;
        } else if (bodies.includes(r.home)) {
          // Nothing left to explore — head home
          r.state = 'cruising';
          r.target = r.home;
          r.returning = true;
          r.stateAtSim = simTime;
          r.vx += Math.cos(r.heading) * 1.4;
          r.vy += Math.sin(r.heading) * 1.4;
        } else {
          r.state = 'departing';
          r.stateAtSim = simTime;
          r.vx += Math.cos(r.heading) * 1.8;
          r.vy += Math.sin(r.heading) * 1.8;
        }
      }
      continue; // position locked to surface — skip the integration step
    } else if (r.state === 'departing') {
      const since = (simTime - r.stateAtSim) / 1000;
      if (since > 15) { rockets.splice(i, 1); continue; }
    }

    r.x += r.vx * dtUnits;
    r.y += r.vy * dtUnits;
  }
}

function drawSingleRocket(r, t) {
  // Flame trail (skip when sitting on a planet surface)
  if (r.state !== 'landed') {
    const flameLen = 10 + 4 * Math.sin(t * 0.02);
    const fx = r.x - Math.cos(r.heading) * flameLen;
    const fy = r.y - Math.sin(r.heading) * flameLen;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    const fg = ctx.createLinearGradient(r.x, r.y, fx, fy);
    fg.addColorStop(0, 'rgba(255,220,80,0.95)');
    fg.addColorStop(0.5, 'rgba(255,120,40,0.55)');
    fg.addColorStop(1, 'rgba(255,40,20,0)');
    ctx.strokeStyle = fg;
    ctx.lineCap = 'round';
    ctx.lineWidth = 4;
    ctx.beginPath();
    ctx.moveTo(r.x, r.y);
    ctx.lineTo(fx, fy);
    ctx.stroke();
    ctx.restore();
  }

  // Rocket body — small triangle
  ctx.save();
  ctx.translate(r.x, r.y);
  ctx.rotate(r.heading);
  ctx.fillStyle = '#e8eef5';
  ctx.beginPath();
  ctx.moveTo(7, 0);
  ctx.lineTo(-4, 3);
  ctx.lineTo(-4, -3);
  ctx.closePath();
  ctx.fill();
  ctx.strokeStyle = '#7dd3fc';
  ctx.lineWidth = 0.8;
  ctx.stroke();
  // Cockpit window
  ctx.fillStyle = '#7dd3fc';
  ctx.beginPath();
  ctx.arc(1, 0, 1.2, 0, Math.PI * 2);
  ctx.fill();
  ctx.restore();
}

function drawRockets(t) {
  for (const r of rockets) drawSingleRocket(r, t);
}

// ---- Rendering ----
function drawStars(t) {
  const w = canvas.clientWidth, h = canvas.clientHeight;
  for (const s of stars) {
    const twinkle = 0.5 + 0.5 * Math.sin(t * s.speed + s.phase);
    ctx.globalAlpha = twinkle * 0.7 + 0.1;
    ctx.fillStyle = '#fff';
    ctx.beginPath();
    ctx.arc(s.x * w, s.y * h, s.r, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.globalAlpha = 1;
}

// ---- Stellar evolution ----
// Main-sequence lifespan is now derived from spectral class via
// getSpectralLifespanSec. Death path is still mass-based:
//   mass 80-500     → white dwarf
//   mass 501-2500   → red giant → collapse → white dwarf
//   mass 2501-100000 → supernova → 25% neutron star / 75% black hole
//   mass > 100000   → direct collapse to black hole (5s)
//   Neutron star: 2 min → 25% nebula (10% spawns solar system) / 75% black hole
//   Black hole: 3 hrs → evaporating (30 min) → removed
// Phases are sticky; changing mass via slider resets to main sequence

// Spectral-class main-sequence lifespans. With the post-rescale time unit
// (1× speed = 1 sim month per real second), all values below are MONTHS, and
// each band's endpoints are the user-specified years × 12.
// Priority for overlapping ranges: O > B > A > F > G > K > M. Lower mass = longer life.
//   M 80–449:        10 T  yr  →  100 B yr     (1.2e14 → 1.2e12  months)
//   K 450–799:       100 B yr  →  70  B yr     (1.2e12 → 8.4e11  months)
//   G 800–1,039:     70  B yr  →  9   B yr     (8.4e11 → 1.08e11 months)
//   F 1,040–1,399:   9   B yr  →  2   B yr     (1.08e11 → 2.4e10 months)
//   A 1,400–1,999:   2   B yr  →  1   B yr     (2.4e10 → 1.2e10 months)
//   B 2,000–15,999:  1   B yr  →  10  M yr     (1.2e10 → 1.2e8  months)
//   O 16,000–100,000:10  M yr  →  3   M yr     (1.2e8  → 3.6e7  months)
function getSpectralLifespanSec(mass) {
  const lerp = (m, m0, m1, s0, s1) => {
    const t = Math.max(0, Math.min(1, (m - m0) / (m1 - m0)));
    return s0 + (s1 - s0) * t;
  };
  const isOType = mass >= 16000 && mass <= 100000;
  const isBType = !isOType && mass >= 2000 && mass <= 18000;
  const isAType = !isOType && !isBType && mass >= 1400 && mass <= 2100;
  const isFType = !isOType && !isBType && !isAType && mass >= 1040 && mass <= 1400;
  const isGType = !isOType && !isBType && !isAType && !isFType && mass >= 800 && mass <= 1400;
  const isKType = !isOType && !isBType && !isAType && !isFType && !isGType && mass >= 450 && mass <= 800;
  const isMType = !isOType && !isBType && !isAType && !isFType && !isGType && !isKType && mass >= 80 && mass <= 600;
  if (isOType) return lerp(mass, 16000, 100000, 1.2e8,  3.6e7);
  if (isBType) return lerp(mass, 2000,  15999,  1.2e10, 1.2e8);
  if (isAType) return lerp(mass, 1400,  1999,   2.4e10, 1.2e10);
  if (isFType) return lerp(mass, 1040,  1399,   1.08e11,2.4e10);
  if (isGType) return lerp(mass, 800,   1039,   8.4e11, 1.08e11);
  if (isKType) return lerp(mass, 450,   799,    1.2e12, 8.4e11);
  if (isMType) return lerp(mass, 80,    449,    1.2e14, 1.2e12);
  return null;
}

// Real-physics Hawking lifespan: τ = 5120π G² M³ / (ℏ c⁴).
// 1 sun = 1000 sim mass = 1.989e30 kg → 1 sim mass unit = 1.989e27 kg.
// Result is in seconds; for stellar-mass BHs this is astronomically large
// (a solar-mass BH lives ~2×10⁶⁷ years), which is the physically correct
// behavior — they essentially never evaporate.
function getBlackHoleLifespanSec(simMass) {
  const G = 6.674e-11;
  const HBAR = 1.054e-34;
  const C = 2.998e8;
  const KG_PER_SIM = 1.989e27;
  const M = Math.max(1, simMass) * KG_PER_SIM;
  return (5120 * Math.PI * G * G * M * M * M) / (HBAR * Math.pow(C, 4));
}

// Higher mass → shorter post-MS phase. Each function clamps to its declared
// mass band and lerps linearly between the two endpoints. All values below
// are in MONTHS (post-rescale unit; 1× = 1 month / real sec).
function _lerpClamp(m, m0, m1, s0, s1) {
  const t = Math.max(0, Math.min(1, (m - m0) / (m1 - m0)));
  return s0 + (s1 - s0) * t;
}
function getRedGiantDurationSec(simMass) {
  // Brief red-giant phase for normal post-MS stars (mass 501–2500). Kept short
  // so it reads as a transitional flash; red SUPER giants have their own
  // duration function below.
  return _lerpClamp(simMass, 501, 2500, 500, 0.25);
}
function getRedSuperGiantDurationSec() {
  // 1 M yr → 500 K yr (random per star).  1.2e7 → 6e6 months.
  return 6e6 + Math.random() * 6e6;
}
function getBlueSuperGiantDurationSec(simMass) {
  // 10 M yr @ 2501  →  2 M yr @ 100000+   (1.2e8 → 2.4e7 months)
  return _lerpClamp(simMass, 2501, 100000, 1.2e8, 2.4e7);
}
function getKSuperGiantDurationSec(simMass) {
  // 50 M yr @ 501  →  10 M yr @ 2500      (6e8 → 1.2e8 months)
  return _lerpClamp(simMass, 501, 2500, 6e8, 1.2e8);
}
function getWolfRayetDurationSec(simMass) {
  // Mass-shed transition phase; left short relative to MS lifetime.
  return _lerpClamp(simMass, 16000, 100000, 1500, 0.25);
}
function getNeutronBeamDurationSec() {
  // Pulsar-beam phase: 5 K yr → 5 M yr (random).  60 K → 60 M months.
  return 60000 + Math.random() * (60_000_000 - 60_000);
}
function getNeutronTotalLifespanSec() {
  // Total neutron-star life: 10 B yr → 100 B yr (random).  1.2e11 → 1.2e12 months.
  return 1.2e11 + Math.random() * (1.2e12 - 1.2e11);
}

function checkStellarEvolution() {
  for (let i = bodies.length - 1; i >= 0; i--) {
    const sun = bodies[i];
    if (!sun.isSun) continue;
    if (!sun.stellarPhase) sun.stellarPhase = 'main-sequence';
    if (sun.createdAtSim == null) sun.createdAtSim = simTime;

    // ---- Terminal phases ----
    // Nebula → 10% spawn solar system, then fade
    if (sun.stellarPhase === 'nebula') {
      const since = (simTime - sun.phaseAtSim) / 1000;
      if (since >= 20) {
        if (!sun.nebulaResolved) {
          sun.nebulaResolved = true;
          if (Math.random() < 0.1) spawnSolarSystem(sun.x, sun.y);
        }
        if (since >= 25) { bodies.splice(i, 1); buildControls(); }
      }
      continue;
    }
    // Evaporating black hole → shrink and remove
    if (sun.stellarPhase === 'evaporating') {
      const since = (simTime - sun.phaseAtSim) / 1000;
      if (since >= 1800) { bodies.splice(i, 1); buildControls(); }
      continue;
    }
    // K super giant — temporary pause during expansion (5–25 min, mass-based).
    // After the timer the star drops back into the expanding phase and
    // continues toward becoming a red giant.
    if (sun.stellarPhase === 'k-super-giant') {
      const since = (simTime - (sun.kSuperAtSim || sun.phaseAtSim || simTime)) / 1000;
      if (sun.kSuperDuration == null) sun.kSuperDuration = getKSuperGiantDurationSec(sun.mass);
      if (since >= sun.kSuperDuration) {
        sun.stellarPhase = 'expanding';
      }
      continue;
    }
    // Blue super giant → 90% explodes (supernova), 10% quietly collapses
    // directly into a neutron star or black hole. Duration 5–25 min, mass-based.
    if (sun.stellarPhase === 'blue-super-giant') {
      const since = (simTime - sun.phaseAtSim) / 1000;
      if (sun.bsgDuration == null) sun.bsgDuration = getBlueSuperGiantDurationSec(sun.mass);
      if (since >= sun.bsgDuration) {
        if (Math.random() < 0.9) {
          // 90%: dramatic supernova (which then resolves to NS or BH normally)
          sun.stellarPhase = 'supernova';
          sun.phaseAtSim = simTime;
        } else if (sun.mass > 100000) {
          // 10% & super-massive → direct black hole
          sun.stellarPhase = 'black-hole';
          sun.radius = 12 + Math.cbrt(sun.mass / 1000) * 3;
          sun.phaseAtSim = simTime;
          sun.accretionRing = [];
        } else {
          // 10% & smaller → direct neutron star (skip the supernova drama).
          // Match the supernova-resolution 25% NS / 75% BH ratio.
          if (Math.random() < 0.25) {
            sun.stellarPhase = 'neutron-star';
            sun.radius = 5;
            sun.phaseAtSim = simTime;
            sun.neutronResolved = false;
            if (Math.random() < 0.0001) {
              sun.strangeMatter = true;
              strangeMatterBurst(sun);
            }
          } else {
            sun.stellarPhase = 'black-hole';
            sun.radius = 12 + Math.cbrt(sun.mass / 1000) * 3;
            sun.phaseAtSim = simTime;
            sun.accretionRing = [];
          }
        }
        triggerMergeFlash();
      }
      continue;
    }
    // Black hole → evaporate after the Hawking lifespan (mass-dependent).
    // For stellar-mass BHs this is ~10⁶⁷ years, so they essentially never
    // evaporate — which is the physically correct behavior.
    if (sun.stellarPhase === 'black-hole') {
      const since = (simTime - sun.phaseAtSim) / 1000;
      if (sun.bhLifespan == null) sun.bhLifespan = getBlackHoleLifespanSec(sun.mass);
      if (since >= sun.bhLifespan) {
        sun.stellarPhase = 'evaporating';
        sun.phaseAtSim = simTime;
      }
      continue;
    }
    // Wolf-Rayet → layers blow off for the chosen duration, then supernova.
    // Ejecta particles spawn each frame in drawSunCorona; nothing to do here
    // except hand off when the timer expires.
    if (sun.stellarPhase === 'wolf-rayet') {
      const since = (simTime - sun.phaseAtSim) / 1000;
      if (sun.wolfRayetDuration == null) sun.wolfRayetDuration = getWolfRayetDurationSec(sun.mass * 3);
      if (since >= sun.wolfRayetDuration) {
        sun.stellarPhase = 'supernova';
        sun.phaseAtSim = simTime;
        triggerMergeFlash();
      }
      continue;
    }
    // Neutron star (with beam) → after the pulsar beam expires it becomes a
    // "dormant" neutron star. Beam duration randomized per star to 5K–5M yr.
    if (sun.stellarPhase === 'neutron-star') {
      const since = (simTime - sun.phaseAtSim) / 1000;
      if (sun.neutronBeamDuration == null) {
        sun.neutronBeamDuration = getNeutronBeamDurationSec();
      }
      if (sun.neutronStartSim == null) sun.neutronStartSim = sun.phaseAtSim;
      if (since >= sun.neutronBeamDuration) {
        sun.stellarPhase = 'dormant-neutron-star';
        sun.phaseAtSim = simTime;
      }
      continue;
    }
    // Dormant neutron star → after the per-star total NS lifespan (10–100 B yr)
    // it becomes a black dwarf. Same rendering as a neutron star but no beam.
    if (sun.stellarPhase === 'dormant-neutron-star') {
      if (sun.neutronStartSim == null) sun.neutronStartSim = sun.phaseAtSim;
      if (sun.neutronTotalLifespan == null) {
        sun.neutronTotalLifespan = getNeutronTotalLifespanSec();
      }
      const totalSince = (simTime - sun.neutronStartSim) / 1000;
      if (totalSince >= sun.neutronTotalLifespan) {
        sun.stellarPhase = 'black-dwarf';
        sun.radius = 28 + Math.cbrt(sun.mass / 1000) * 4;
      }
      continue;
    }
    // Supernova flash → resolve to neutron star or black hole
    if (sun.stellarPhase === 'supernova') {
      const since = (simTime - sun.phaseAtSim) / 1000;
      if (since >= 3) {
        if (Math.random() < 0.25) {
          sun.stellarPhase = 'neutron-star';
          sun.radius = 5;
          // 0.01% chance this neutron star is made of strange matter, whose
          // massive magnetic field annihilates nearby life and rockets.
          if (Math.random() < 0.0001) {
            sun.strangeMatter = true;
            strangeMatterBurst(sun);
          }
        } else {
          sun.stellarPhase = 'black-hole';
          sun.radius = 12 + Math.cbrt(sun.mass / 1000) * 3;
          sun.accretionRing = [];
        }
        sun.phaseAtSim = simTime;
        sun.neutronResolved = false;
        const el = document.getElementById('mass-val-' + sun.id);
        if (el) el.textContent = sun.mass.toFixed(0);
      }
      continue;
    }

    // White dwarf → black dwarf (shared)
    if (sun.stellarPhase === 'white-dwarf') {
      if (sun.whiteDwarfAtSim != null) {
        const sinceWD = (simTime - sun.whiteDwarfAtSim) / 1000;
        if (sinceWD >= 3600) sun.stellarPhase = 'black-dwarf';
      }
      continue;
    }
    if (sun.stellarPhase === 'black-dwarf') continue;

    // Red giant → collapsing → white dwarf. Duration 0.25s–8m20s, mass-based.
    if (sun.stellarPhase === 'red-giant') {
      if (sun.redGiantAtSim != null) {
        const sinceRG = (simTime - sun.redGiantAtSim) / 1000;
        if (sun.redGiantDuration == null) {
          sun.redGiantDuration = sun.redSuperGiant
            ? getRedSuperGiantDurationSec()
            : getRedGiantDurationSec(sun.mass);
        }
        if (sinceRG >= sun.redGiantDuration) {
          sun.stellarPhase = 'collapsing';
          sun.phaseAtSim = simTime;
        }
      }
      continue;
    }
    if (sun.stellarPhase === 'collapsing') {
      const since = (simTime - sun.phaseAtSim) / 1000;
      if (since >= 2) {
        sun.stellarPhase = 'white-dwarf';
        sun.whiteDwarfAtSim = simTime;
        sun.mass *= 0.1;
        sun.radius = 28 + Math.cbrt(sun.mass / 1000) * 4;
        spawnCollapseParticles(sun);
        const el = document.getElementById('mass-val-' + sun.id);
        if (el) el.textContent = sun.mass.toFixed(0);
        triggerMergeFlash();
      }
      continue;
    }

    // Star afterlife toggle: when disabled, freeze main-sequence stars so
    // they never leave the main sequence. Existing post-MS phases (red giant,
    // white dwarf, supernova, black hole, …) above continue normally so
    // toggling mid-game doesn't strand a star in a partial phase.
    if (!starAfterlifeEnabled) {
      if (sun.stellarPhase === 'transitioning' || sun.stellarPhase === 'expanding') {
        sun.stellarPhase = 'main-sequence';
      }
      if (sun.stellarPhase === 'main-sequence') {
        sun.createdAtSim = simTime; // hold the aging clock at zero
      }
      continue;
    }

    const mass = sun.mass;
    const elapsed = (simTime - sun.createdAtSim) / 1000;

    // Path D: mass > 100000 → direct collapse to a black hole, skipping supernova
    if (mass > 100000) {
      if (elapsed >= 5) {
        if (Math.random() < 0.1) {
          // 10% chance: become a blue super giant instead of collapsing
          sun.stellarPhase = 'blue-super-giant';
          sun.phaseAtSim = simTime;
        } else {
          sun.stellarPhase = 'black-hole';
          sun.radius = 12 + Math.cbrt(sun.mass / 1000) * 3;
          sun.phaseAtSim = simTime;
          sun.accretionRing = [];
        }
        triggerMergeFlash();
      }
      continue;
    }

    // Path C: mass 2501-100000 → supernova. Lifespan from spectral class.
    // O-type stars (mass 16,000+) get a 10% chance to become a Wolf-Rayet
    // first: they shed 2/3 of their mass as their outer layers blow off,
    // then explode as a supernova when the Wolf-Rayet phase ends.
    if (mass >= 2501) {
      const snSec = getSpectralLifespanSec(mass) ?? 120;
      if (elapsed >= snSec) {
        const isOType = mass >= 16000 && mass <= 100000;
        if (isOType && Math.random() < 0.1) {
          // 10% Wolf-Rayet
          sun.stellarPhase = 'wolf-rayet';
          sun.phaseAtSim = simTime;
          sun.wolfRayetStartMass = sun.mass;
          sun.mass = sun.mass / 3;       // lose 2/3 of the mass
          sun.radius = 28 + Math.cbrt(sun.mass / 1000) * 4;
          sun.wolfRayetDuration = getWolfRayetDurationSec(sun.wolfRayetStartMass);
          const el = document.getElementById('mass-val-' + sun.id);
          if (el) el.textContent = sun.mass.toFixed(0);
        } else if (Math.random() < 0.1) {
          // 10% chance: become a blue super giant instead of going supernova
          sun.stellarPhase = 'blue-super-giant';
          sun.phaseAtSim = simTime;
        } else {
          sun.stellarPhase = 'supernova';
          sun.phaseAtSim = simTime;
        }
        triggerMergeFlash();
      }
      continue;
    }
    // Path B: mass 501-2500 → red giant. Lifespan from spectral class.
    if (mass >= 501 && mass <= 2500) {
      const rgSec = getSpectralLifespanSec(mass) ?? (4 * 60);
      if (elapsed >= rgSec) {
        sun.stellarPhase = 'red-giant';
        sun.redGiantAtSim = simTime;
        // 10% of red giants are actually red super giants — 10× larger.
        if (sun.redSuperGiant === undefined && Math.random() < 0.1) {
          sun.redSuperGiant = true;
        }
      } else if (elapsed >= rgSec - 20) {
        // 10% one-time roll: pause expansion as a K super giant for 60 s
        if (sun.kSuperRolled === undefined) {
          sun.kSuperRolled = true;
          if (Math.random() < 0.1) {
            sun.stellarPhase = 'k-super-giant';
            sun.kSuperAtSim = simTime;
            continue;
          }
        }
        sun.stellarPhase = 'expanding';
      }
      continue;
    }
    // Path A: mass 80-500 → white dwarf. Lifespan from spectral class.
    if (mass >= 80 && mass <= 500) {
      const wdSec = getSpectralLifespanSec(mass) ?? (10 * 60);
      if (elapsed >= wdSec) {
        sun.stellarPhase = 'white-dwarf';
        sun.whiteDwarfAtSim = simTime;
        sun.mass *= 0.2;
        sun.radius = 28 + Math.cbrt(sun.mass / 1000) * 4;
        const el = document.getElementById('mass-val-' + sun.id);
        if (el) el.textContent = sun.mass.toFixed(0);
      } else if (elapsed >= wdSec - 30) {
        sun.stellarPhase = 'transitioning';
      }
    }
  }
}

// Spawn collapse shell particles
function spawnCollapseParticles(sun) {
  const particles = [];
  for (let i = 0; i < 24; i++) {
    const angle = (i / 24) * Math.PI * 2;
    const speed = 1.5 + Math.random() * 2;
    particles.push({ x: sun.x, y: sun.y, vx: Math.cos(angle)*speed, vy: Math.sin(angle)*speed, life: 1 });
  }
  mergeEffects.push({ x: sun.x, y: sun.y, particles, age: 0, maxAge: 60, color: '#ff6644' });
}

// Spawn a mini solar system from nebula
function spawnSolarSystem(cx, cy) {
  const newMass = 200 + Math.random() * 300;
  const sunRadius = 28 + Math.cbrt(newMass / 1000) * 4;
  const sunPos = findFreeSpawnPos(cx, cy, sunRadius);
  const newSun = {
    id: 'sun-' + nextSunId, name: 'Star ' + nextSunId, isSun: true,
    x: sunPos.x, y: sunPos.y, vx: 0, vy: 0,
    mass: newMass, radius: sunRadius, color: getStarColor(newMass),
    trail: [], velMul: 1, createdAtSim: simTime, stellarPhase: 'main-sequence'
  };
  bodies.push(newSun);
  nextSunId++;
  const numPlanets = 2 + Math.floor(Math.random() * 3);
  for (let i = 0; i < numPlanets; i++) {
    const dist = 60 + i * 50 + Math.random() * 30;
    const angle = Math.random() * Math.PI * 2;
    const pColor = PALETTE[Math.floor(Math.random() * PALETTE.length)];
    const pMass = 0.5 + Math.random() * 5;
    const pRadius = 3 + Math.cbrt(pMass) * 2.2;
    const pos = findFreeSpawnPos(sunPos.x + Math.cos(angle) * dist, sunPos.y + Math.sin(angle) * dist, pRadius);
    const actDx = pos.x - sunPos.x, actDy = pos.y - sunPos.y;
    const actDist = Math.sqrt(actDx * actDx + actDy * actDy);
    const actAngle = Math.atan2(actDy, actDx);
    const orbV = actDist > 0 ? Math.sqrt(G_BASE * newSun.mass / actDist) : 0;
    bodies.push({
      id: 'planet-' + nextPlanetId, name: 'Planet ' + nextPlanetId, isSun: false,
      x: pos.x, y: pos.y,
      vx: -Math.sin(actAngle) * orbV, vy: Math.cos(actAngle) * orbV,
      mass: pMass, radius: pRadius,
      color: pColor, trail: [], velMul: 1
    });
    nextPlanetId++;
  }
  buildControls();
}

function triggerMergeFlash() {
  const flash = document.getElementById('merge-flash');
  if (flash) { flash.classList.add('active'); setTimeout(() => flash.classList.remove('active'), 200); }
}

// Map a star's mass to a stellar-class-style color: red → orange → yellow → light blue → dark blue
function getStarColor(mass) {
  const stops = [
    [100,   [255,  68,  68]],  // red
    [1000,  [255, 150,  60]],  // orange
    [2500,  [255, 220,  80]],  // yellow
    [5000,  [170, 200, 255]],  // light blue
    [10000, [ 70, 100, 220]]   // dark blue
  ];
  if (mass <= stops[0][0]) return rgbToHex(stops[0][1]);
  if (mass >= stops[stops.length - 1][0]) return rgbToHex(stops[stops.length - 1][1]);
  for (let i = 0; i < stops.length - 1; i++) {
    const m0 = stops[i][0], m1 = stops[i + 1][0];
    if (mass >= m0 && mass <= m1) {
      const t = (mass - m0) / (m1 - m0);
      const c0 = stops[i][1], c1 = stops[i + 1][1];
      return rgbToHex([
        Math.round(c0[0] + (c1[0] - c0[0]) * t),
        Math.round(c0[1] + (c1[1] - c0[1]) * t),
        Math.round(c0[2] + (c1[2] - c0[2]) * t)
      ]);
    }
  }
  return rgbToHex(stops[0][1]);
}

function rgbToHex(rgb) {
  return '#' + rgb.map(v => v.toString(16).padStart(2, '0')).join('');
}

// Compact display for masses that span 0.1 → 1e14
function formatMass(m) {
  if (!isFinite(m)) return '∞';
  if (m >= 1e5) return m.toExponential(2);
  if (m >= 1000) return Math.round(m).toString();
  return m.toFixed(1);
}

function getSunPhase(sun) {
  return sun.stellarPhase || 'main-sequence';
}

function getEffectiveRadius(b) {
  if (!b.isSun) return planetDisplayRadius(b);
  const phase = getSunPhase(b);
  if (phase === 'blue-super-giant') return b.radius * 30;
  if (phase === 'red-giant' || phase === 'expanding') {
    const rgFactor = getRedGiantFactor(b);
    if (phase === 'red-giant' || rgFactor > 0) {
      // Match the visible star disc, not the fuzzy outer corona.
      // Red super giants are 10× larger.
      const superMul = b.redSuperGiant ? 10 : 1;
      return b.radius * (1 + rgFactor * 2.5) * superMul;
    }
  }
  return b.radius;
}

// Spawn-position guard: no new body is allowed to overlap an existing body.
// `newRadius` is the effective (visual) radius of what we're about to spawn.
function isPositionFree(x, y, newRadius) {
  for (const b of bodies) {
    const dx = b.x - x, dy = b.y - y;
    const minDist = getEffectiveRadius(b) + newRadius + 10;
    if (dx * dx + dy * dy < minDist * minDist) return false;
  }
  return true;
}

function findFreeSpawnPos(cx, cy, newRadius) {
  if (isPositionFree(cx, cy, newRadius)) return { x: cx, y: cy };
  // Walk outward from the requested point in random directions, growing
  // the search radius each attempt. Gives up after 80 tries and returns
  // the requested point as a fallback (useful for super-massive named BHs).
  for (let attempt = 1; attempt <= 80; attempt++) {
    const angle = Math.random() * Math.PI * 2;
    const radius = (newRadius + 30) * (1 + attempt * 0.25);
    const x = cx + Math.cos(angle) * radius;
    const y = cy + Math.sin(angle) * radius;
    if (isPositionFree(x, y, newRadius)) return { x, y };
  }
  return { x: cx, y: cy };
}

function getSunEvolutionFactor(sun) {
  const phase = getSunPhase(sun);
  if (phase === 'black-dwarf') return 2;
  if (phase === 'white-dwarf') {
    if (sun.whiteDwarfAtSim != null) {
      const sinceWD = (simTime - sun.whiteDwarfAtSim) / 1000;
      return 1 + Math.min(sinceWD / 3600, 1);
    }
    return 1;
  }
  if (phase === 'red-giant' || phase === 'expanding' || phase === 'collapsing') return 0;
  if (phase === 'supernova' || phase === 'neutron-star' || phase === 'dormant-neutron-star' || phase === 'wolf-rayet' || phase === 'black-hole' || phase === 'evaporating' || phase === 'nebula') return 0;
  if (phase === 'transitioning') {
    if (sun.createdAtSim == null) return 0;
    const mass = sun.mass;
    if (mass < 80 || mass > 500) return 0;
    const elapsed = (simTime - sun.createdAtSim) / 1000;
    const wdSec = getSpectralLifespanSec(mass) ?? (10 * 60);
    const start = Math.max(0, wdSec - 30);
    if (elapsed >= start) return Math.min((elapsed - start) / (wdSec - start), 1);
  }
  return 0;
}

function getRedGiantFactor(sun) {
  const phase = getSunPhase(sun);
  if (phase === 'red-giant' && sun.redGiantAtSim != null) {
    return Math.min((simTime - sun.redGiantAtSim) / 10000, 1);
  }
  if (phase === 'expanding' && sun.createdAtSim != null) {
    const mass = sun.mass;
    if (mass < 501 || mass > 2500) return 0;
    const elapsed = (simTime - sun.createdAtSim) / 1000;
    const rgSec = getSpectralLifespanSec(mass) ?? (4 * 60);
    const start = Math.max(0, rgSec - 20);
    if (elapsed >= start) return Math.min((elapsed - start) / (rgSec - start), 1) * 0.5;
  }
  return 0;
}

function getPhaseLabel(sun) {
  const phase = getSunPhase(sun);
  // Input is now in MONTHS (post-rescale: 1× speed = 1 sim month / real sec).
  // Output prefers years with a scale suffix; falls back to "mo" only below a
  // year, since the user-facing star lifespans are all measured in years.
  const fmtTime = (months) => {
    if (months < 0 || !isFinite(months)) months = 0;
    const yrs = months / 12;
    if (yrs >= 1e12) return (yrs / 1e12).toFixed(2) + ' T yr';
    if (yrs >= 1e9)  return (yrs / 1e9).toFixed(2) + ' B yr';
    if (yrs >= 1e6)  return (yrs / 1e6).toFixed(2) + ' M yr';
    if (yrs >= 1e3)  return (yrs / 1e3).toFixed(2) + ' k yr';
    if (yrs >= 1)    return yrs.toFixed(1) + ' yr';
    return Math.round(months) + ' mo';
  };

  if (phase === 'black-dwarf') return '● Black Dwarf';

  if (phase === 'white-dwarf') {
    if (sun.whiteDwarfAtSim != null) {
      const remaining = 3600 - (simTime - sun.whiteDwarfAtSim) / 1000;
      return '✦ White Dwarf · ' + fmtTime(remaining) + ' to black dwarf';
    }
    return '✦ White Dwarf';
  }

  if (phase === 'transitioning') {
    if (sun.createdAtSim != null && sun.mass >= 80 && sun.mass <= 500) {
      const elapsed = (simTime - sun.createdAtSim) / 1000;
      const whiteDwarfSec = getSpectralLifespanSec(sun.mass) ?? (10 * 60);
      return '⚡ Collapsing · ' + fmtTime(whiteDwarfSec - elapsed) + ' left';
    }
  }
  if (phase === 'collapsing') return '💥 Collapsing to White Dwarf';
  if (phase === 'k-super-giant') {
    if (sun.kSuperAtSim != null) {
      const dur = sun.kSuperDuration ?? getKSuperGiantDurationSec(sun.mass);
      const remaining = dur - (simTime - sun.kSuperAtSim) / 1000;
      return '🟠 K Super Giant · ' + fmtTime(remaining) + ' left';
    }
    return '🟠 K Super Giant';
  }
  if (phase === 'red-giant') {
    // Betelgeuse is held in this phase indefinitely — show that instead of
    // the misleading collapse countdown.
    if (isBetelgeuseLike(sun)) return '🔴 Red Super Giant · stable';
    const label = sun.redSuperGiant ? '🔴 Red Super Giant' : '🔴 Red Giant';
    if (sun.redGiantAtSim != null) {
      const dur = sun.redGiantDuration ?? (sun.redSuperGiant
        ? getRedSuperGiantDurationSec()
        : getRedGiantDurationSec(sun.mass));
      const remaining = dur - (simTime - sun.redGiantAtSim) / 1000;
      return label + ' · ' + fmtTime(remaining) + ' left';
    }
    return label;
  }
  if (phase === 'blue-super-giant') {
    if (sun.phaseAtSim != null) {
      const dur = sun.bsgDuration ?? getBlueSuperGiantDurationSec(sun.mass);
      const remaining = dur - (simTime - sun.phaseAtSim) / 1000;
      return '🔵 Blue Super Giant · ' + fmtTime(remaining) + ' left';
    }
    return '🔵 Blue Super Giant';
  }
  if (phase === 'wolf-rayet') {
    if (sun.phaseAtSim != null) {
      const dur = sun.wolfRayetDuration ?? getWolfRayetDurationSec((sun.wolfRayetStartMass || sun.mass * 3));
      const remaining = dur - (simTime - sun.phaseAtSim) / 1000;
      return '✨ Wolf-Rayet (20k–210k K) · ' + fmtTime(remaining) + ' left';
    }
    return '✨ Wolf-Rayet';
  }
  if (phase === 'expanding') {
    if (sun.createdAtSim != null && sun.mass >= 501 && sun.mass <= 2500) {
      const elapsed = (simTime - sun.createdAtSim) / 1000;
      const rgSec = getSpectralLifespanSec(sun.mass) ?? (4 * 60);
      return '⚡ Expanding · ' + fmtTime(rgSec - elapsed) + ' to red giant';
    }
  }
  if (phase === 'supernova') return '💥 SUPERNOVA!';
  if (phase === 'neutron-star') {
    let label;
    if (sun.magnetar) label = '⚡ Magnetar · 10¹¹ T';
    else if (sun.strangeMatter) label = '🟢 Strange Neutron Star';
    else label = '💫 Neutron Star';
    if (sun.phaseAtSim != null) {
      const dur = sun.neutronBeamDuration ?? 1800; // ~30 min if unset
      const remaining = dur - (simTime - sun.phaseAtSim) / 1000;
      return label + ' · ' + fmtTime(remaining) + ' to beam stops';
    }
    return label;
  }
  if (phase === 'dormant-neutron-star') {
    const label = sun.magnetar ? '⚡ Dormant Magnetar'
                : sun.strangeMatter ? '🟢 Dormant Strange NS'
                : '💫 Cold Neutron Star';
    if (sun.neutronStartSim != null) {
      if (sun.neutronTotalLifespan == null) sun.neutronTotalLifespan = getNeutronTotalLifespanSec();
      const remaining = sun.neutronTotalLifespan - (simTime - sun.neutronStartSim) / 1000;
      return label + ' · ' + fmtTime(remaining) + ' to black dwarf';
    }
    return label;
  }
  if (phase === 'black-hole') {
    if (sun.phaseAtSim != null) {
      const lifespan = sun.bhLifespan ?? getBlackHoleLifespanSec(sun.mass);
      const remaining = lifespan - (simTime - sun.phaseAtSim) / 1000;
      return '🕳️ Black Hole · ' + fmtTime(remaining) + ' to evaporate';
    }
    return '🕳️ Black Hole';
  }
  if (phase === 'evaporating') {
    if (sun.phaseAtSim != null) {
      const remaining = 1800 - (simTime - sun.phaseAtSim) / 1000;
      return '🕳️ Evaporating · ' + fmtTime(remaining) + ' left';
    }
    return '🕳️ Evaporating';
  }
  if (phase === 'nebula') return '🌫️ Nebula';

  // Spectral class prefix for the main-sequence label.
  // Priority where ranges overlap: O > B > A > F > G.
  const isOType = sun.mass >= 16000 && sun.mass <= 100000;
  const isBType = !isOType && sun.mass >= 2000 && sun.mass <= 18000;
  const isAType = !isOType && !isBType && sun.mass >= 1400 && sun.mass <= 2100;
  const isFType = !isOType && !isBType && !isAType && sun.mass >= 1040 && sun.mass <= 1400;
  const isGType = !isOType && !isBType && !isAType && !isFType && sun.mass >= 800 && sun.mass <= 1400;
  const isKType = !isOType && !isBType && !isAType && !isFType && !isGType && sun.mass >= 450 && sun.mass <= 800;
  const isMType = !isOType && !isBType && !isAType && !isFType && !isGType && !isKType && sun.mass >= 80 && sun.mass <= 600;
  const mainLabel = isOType ? '🔵 O Type (30,000–50,000 K)'
                  : isBType ? '🔷 B Type (2,000–30,000 K)'
                  : isAType ? '🤍 A Type (7,300–10,000 K)'
                  : isFType ? '🟡 F Type (6,000–7,500 K)'
                  : isGType ? '🟨 G Type (5,300–6,000 K)'
                  : isKType ? '🟠 K Type (3,900–5,300 K)'
                  : isMType ? '🔴 M Type (2,500–3,700 K)'
                  : '☀ Main Sequence';

  // Main sequence — countdown driven by spectral-class lifespan.
  if (sun.mass > 100000 && sun.createdAtSim != null) {
    const elapsed = (simTime - sun.createdAtSim) / 1000;
    return mainLabel + ' · ' + fmtTime(5 - elapsed) + ' to black hole';
  }
  if (sun.createdAtSim != null) {
    const lifespan = getSpectralLifespanSec(sun.mass);
    if (lifespan != null) {
      const elapsed = (simTime - sun.createdAtSim) / 1000;
      const fate = sun.mass >= 2501 ? ' to supernova'
                 : sun.mass >= 501  ? ' to red giant'
                 : ' left';
      return mainLabel + ' · ' + fmtTime(lifespan - elapsed) + fate;
    }
  }
  return mainLabel;
}

function drawSunCorona(sun, t) {
  const evo = getSunEvolutionFactor(sun);
  const phase = getSunPhase(sun);
  const rgFactor = getRedGiantFactor(sun);

  // Blue super giant: 30× radius hot blue ball with a broad cool halo
  if (phase === 'blue-super-giant') {
    const bsgScale = 30;
    const pulse = 1 + 0.06 * Math.sin(t * 0.0025);
    const outerR = sun.radius * bsgScale * 1.6 * pulse;
    const coreR  = sun.radius * bsgScale * pulse;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    const g1 = ctx.createRadialGradient(sun.x, sun.y, sun.radius * 0.5, sun.x, sun.y, outerR);
    g1.addColorStop(0,   'rgba(120,170,255,0.45)');
    g1.addColorStop(0.4, 'rgba(60,110,255,0.25)');
    g1.addColorStop(0.7, 'rgba(30,70,220,0.08)');
    g1.addColorStop(1,   'rgba(15,40,180,0)');
    ctx.fillStyle = g1;
    ctx.beginPath();
    ctx.arc(sun.x, sun.y, outerR, 0, Math.PI * 2);
    ctx.fill();
    const g2 = ctx.createRadialGradient(sun.x, sun.y, 0, sun.x, sun.y, coreR);
    g2.addColorStop(0,   'rgba(170,210,255,0.95)');
    g2.addColorStop(0.4, 'rgba(80,140,255,0.65)');
    g2.addColorStop(1,   'rgba(30,80,220,0)');
    ctx.fillStyle = g2;
    ctx.beginPath();
    ctx.arc(sun.x, sun.y, coreR, 0, Math.PI * 2);
    ctx.fill();
    ctx.restore();
    return;
  }

  // Red giant: expanded deep red corona (10× scale for red super giants)
  if (phase === 'red-giant' || (phase === 'expanding' && rgFactor > 0)) {
    const rgPulse = 1 + 0.12 * Math.sin(t * 0.002);
    const superMul = sun.redSuperGiant ? 10 : 1;
    const expandScale = (6 + rgFactor * 6) * superMul;
    const r = sun.radius * expandScale * rgPulse;
    const innerR = sun.radius * 3 * superMul;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    const g1 = ctx.createRadialGradient(sun.x, sun.y, sun.radius * 0.5 * superMul, sun.x, sun.y, r);
    g1.addColorStop(0, 'rgba(255,60,20,0.3)');
    g1.addColorStop(0.4, 'rgba(220,30,10,0.15)');
    g1.addColorStop(0.7, 'rgba(180,10,0,0.05)');
    g1.addColorStop(1, 'rgba(120,0,0,0)');
    ctx.fillStyle = g1;
    ctx.beginPath();
    ctx.arc(sun.x, sun.y, r, 0, Math.PI * 2);
    ctx.fill();
    const g2 = ctx.createRadialGradient(sun.x, sun.y, 0, sun.x, sun.y, innerR);
    g2.addColorStop(0, 'rgba(255,180,80,0.7)');
    g2.addColorStop(0.5, 'rgba(255,80,30,0.3)');
    g2.addColorStop(1, 'rgba(200,20,0,0)');
    ctx.fillStyle = g2;
    ctx.beginPath();
    ctx.arc(sun.x, sun.y, innerR, 0, Math.PI * 2);
    ctx.fill();
    ctx.restore();
    return;
  }

  // Collapsing: red giant shrinking rapidly
  if (phase === 'collapsing') {
    const since = sun.phaseAtSim ? (simTime - sun.phaseAtSim) / 1000 : 0;
    const shrink = Math.max(0.2, 1 - since / 2);
    const r = sun.radius * (3 * shrink);
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    const g = ctx.createRadialGradient(sun.x, sun.y, 0, sun.x, sun.y, r);
    g.addColorStop(0, `rgba(255,200,100,${0.8 * shrink})`);
    g.addColorStop(0.5, `rgba(255,60,20,${0.3 * shrink})`);
    g.addColorStop(1, 'rgba(120,0,0,0)');
    ctx.fillStyle = g;
    ctx.beginPath();
    ctx.arc(sun.x, sun.y, r, 0, Math.PI * 2);
    ctx.fill();
    ctx.restore();
    return;
  }

  // Supernova: bright expanding white flash
  if (phase === 'supernova') {
    const since = sun.phaseAtSim ? (simTime - sun.phaseAtSim) / 1000 : 0;
    const expand = since / 3;
    const r = sun.radius * (2 + expand * 15);
    const alpha = Math.max(0, 1 - expand * 0.7);
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    const g = ctx.createRadialGradient(sun.x, sun.y, 0, sun.x, sun.y, r);
    g.addColorStop(0, `rgba(255,255,255,${alpha})`);
    g.addColorStop(0.2, `rgba(255,220,150,${alpha * 0.7})`);
    g.addColorStop(0.5, `rgba(255,100,50,${alpha * 0.3})`);
    g.addColorStop(1, 'rgba(255,50,0,0)');
    ctx.fillStyle = g;
    ctx.beginPath();
    ctx.arc(sun.x, sun.y, r, 0, Math.PI * 2);
    ctx.fill();
    ctx.restore();
    return;
  }

  // Wolf-Rayet: hot bare-core star with outer layers blowing off as dust.
  // Each frame we emit a few outward-streaming ejecta particles so the
  // "layers dust away" effect runs continuously through the phase. The
  // core itself is a small, intensely hot blue-white sphere.
  if (phase === 'wolf-rayet') {
    const since = sun.phaseAtSim ? (simTime - sun.phaseAtSim) / 1000 : 0;
    const dur = sun.wolfRayetDuration || 60;
    // Outer ejecta cloud shrinks from 4× radius down toward the bare core.
    const progress = Math.max(0, Math.min(1, since / dur));
    const cloudR = sun.radius * (4 - 3 * progress);
    const coreR  = sun.radius;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    // Dusty ejecta halo
    const g1 = ctx.createRadialGradient(sun.x, sun.y, coreR * 0.6, sun.x, sun.y, cloudR);
    g1.addColorStop(0,   'rgba(220,235,255,0.55)');
    g1.addColorStop(0.4, 'rgba(160,200,255,0.25)');
    g1.addColorStop(0.7, 'rgba(120,160,220,0.10)');
    g1.addColorStop(1,   'rgba(80,120,200,0)');
    ctx.fillStyle = g1;
    ctx.beginPath();
    ctx.arc(sun.x, sun.y, cloudR, 0, Math.PI * 2);
    ctx.fill();
    // Bare hot core
    const g2 = ctx.createRadialGradient(sun.x, sun.y, 0, sun.x, sun.y, coreR * 1.6);
    g2.addColorStop(0,   'rgba(255,255,255,1)');
    g2.addColorStop(0.3, 'rgba(220,235,255,0.9)');
    g2.addColorStop(0.7, 'rgba(140,180,255,0.5)');
    g2.addColorStop(1,   'rgba(80,120,220,0)');
    ctx.fillStyle = g2;
    ctx.beginPath();
    ctx.arc(sun.x, sun.y, coreR * 1.6, 0, Math.PI * 2);
    ctx.fill();
    ctx.restore();
    // Spawn a few dust particles streaming outward each frame.
    if (!paused && mergeEffects.length < 200) {
      const n = 2;
      const particles = [];
      for (let i = 0; i < n; i++) {
        const a = Math.random() * Math.PI * 2;
        const sp = 1.2 + Math.random() * 1.8;
        particles.push({
          x: sun.x + Math.cos(a) * coreR * 1.2,
          y: sun.y + Math.sin(a) * coreR * 1.2,
          vx: Math.cos(a) * sp,
          vy: Math.sin(a) * sp,
          life: 1
        });
      }
      mergeEffects.push({ x: sun.x, y: sun.y, particles, age: 0, maxAge: 80, color: '#a8c8ff' });
    }
    return;
  }

  // Neutron star: tiny intensely bright pulsating glow.
  // Strange-matter variant gets a slowly-rotating dipole magnetic field and pulsar jets.
  // Magnetar variant has the same shape but a magnetic field 20× larger.
  // Dormant variant ('dormant-neutron-star') uses the same core + field/halo
  // rendering but no rotating beam.
  if (phase === 'neutron-star' || phase === 'dormant-neutron-star') {
    const dormant = phase === 'dormant-neutron-star';
    const pulse = 1 + 0.3 * Math.sin(t * 0.02);
    if (sun.strangeMatter || sun.magnetar) {
      const isMagnetar = !!sun.magnetar;
      const fieldScale = isMagnetar ? 200 : 1;
      // Magnetar = magenta/purple; strange-matter neutron star = green
      const pal = isMagnetar
        ? { beam: '255,180,255', beamHot: '255,240,255', field: '220,120,255', coreIn: '255,180,255', coreOut: '160,60,200' }
        : { beam: '180,255,180', beamHot: '240,255,240', field: '120,220,120', coreIn: '180,255,180', coreOut: '60,200,60' };

      const axisAngle = t * 0.0008;
      ctx.save();
      ctx.globalCompositeOperation = 'lighter';
      ctx.translate(sun.x, sun.y);
      ctx.rotate(axisAngle);

      // Pulsar jets along the magnetic axis (length scaled with the field)
      // Strange-NS jets are much longer than the dipole-field rings;
      // magnetar still scales by fieldScale (200×) on top of the magnetar base.
      // Suppressed on dormant neutron stars (beams have shut off).
      if (!dormant) {
        const beamBase   = isMagnetar ?  90 : 320;
        const beamWobble = isMagnetar ?  30 : 80;
        const beamLen = (beamBase + beamWobble * Math.sin(t * 0.012)) * fieldScale;
        const beamG = ctx.createLinearGradient(0, -beamLen, 0, beamLen);
        beamG.addColorStop(0,    `rgba(${pal.beam},0)`);
        beamG.addColorStop(0.45, `rgba(${pal.beam},0.7)`);
        beamG.addColorStop(0.5,  `rgba(${pal.beamHot},0.95)`);
        beamG.addColorStop(0.55, `rgba(${pal.beam},0.7)`);
        beamG.addColorStop(1,    `rgba(${pal.beam},0)`);
        ctx.fillStyle = beamG;
        const beamWidth = isMagnetar ? 14 : 6;
        ctx.fillRect(-beamWidth / 2, -beamLen, beamWidth, beamLen * 2);
      }

      // Dipole field lines: two stacked elliptical lobes (top + bottom) per ring
      for (let i = 1; i <= 5; i++) {
        const lobeH = (8 + i * 11) * fieldScale;
        const lobeW = lobeH * (0.3 + i * 0.05);
        const alpha = (isMagnetar ? 0.85 - i * 0.1 : 0.55 - i * 0.07) * pulse;
        ctx.strokeStyle = `rgba(${pal.field},${alpha})`;
        ctx.lineWidth = isMagnetar ? 4 : 1.4;
        // Subtle inner-lobe fill on magnetar gives the field some body
        const fillAlpha = isMagnetar ? alpha * 0.22 : 0;
        if (fillAlpha > 0) ctx.fillStyle = `rgba(${pal.field},${fillAlpha})`;
        ctx.beginPath();
        ctx.ellipse(0, -lobeH / 2, lobeW, lobeH / 2, 0, 0, Math.PI * 2);
        if (fillAlpha > 0) ctx.fill();
        ctx.stroke();
        ctx.beginPath();
        ctx.ellipse(0,  lobeH / 2, lobeW, lobeH / 2, 0, 0, Math.PI * 2);
        if (fillAlpha > 0) ctx.fill();
        ctx.stroke();
      }
      ctx.restore();

      // Bright core (un-rotated so it stays centered)
      ctx.save();
      ctx.globalCompositeOperation = 'lighter';
      const coreG = ctx.createRadialGradient(sun.x, sun.y, 0, sun.x, sun.y, 14 * pulse);
      coreG.addColorStop(0, 'rgba(255,255,255,1)');
      coreG.addColorStop(0.3, `rgba(${pal.coreIn},0.85)`);
      coreG.addColorStop(1, `rgba(${pal.coreOut},0)`);
      ctx.fillStyle = coreG;
      ctx.beginPath();
      ctx.arc(sun.x, sun.y, 14 * pulse, 0, Math.PI * 2);
      ctx.fill();
      ctx.restore();
      return;
    }

    // Pulsar beams: magnetic axis tilted ~30° from a vertical rotation axis.
    // As the star spins, the magnetic axis traces a cone in 3D — projecting
    // to 2D, the beam angle wobbles between ±tilt and each beam's length
    // foreshortens as it dips toward/away from the viewer's eyepoint.
    // Default: 700 RPM. Easter egg: neutron stars named after real long-period
    // radio transients spin down from the normal pulsar rate to their measured
    // periods over LPT_SPINDOWN_MS. The angle is integrated analytically so
    // the rotation stays continuous through the transition.
    const LPT_PERIODS_MS = {
      'askap j1935+2148': 54 * 60 * 1000,            // 54 min
      'askap j1839-075':  6.45 * 60 * 60 * 1000      // 6.45 h
    };
    const LPT_SPINDOWN_MS = 30000; // 30 s of anim time to slow from 700 RPM to LPT rate
    const DEFAULT_NS_SPIN = 700 * 2 * Math.PI / 60000; // ≈ 0.0733 rad/ms
    const lptPeriod = LPT_PERIODS_MS[(sun.name || '').trim().toLowerCase()];
    let nsSpin;
    if (lptPeriod) {
      // First time this body looks like an LPT, snapshot the start of the
      // spin-down: anim time and the angle the body had so it doesn't jump.
      if (sun.lptStartAnim == null) {
        sun.lptStartAnim = t;
        sun.lptStartAngle = t * DEFAULT_NS_SPIN;
      }
      const elapsed = t - sun.lptStartAnim;
      const R0 = DEFAULT_NS_SPIN;
      const R1 = 2 * Math.PI / lptPeriod;
      const lnR = Math.log(R1 / R0); // negative because R1 < R0
      if (elapsed <= LPT_SPINDOWN_MS) {
        // Exponential decay: spinRate(t') = R0 · (R1/R0)^(t'/T)
        // Integrated from 0 to elapsed:
        const factor = (Math.pow(R1 / R0, elapsed / LPT_SPINDOWN_MS) - 1);
        nsSpin = sun.lptStartAngle + R0 * LPT_SPINDOWN_MS * factor / lnR;
      } else {
        // After spin-down: constant rotation at R1
        const angleAtEnd = R0 * LPT_SPINDOWN_MS * (R1 / R0 - 1) / lnR;
        nsSpin = sun.lptStartAngle + angleAtEnd + R1 * (elapsed - LPT_SPINDOWN_MS);
      }
    } else {
      nsSpin = t * DEFAULT_NS_SPIN;
    }
    const tilt = 0.25; // ~14° magnetic-axis offset from the spin axis
    const sinTilt = Math.sin(tilt);
    const cosTilt = Math.cos(tilt);
    const cosTheta = Math.cos(nsSpin);
    const sinTheta = Math.sin(nsSpin);
    // 2D-projected angle of the magnetic axis (measured from vertical)
    const beamAngle = Math.atan2(sinTilt * cosTheta, cosTilt);
    // Foreshortening: how much of the cone-tip length we see in the plane
    const lenFactor = Math.sqrt(cosTilt * cosTilt + sinTilt * sinTilt * cosTheta * cosTheta);
    const fullBeamLen = (400 + 80 * Math.sin(t * 0.015)) * lenFactor;
    // Top beam brightens when its tip swings toward the viewer (+Z);
    // bottom beam does the opposite. Squared so the flash spikes.
    const topZ = Math.max(0, sinTheta);
    const botZ = Math.max(0, -sinTheta);
    const topFlash = 0.35 + 0.65 * topZ * topZ;
    const botFlash = 0.35 + 0.65 * botZ * botZ;
    const baseHalfW = 6;
    const tipHalfW = 0.8;

    // Dormant neutron stars have shut their beams off — render only the core.
    if (!dormant) {
      ctx.save();
      ctx.globalCompositeOperation = 'lighter';
      ctx.translate(sun.x, sun.y);
      ctx.rotate(beamAngle);

      // Top beam — tapered triangle from base (origin) to tip
      const topG = ctx.createLinearGradient(0, 0, 0, -fullBeamLen);
      topG.addColorStop(0,   `rgba(245,250,255,${0.98 * topFlash})`);
      topG.addColorStop(0.3, `rgba(200,220,255,${0.6 * topFlash})`);
      topG.addColorStop(1,   `rgba(180,200,255,0)`);
      ctx.fillStyle = topG;
      ctx.beginPath();
      ctx.moveTo(-baseHalfW, 0);
      ctx.lineTo(-tipHalfW, -fullBeamLen);
      ctx.lineTo( tipHalfW, -fullBeamLen);
      ctx.lineTo( baseHalfW, 0);
      ctx.closePath();
      ctx.fill();

      // Bottom beam — same cone, opposite direction, with its own flash phase
      const botG = ctx.createLinearGradient(0, 0, 0, fullBeamLen);
      botG.addColorStop(0,   `rgba(245,250,255,${0.98 * botFlash})`);
      botG.addColorStop(0.3, `rgba(200,220,255,${0.6 * botFlash})`);
      botG.addColorStop(1,   `rgba(180,200,255,0)`);
      ctx.fillStyle = botG;
      ctx.beginPath();
      ctx.moveTo(-baseHalfW, 0);
      ctx.lineTo(-tipHalfW, fullBeamLen);
      ctx.lineTo( tipHalfW, fullBeamLen);
      ctx.lineTo( baseHalfW, 0);
      ctx.closePath();
      ctx.fill();

      ctx.restore();
    }

    // Bright pulsating core (un-rotated so it stays put while beams sweep)
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    const g = ctx.createRadialGradient(sun.x, sun.y, 0, sun.x, sun.y, 20 * pulse);
    g.addColorStop(0, 'rgba(200,220,255,0.95)');
    g.addColorStop(0.3, 'rgba(100,150,255,0.4)');
    g.addColorStop(1, 'rgba(50,80,200,0)');
    ctx.fillStyle = g;
    ctx.beginPath();
    ctx.arc(sun.x, sun.y, 20 * pulse, 0, Math.PI * 2);
    ctx.fill();
    ctx.restore();
    return;
  }

  // Black hole with spinning accretion ring
  if (phase === 'black-hole' || phase === 'evaporating') {
    let scale = 1;
    if (phase === 'evaporating' && sun.phaseAtSim) {
      scale = Math.max(0.05, 1 - (simTime - sun.phaseAtSim) / 1000 / 1800);
    }
    const bhR = (sun.radius || 12) * scale;
    const cx = sun.x, cy = sun.y;

    // If the BH is too small on screen to draw the elaborate disk without
    // the strokes overflowing the shadow, switch to a simple dot+glow render.
    // Lets the BH shrink naturally with zoom instead of artificially growing.
    const screenBhR = bhR * viewZoom;
    if (screenBhR < 6) {
      const dotR = Math.max(bhR, 1.5 / viewZoom);
      ctx.save();
      // Faint orange glow so it's still locatable on screen
      ctx.globalCompositeOperation = 'lighter';
      const glow = ctx.createRadialGradient(cx, cy, 0, cx, cy, dotR * 3);
      glow.addColorStop(0, `rgba(255,140,60,${0.7 * scale})`);
      glow.addColorStop(0.5, `rgba(255,80,30,${0.2 * scale})`);
      glow.addColorStop(1, 'rgba(0,0,0,0)');
      ctx.fillStyle = glow;
      ctx.beginPath();
      ctx.arc(cx, cy, dotR * 3, 0, Math.PI * 2);
      ctx.fill();
      // Black event horizon dot
      ctx.globalCompositeOperation = 'source-over';
      ctx.fillStyle = '#000';
      ctx.beginPath();
      ctx.arc(cx, cy, dotR, 0, Math.PI * 2);
      ctx.fill();
      ctx.restore();
      return;
    }

    const eventR = bhR * 1.2;
    const photonR = bhR * 1.4;
    // Disk pulled in slightly so the black middle stays clearly visible
    const diskInner = bhR * 2.0;
    const diskOuter = bhR * 4.2;
    const spin = t * 0.0015;
    // Bigger black holes get thicker accretion-disk strokes (instead of more
    // rings, which got too noisy). Log curve, capped at 6×. Uses the raw
    // radius so a small BH zoomed out doesn't pretend to be bigger.
    const thickScale = Math.min(6, Math.max(1, Math.log10(bhR) - 0.5));
    // Stroke widths are interpreted in world units, but world units shrink
    // when the user zooms out. Multiply by 1/viewZoom so the strokes stay a
    // constant size in screen pixels — otherwise huge BHs disappear when
    // zoomed out far enough to see them.
    const pxScale = 1 / viewZoom;

    ctx.save();
    ctx.globalCompositeOperation = 'lighter';

    // Outer atmospheric glow
    {
      const halo = ctx.createRadialGradient(cx, cy, eventR, cx, cy, diskOuter * 1.6);
      halo.addColorStop(0, `rgba(255,120,40,${0.16 * scale})`);
      halo.addColorStop(0.4, `rgba(220,80,20,${0.07 * scale})`);
      halo.addColorStop(1, 'rgba(0,0,0,0)');
      ctx.fillStyle = halo;
      ctx.beginPath();
      ctx.arc(cx, cy, diskOuter * 1.6, 0, Math.PI * 2);
      ctx.fill();
    }

    // Outer top arch — broad, diffuse halo arch (faintest, drawn first).
    // Clipped at diskOuter so no top-arch ring extends past the main disk.
    const outerTopRings = 8;
    for (let i = 0; i < outerTopRings; i++) {
      const tNorm = i / outerTopRings;
      const rx = diskOuter * 0.7 + (diskOuter * 1.0 - diskOuter * 0.7) * tNorm;
      const ry = rx * (0.55 + tNorm * 0.05);
      const cg = Math.round(160 - tNorm * 80);
      const cb = Math.round(60 + tNorm * 20);
      const streak = 0.5 + 0.5 * Math.sin(spin * (2.5 - tNorm) + i * 0.7);
      const alpha = (0.45 - tNorm * 0.3) * scale * streak;
      ctx.strokeStyle = `rgba(255,${cg},${cb},${alpha})`;
      ctx.lineWidth = (1.6 + (1 - tNorm) * 2.5) * scale * pxScale * thickScale;
      ctx.beginPath();
      ctx.ellipse(cx, cy, rx, ry, 0, Math.PI, 2 * Math.PI);
      ctx.stroke();
    }

    // Top arch — gravitationally-lensed back of the disk lifted over the BH
    const archRings = 14;
    for (let i = 0; i < archRings; i++) {
      const tNorm = i / archRings;
      const rx = diskInner + (diskOuter - diskInner) * tNorm;
      const ry = rx * (0.42 + tNorm * 0.08);
      const cg = Math.round(195 - tNorm * 145);
      const cb = Math.round(40 + tNorm * 20);
      const streak = 0.55 + 0.45 * Math.sin(spin * (4 - tNorm * 2) + i * 0.5);
      const alpha = (0.85 - tNorm * 0.55) * scale * streak;
      ctx.strokeStyle = `rgba(255,${cg},${cb},${alpha})`;
      ctx.lineWidth = (2.5 + (1 - tNorm) * 4) * scale * pxScale * thickScale;
      ctx.beginPath();
      ctx.ellipse(cx, cy, rx, ry, 0, Math.PI, 2 * Math.PI);
      ctx.stroke();
    }

    // Inner top arch — secondary lensed image close to the photon ring
    const innerTopRings = 7;
    for (let i = 0; i < innerTopRings; i++) {
      const tNorm = i / innerTopRings;
      const rx = bhR * 1.55 + (bhR * 2.6 - bhR * 1.55) * tNorm;
      const ry = rx * (0.32 + tNorm * 0.05);
      const cg = Math.round(215 - tNorm * 140);
      const cb = Math.round(30 + tNorm * 22);
      const streak = 0.6 + 0.4 * Math.sin(spin * (6 - tNorm * 2) + i * 0.5);
      const alpha = (0.72 - tNorm * 0.4) * scale * streak;
      ctx.strokeStyle = `rgba(255,${cg},${cb},${alpha})`;
      ctx.lineWidth = (1.6 + (1 - tNorm) * 2.2) * scale * pxScale * thickScale;
      ctx.beginPath();
      ctx.ellipse(cx, cy, rx, ry, 0, Math.PI, 2 * Math.PI);
      ctx.stroke();
    }

    // Bottom secondary lensed arch (smaller, from disk wrapping below)
    const botRings = 10;
    for (let i = 0; i < botRings; i++) {
      const tNorm = i / botRings;
      const rx = diskInner * 0.92 + (diskOuter * 0.68 - diskInner * 0.92) * tNorm;
      const ry = rx * (0.26 + tNorm * 0.08);
      const cg = Math.round(180 - tNorm * 130);
      const cb = Math.round(50 + tNorm * 18);
      const streak = 0.5 + 0.5 * Math.sin(-spin * (5 - tNorm * 2) + i * 0.7);
      const alpha = (0.78 - tNorm * 0.5) * scale * streak;
      ctx.strokeStyle = `rgba(255,${cg},${cb},${alpha})`;
      ctx.lineWidth = (1.8 + (1 - tNorm) * 3) * scale * pxScale * thickScale;
      ctx.beginPath();
      ctx.ellipse(cx, cy, rx, ry, 0, 0, Math.PI);
      ctx.stroke();
    }

    // Inner bottom arch — secondary lensed image hugging the photon ring
    const innerBotRings = 6;
    for (let i = 0; i < innerBotRings; i++) {
      const tNorm = i / innerBotRings;
      const rx = bhR * 1.55 + (bhR * 2.2 - bhR * 1.55) * tNorm;
      const ry = rx * (0.18 + tNorm * 0.04);
      const cg = Math.round(200 - tNorm * 130);
      const cb = Math.round(40 + tNorm * 18);
      const streak = 0.55 + 0.45 * Math.sin(-spin * (7 - tNorm * 2) + i * 0.8);
      const alpha = (0.66 - tNorm * 0.38) * scale * streak;
      ctx.strokeStyle = `rgba(255,${cg},${cb},${alpha})`;
      ctx.lineWidth = (1.4 + (1 - tNorm) * 1.9) * scale * pxScale * thickScale;
      ctx.beginPath();
      ctx.ellipse(cx, cy, rx, ry, 0, 0, Math.PI);
      ctx.stroke();
    }

    // Main horizontal accretion disk — fatter flat ellipses, hot inner to cooler outer.
    // BACK half (top of ellipse) drawn here so the event horizon shadow can hide it.
    const diskRings = 16;
    const drawDiskHalf = (halfStart, halfEnd) => {
      for (let i = 0; i < diskRings; i++) {
        const tNorm = i / diskRings;
        const rx = diskInner + (diskOuter - diskInner) * tNorm;
        const ry = rx * 0.13;
        const cg = Math.round(205 - tNorm * 155);
        const cb = Math.round(30 + tNorm * 28);
        const streak = 0.6 + 0.4 * Math.sin(spin * (5 - tNorm * 2) + i * 0.4);
        const alpha = (0.95 - tNorm * 0.55) * scale * streak;
        ctx.strokeStyle = `rgba(255,${cg},${cb},${alpha})`;
        ctx.lineWidth = (3 + (1 - tNorm) * 3) * scale * pxScale * thickScale;
        ctx.beginPath();
        ctx.ellipse(cx, cy, rx, ry, 0, halfStart, halfEnd);
        ctx.stroke();
      }
    };
    // Back half: top of the ellipse (canvas y < cy)
    drawDiskHalf(Math.PI, 2 * Math.PI);

    // Captured particles still spiraling toward the event horizon
    if (sun.accretionRing && sun.accretionRing.length > 0) {
      for (let p = sun.accretionRing.length - 1; p >= 0; p--) {
        const part = sun.accretionRing[p];
        if (!paused) {
          part.angle += part.speed;
          part.orbitR *= 0.9997;
          part.life -= 0.0003;
        }
        if (part.orbitR < bhR * 0.5 || part.life <= 0) {
          sun.accretionRing.splice(p, 1);
          continue;
        }
        const px = cx + Math.cos(part.angle) * part.orbitR;
        const py = cy + Math.sin(part.angle) * part.orbitR * 0.15;
        const alpha = part.life * 0.85;
        const pr = parseInt(part.color.slice(1,3),16) || 255;
        const pg = parseInt(part.color.slice(3,5),16) || 136;
        const pb = parseInt(part.color.slice(5,7),16) || 68;
        ctx.fillStyle = `rgba(${pr},${pg},${pb},${alpha})`;
        ctx.beginPath();
        ctx.arc(px, py, part.size * scale, 0, Math.PI * 2);
        ctx.fill();
        ctx.fillStyle = `rgba(${pr},${pg},${pb},${alpha * 0.3})`;
        ctx.beginPath();
        ctx.arc(px, py, part.size * scale * 2.5, 0, Math.PI * 2);
        ctx.fill();
      }
    }

    // Event horizon shadow — must be opaque black, so switch off additive blend
    ctx.globalCompositeOperation = 'source-over';
    ctx.fillStyle = '#000';
    ctx.beginPath();
    ctx.arc(cx, cy, eventR, 0, Math.PI * 2);
    ctx.fill();

    // FRONT half of the accretion disk: bottom of the ellipse, drawn on top
    // of the shadow so the disk visibly passes in front of the black hole.
    ctx.globalCompositeOperation = 'lighter';
    drawDiskHalf(0, Math.PI);

    // Photon ring — bright thin ring just outside the event horizon
    ctx.globalCompositeOperation = 'lighter';
    ctx.lineWidth = 2 * scale * pxScale;
    ctx.strokeStyle = `rgba(255,220,140,${0.95 * scale})`;
    ctx.beginPath();
    ctx.arc(cx, cy, photonR, 0, Math.PI * 2);
    ctx.stroke();
    ctx.lineWidth = 1 * scale * pxScale;
    ctx.strokeStyle = `rgba(255,150,80,${0.55 * scale})`;
    ctx.beginPath();
    ctx.arc(cx, cy, photonR * 1.08, 0, Math.PI * 2);
    ctx.stroke();

    ctx.restore();
    return;
  }

  // Nebula: colorful expanding cloud
  if (phase === 'nebula') {
    const since = sun.phaseAtSim ? (simTime - sun.phaseAtSim) / 1000 : 0;
    const r = 20 + since * 8;
    const alpha = Math.max(0.05, 1 - since / 25);
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    const colors = [[180,80,255],[80,200,255],[255,120,80]];
    for (let i = 0; i < 3; i++) {
      const c = colors[i];
      const angle = (i / 3) * Math.PI * 2 + since * 0.1;
      const ox = Math.cos(angle) * r * 0.3;
      const oy = Math.sin(angle) * r * 0.3;
      const g = ctx.createRadialGradient(sun.x + ox, sun.y + oy, 0, sun.x + ox, sun.y + oy, r * 0.7);
      g.addColorStop(0, `rgba(${c[0]},${c[1]},${c[2]},${alpha * 0.5})`);
      g.addColorStop(1, `rgba(${c[0]},${c[1]},${c[2]},0)`);
      ctx.fillStyle = g;
      ctx.beginPath();
      ctx.arc(sun.x + ox, sun.y + oy, r * 0.7, 0, Math.PI * 2);
      ctx.fill();
    }
    ctx.restore();
    return;
  }

  const pulse = 1 + 0.08 * Math.sin(t * 0.003) * Math.max(0, 1 - evo);
  // Shrink corona as star evolves
  const coronaScale = evo < 1 ? (3 - evo * 1.5) : (1.5 - (evo - 1) * 1.2);
  const r = sun.radius * Math.max(coronaScale, 0.3) * pulse;

  // Determine colors based on evolution
  let hex = sun.color || '#ffb347';
  let glowAlpha = 0.35;
  if (evo >= 1) {
    // White dwarf to black dwarf transition
    const bdProgress = evo - 1; // 0 to 1
    if (bdProgress < 0.5) {
      hex = '#e0e8ff'; // white-blue
    } else {
      hex = '#444444'; // cooling dark
    }
    glowAlpha = Math.max(0.02, 0.25 * (1 - bdProgress));
  } else if (evo > 0) {
    // Transitioning: shift toward white
    const r0 = parseInt((sun.color || '#ffb347').slice(1,3),16);
    const g0 = parseInt((sun.color || '#ffb347').slice(3,5),16);
    const b0 = parseInt((sun.color || '#ffb347').slice(5,7),16);
    const wr = Math.round(r0 + (224 - r0) * evo);
    const wg = Math.round(g0 + (232 - g0) * evo);
    const wb = Math.round(b0 + (255 - b0) * evo);
    hex = '#' + wr.toString(16).padStart(2,'0') + wg.toString(16).padStart(2,'0') + wb.toString(16).padStart(2,'0');
  }

  const cr = parseInt(hex.slice(1,3),16), cg = parseInt(hex.slice(3,5),16), cb = parseInt(hex.slice(5,7),16);

  // Black dwarf: same shape as a white dwarf, but emits no light.
  // The disc itself (drawn in drawBody) handles the visible black orb.
  if (evo >= 2) return;

  // Outer glow
  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  const g1 = ctx.createRadialGradient(sun.x, sun.y, sun.radius * 0.5, sun.x, sun.y, r);
  g1.addColorStop(0, `rgba(${cr},${cg},${cb},${glowAlpha})`);
  g1.addColorStop(0.4, `rgba(${cr},${Math.max(cg-60,0)},${Math.max(cb-40,0)},${glowAlpha * 0.34})`);
  g1.addColorStop(1, `rgba(${cr},${Math.max(cg-120,0)},${Math.max(cb-60,0)},0)`);
  ctx.fillStyle = g1;
  ctx.beginPath();
  ctx.arc(sun.x, sun.y, r, 0, Math.PI * 2);
  ctx.fill();

  // Inner glow (dimmer for evolved stars)
  const innerAlpha = evo < 1 ? 0.9 : Math.max(0.1, 0.9 - (evo - 1) * 0.8);
  const g2 = ctx.createRadialGradient(sun.x, sun.y, 0, sun.x, sun.y, sun.radius * 1.4);
  g2.addColorStop(0, `rgba(255,${Math.min(cg+50,255)},${Math.min(cb+100,255)},${innerAlpha})`);
  g2.addColorStop(0.5, `rgba(${cr},${cg},${cb},${innerAlpha * 0.55})`);
  g2.addColorStop(1, `rgba(${cr},${Math.max(cg-40,0)},${Math.max(cb-30,0)},0)`);
  ctx.fillStyle = g2;
  ctx.beginPath();
  ctx.arc(sun.x, sun.y, sun.radius * 1.4, 0, Math.PI * 2);
  ctx.fill();
  ctx.restore();
}

// Draws a cartoon face (two eyes + a mouth) centered at (x, y) on a disc of
// the given radius. The face appears only when the body is large enough on
// screen to actually see. `mood` picks the expression; `color` is the fill
// color for eyes/mouth strokes (auto-picks contrast if omitted).
function drawFace(x, y, r, mood = 'happy', color) {
  if (!facesEnabled) return;
  const screenR = r * viewZoom;
  if (screenR < 12) return;
  ctx.save();
  ctx.fillStyle = color || '#111';
  ctx.strokeStyle = color || '#111';
  ctx.lineWidth = Math.max(r * 0.05, 1);
  ctx.lineCap = 'round';
  ctx.lineJoin = 'round';
  const exo = r * 0.32;            // eye x-offset from center
  const eyo = r * 0.12;            // eye y-offset (above center)
  const eR  = r * 0.10;            // eye radius
  const my  = y + r * 0.22;        // mouth y
  const mw  = r * 0.40;            // mouth half-width
  const lE  = x - exo, rE = x + exo;
  const eY  = y - eyo;
  if (mood === 'dead') {
    [lE, rE].forEach(cx => {
      ctx.beginPath();
      ctx.moveTo(cx - eR, eY - eR); ctx.lineTo(cx + eR, eY + eR);
      ctx.moveTo(cx + eR, eY - eR); ctx.lineTo(cx - eR, eY + eR);
      ctx.stroke();
    });
    ctx.beginPath(); ctx.moveTo(x - mw, my); ctx.lineTo(x + mw, my); ctx.stroke();
  } else if (mood === 'sleepy') {
    ctx.beginPath();
    ctx.moveTo(lE - eR, eY); ctx.lineTo(lE + eR, eY);
    ctx.moveTo(rE - eR, eY); ctx.lineTo(rE + eR, eY);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(x - mw * 0.6, my); ctx.lineTo(x + mw * 0.6, my);
    ctx.stroke();
  } else if (mood === 'angry') {
    // Plain "annoyed" angry — normal round eyes, mildly furrowed eyebrows
    // above (not slanting into the eyes), and a deep frown. Avoids the
    // sharp slit-eyed villain look.
    ctx.beginPath(); ctx.arc(lE, eY, eR, 0, Math.PI * 2); ctx.fill();
    ctx.beginPath(); ctx.arc(rE, eY, eR, 0, Math.PI * 2); ctx.fill();
    // Steeply-slanted eyebrows above each eye — outer end high, inner end
    // dips close to the eye for a more intense angry look.
    ctx.lineWidth = Math.max(r * 0.08, 1.6);
    const browY = eY - eR * 1.6;
    ctx.beginPath();
    ctx.moveTo(lE - eR * 1.3, browY - eR * 0.9);   // outer end high
    ctx.lineTo(lE + eR * 1.3, browY + eR * 0.7);   // inner end low
    ctx.moveTo(rE - eR * 1.3, browY + eR * 0.7);   // inner end low
    ctx.lineTo(rE + eR * 1.3, browY - eR * 0.9);   // outer end high
    ctx.stroke();
    // Frown mouth — corners down, middle up (inverted-U / ∩ shape).
    ctx.beginPath();
    ctx.moveTo(x - mw, my + r * 0.10);
    ctx.quadraticCurveTo(x, my - r * 0.10, x + mw, my + r * 0.10);
    ctx.stroke();
  } else if (mood === 'surprised') {
    ctx.beginPath(); ctx.arc(lE, eY, eR * 1.2, 0, Math.PI * 2); ctx.fill();
    ctx.beginPath(); ctx.arc(rE, eY, eR * 1.2, 0, Math.PI * 2); ctx.fill();
    ctx.beginPath(); ctx.arc(x, my + r * 0.04, r * 0.13, 0, Math.PI * 2);
    ctx.stroke();
  } else if (mood === 'neutral') {
    ctx.beginPath(); ctx.arc(lE, eY, eR * 0.85, 0, Math.PI * 2); ctx.fill();
    ctx.beginPath(); ctx.arc(rE, eY, eR * 0.85, 0, Math.PI * 2); ctx.fill();
    ctx.beginPath();
    ctx.moveTo(x - mw * 0.6, my); ctx.lineTo(x + mw * 0.6, my); ctx.stroke();
  } else {
    // 'happy' default — round eyes + smiling arc.
    ctx.beginPath(); ctx.arc(lE, eY, eR, 0, Math.PI * 2); ctx.fill();
    ctx.beginPath(); ctx.arc(rE, eY, eR, 0, Math.PI * 2); ctx.fill();
    ctx.beginPath();
    ctx.arc(x, my - r * 0.06, mw * 0.9, 0.15 * Math.PI, 0.85 * Math.PI);
    ctx.stroke();
  }
  ctx.restore();
}

function sunFaceMood(phase) {
  switch (phase) {
    case 'main-sequence':   return 'happy';
    case 'transitioning':   return 'sleepy';
    case 'expanding':       return 'angry';     // transitioning to red giant
    case 'red-giant':       return 'angry';
    case 'k-super-giant':   return 'happy';
    case 'blue-super-giant':return 'surprised';
    case 'white-dwarf':     return 'neutral';
    case 'black-dwarf':     return 'dead';
    default:                return null; // BH, NS, supernova, etc. — no face
  }
}

// Compute the current canvas transform's average scale factor (world → screen).
// Used to enforce a minimum on-screen body size at extreme zoom-out.
function currentScreenScale() {
  const tr = ctx.getTransform();
  // Average the x and y scale; DPR shows up here so we strip it back out.
  return (Math.abs(tr.a) + Math.abs(tr.d)) / (2 * RENDER_DPR);
}

function drawBody(b, t) {
  // Apply the size-exaggeration multiplier (user-facing slider, default 1).
  // Swapping b.radius for the duration of the draw means every gradient,
  // glow, ring, face, and continent that derives off b.radius scales with
  // it — without touching physics. We restore in the finally below so
  // collision detection, mass sliders, and stellar-phase code keep seeing
  // the real radius. (The same try/finally previously hosted a min-screen-
  // radius hack; that's gone, but the scaffold is now used for the
  // exaggeration swap.)
  const _bodyOrigR = b.radius;
  if (sizeExaggeration !== 1) b.radius = b.radius * sizeExaggeration;
  try {

  // Asteroids and comets are batch-drawn outside drawBody for perf — the
  // main render loop calls drawAsteroidsBatched2D / drawCometsBatched2D
  // (or the 3D equivalents). If anyone still routes one through drawBody
  // we fall back to a cheap flat disc here.
  if (b.isAsteroid) {
    ctx.fillStyle = b.color || '#9a8a7a';
    ctx.beginPath();
    ctx.arc(b.x, b.y, b.radius, 0, Math.PI * 2);
    ctx.fill();
    return;
  }
  if (b.isComet) {
    drawCometSingle(b);
    return;
  }

  if (b.isSun) {
    const evo = getSunEvolutionFactor(b);
    const phase = getSunPhase(b);
    const rgFactor = getRedGiantFactor(b);
    drawSunCorona(b, t);
    // Realistic mode for a body named "Sun" (must be main-sequence — we don't
    // try to map evolutionary phases to photographs). Paints over the disc
    // after the corona; face/glow code is skipped below.
    if (realisticMode && (b.name || '').toLowerCase() === 'sun' && phase === 'main-sequence') {
      drawRealisticSun(b, t);
      return;
    }

    // Determine disc color based on phase
    let hex = b.color || '#ffb347';
    let discRadius = b.radius;

    if (phase === 'blue-super-giant') {
      discRadius = b.radius * 30;
      hex = '#3a7aff';
    } else if (phase === 'red-giant' || (phase === 'expanding' && rgFactor > 0)) {
      const superMul = b.redSuperGiant ? 10 : 1;
      discRadius = b.radius * (1 + rgFactor * 2.5) * superMul;
      hex = '#ff4422';
    } else if (phase === 'collapsing') {
      const since = b.phaseAtSim ? (simTime - b.phaseAtSim) / 1000 : 0;
      discRadius = b.radius * Math.max(0.3, 1 - since / 2);
      hex = '#ff8844';
    } else if (phase === 'supernova') {
      discRadius = b.radius * 1.5;
      hex = '#ffffff';
    } else if (phase === 'neutron-star' || phase === 'dormant-neutron-star') {
      discRadius = 3;
      if (b.magnetar) hex = '#ff66ff';
      else if (b.strangeMatter) hex = '#66ff66';
      else hex = '#ccddff';
    } else if (phase === 'wolf-rayet') {
      // Corona handles everything (cloud + hot core + ejecta particles).
      discRadius = 0;
    } else if (phase === 'black-hole' || phase === 'evaporating') {
      // Event horizon + photon ring already rendered in drawSunCorona
      discRadius = 0;
      hex = '#000000';
    } else if (phase === 'nebula') {
      // Nebula has no disc, corona already rendered the cloud
      discRadius = 0;
    } else if (evo >= 2) {
      // Black dwarf: same size as a white dwarf, pure black, no light.
      hex = '#000000';
      discRadius = b.radius * 0.5;
    } else if (evo >= 1) {
      // White dwarf: small white-blue disc
      const bdProgress = evo - 1;
      discRadius = b.radius * (0.5 - bdProgress * 0.15);
      if (bdProgress < 0.5) {
        hex = '#e0e8ff';
      } else {
        const fade = (bdProgress - 0.5) * 2;
        const rv = Math.round(224 - fade * 198);
        const gv = Math.round(232 - fade * 206);
        const bv = Math.round(255 - fade * 229);
        hex = '#' + rv.toString(16).padStart(2,'0') + gv.toString(16).padStart(2,'0') + bv.toString(16).padStart(2,'0');
      }
    } else if (evo > 0) {
      // Transitioning: shrink and shift toward white
      discRadius = b.radius * (1 - evo * 0.5);
      const r0 = parseInt((b.color || '#ffb347').slice(1,3),16);
      const g0 = parseInt((b.color || '#ffb347').slice(3,5),16);
      const b0 = parseInt((b.color || '#ffb347').slice(5,7),16);
      const wr = Math.round(r0 + (224 - r0) * evo);
      const wg = Math.round(g0 + (232 - g0) * evo);
      const wb = Math.round(b0 + (255 - b0) * evo);
      hex = '#' + wr.toString(16).padStart(2,'0') + wg.toString(16).padStart(2,'0') + wb.toString(16).padStart(2,'0');
    }

    if (discRadius > 0) {
      if (phase === 'black-dwarf') {
        // Flat pure-black disc — no highlight, no rim shading, no light.
        ctx.fillStyle = '#000000';
        ctx.beginPath();
        ctx.arc(b.x, b.y, discRadius, 0, Math.PI * 2);
        ctx.fill();
      } else {
        const cr = parseInt(hex.slice(1,3),16), cg = parseInt(hex.slice(3,5),16), cb = parseInt(hex.slice(5,7),16);
        const sg = ctx.createRadialGradient(b.x - discRadius * 0.2, b.y - discRadius * 0.2, 0, b.x, b.y, discRadius);
        sg.addColorStop(0, `rgb(${Math.min(cr+50,255)},${Math.min(cg+50,255)},${Math.min(cb+50,255)})`);
        sg.addColorStop(0.4, hex);
        sg.addColorStop(1, `rgb(${Math.max(cr-40,0)},${Math.max(cg-40,0)},${Math.max(cb-40,0)})`);
        ctx.fillStyle = sg;
        ctx.beginPath();
        ctx.arc(b.x, b.y, discRadius, 0, Math.PI * 2);
        ctx.fill();
      }
      // Face on top of the sun's disc (skipped for transient/compact phases).
      const mood = sunFaceMood(phase);
      if (mood) {
        const faceColor = phase === 'black-dwarf' ? '#666' : '#111';
        drawFace(b.x, b.y, discRadius, mood, faceColor);
      }
    }
  } else {
    // Apply any name-based size multiplier (e.g. ROXs 42Bb is 7× larger).
    // Temporarily swap b.radius so all the existing planet-drawing code
    // (glow, continents, spots, rings, highlight) automatically scales.
    const _origR = b.radius;
    const _displayR = planetDisplayRadius(b);
    if (_displayR !== _origR) b.radius = _displayR;

    // Realistic mode — if the body's name matches a real solar-system
    // planet, paint the textured version (handles its own rings) and skip
    // the rest of the cartoon path (no glow, no face, no continents on top).
    if (drawRealisticBody(b, t)) {
      if (_displayR !== _origR) b.radius = _origR;
      return;
    }

    // Planetary rings — back half drawn first
    const _isSaturn  = isSaturnLike(b);
    const _isJ1407b  = isJ1407bLike(b);
    if (_isSaturn) drawSaturnRings(b, true, 1);
    else if (_isJ1407b) drawJ1407bRings(b, true);

    // Dwarf-star halo: soft outer glow when mass > 50
    if (b.mass > 50) {
      const hex = b.color || '#ffffff';
      const cr = parseInt(hex.slice(1,3),16) || 255;
      const cg = parseInt(hex.slice(3,5),16) || 255;
      const cb = parseInt(hex.slice(5,7),16) || 255;
      const haloR = b.radius * 3.2;
      ctx.save();
      ctx.globalCompositeOperation = 'lighter';
      const halo = ctx.createRadialGradient(b.x, b.y, b.radius * 0.6, b.x, b.y, haloR);
      halo.addColorStop(0, `rgba(${cr},${cg},${cb},0.35)`);
      halo.addColorStop(0.5, `rgba(${cr},${cg},${cb},0.12)`);
      halo.addColorStop(1, `rgba(${cr},${cg},${cb},0)`);
      ctx.fillStyle = halo;
      ctx.beginPath();
      ctx.arc(b.x, b.y, haloR, 0, Math.PI * 2);
      ctx.fill();
      ctx.restore();
    }

    // Planet glow
    ctx.save();
    ctx.shadowColor = b.color;
    ctx.shadowBlur = b.mass > 50 ? 22 : 15;
    ctx.fillStyle = b.color;
    ctx.beginPath();
    ctx.arc(b.x, b.y, b.radius, 0, Math.PI * 2);
    ctx.fill();
    ctx.restore();

    // Earth-like life: green continents on the surface
    if (b.continents) {
      ctx.save();
      ctx.beginPath();
      ctx.arc(b.x, b.y, b.radius, 0, Math.PI * 2);
      ctx.clip();
      for (const c of b.continents) {
        const cx = b.x + Math.cos(c.angle) * c.distFrac * b.radius;
        const cy = b.y + Math.sin(c.angle) * c.distFrac * b.radius;
        const cr = c.sizeFrac * b.radius;
        const gShade = Math.round(140 + c.shade * 70); // 140–210
        ctx.fillStyle = `rgb(40, ${gShade}, 60)`;
        ctx.beginPath();
        ctx.arc(cx, cy, cr, 0, Math.PI * 2);
        ctx.fill();
      }
      ctx.restore();
    }

    // Jupiter Great Red Spot
    if (isJupiterLike(b)) drawJupiterSpot(b);

    // Pluto Tombaugh Regio (light brown heart)
    if (isPlutoLike(b)) drawPlutoHeart(b);

    // Highlight
    const hg = ctx.createRadialGradient(b.x - b.radius * 0.3, b.y - b.radius * 0.3, 0, b.x, b.y, b.radius);
    hg.addColorStop(0, 'rgba(255,255,255,0.35)');
    hg.addColorStop(1, 'rgba(255,255,255,0)');
    ctx.fillStyle = hg;
    ctx.beginPath();
    ctx.arc(b.x, b.y, b.radius, 0, Math.PI * 2);
    ctx.fill();

    // Planetary rings — front half drawn on top of the body and highlight
    if (_isSaturn) drawSaturnRings(b, false, 1);
    else if (_isJ1407b) drawJ1407bRings(b, false);

    // Face on planets and moons. Dwarf stars (mass > 50) get the same treatment.
    const planetMood = b.continents ? 'happy' : 'happy';
    drawFace(b.x, b.y, b.radius, planetMood, '#111');

    // Restore the body's stored radius so physics / sliders see the real value
    if (_displayR !== _origR) b.radius = _origR;
  }

  } finally {
    // Restore the min-screen-radius swap from the top of the function.
    b.radius = _bodyOrigR;
  }
}

// Batched asteroid render — flat shaded discs, grouped by color so we only
// flip fillStyle once per palette entry instead of once per asteroid. Skips
// the drawBody save/restore + try/finally + size-exag swap entirely. Called
// from the main render loop in place of per-asteroid drawBody.
function drawAsteroidsBatched2D() {
  // Gather asteroids per color once
  const byColor = new Map();
  for (const b of bodies) {
    if (!b.isAsteroid) continue;
    const c = b.color || '#9a8a7a';
    let arr = byColor.get(c);
    if (!arr) { arr = []; byColor.set(c, arr); }
    arr.push(b);
  }
  for (const [color, group] of byColor) {
    ctx.fillStyle = color;
    ctx.beginPath();
    for (const b of group) {
      const r = b.radius * sizeExaggeration;
      ctx.moveTo(b.x + r, b.y);
      ctx.arc(b.x, b.y, r, 0, Math.PI * 2);
    }
    ctx.fill();
  }
}

function drawAsteroidsBatched3D() {
  ctx.setTransform(RENDER_DPR, 0, 0, RENDER_DPR, 0, 0);
  const byColor = new Map();
  for (const b of bodies) {
    if (!b.isAsteroid) continue;
    const proj = project3DScreen(b.x, b.y, b.z || 0);
    if (proj.scale <= 0) continue;
    const sr = Math.max(0.5, b.radius * sizeExaggeration * proj.scale);
    const c = b.color || '#9a8a7a';
    let arr = byColor.get(c);
    if (!arr) { arr = []; byColor.set(c, arr); }
    arr.push({ sx: proj.sx, sy: proj.sy, sr });
  }
  for (const [color, group] of byColor) {
    ctx.fillStyle = color;
    ctx.beginPath();
    for (const p of group) {
      ctx.moveTo(p.sx + p.sr, p.sy);
      ctx.arc(p.sx, p.sy, p.sr, 0, Math.PI * 2);
    }
    ctx.fill();
  }
}

// Single-comet render — nucleus + tapered tail pointing away from the
// nearest sun. The tail extends ~1 AU and fades to transparent. In
// realisticMode the tail is layered (5 stacked tapered strokes from a
// wide pale-blue haze down to a bright white spine) and the nucleus
// gets a wider blue-white halo to match the reference photo.
function drawCometSingle(b) {
  let nearest = null, bestDistSq = Infinity;
  for (const s of bodies) {
    if (!s.isSun) continue;
    const dx = b.x - s.x, dy = b.y - s.y;
    const d2 = dx*dx + dy*dy;
    if (d2 < bestDistSq) { bestDistSq = d2; nearest = s; }
  }
  if (nearest) {
    const dx = b.x - nearest.x, dy = b.y - nearest.y;
    const dist = Math.sqrt(bestDistSq);
    if (dist > 0.0001) {
      const ux = dx / dist, uy = dy / dist;
      const px = -uy, py = ux;
      const tailLen = _AU_SIM_UNITS;
      const tipX = b.x + ux * tailLen;
      const tipY = b.y + uy * tailLen;

      if (realisticMode) {
        // Five-layer tail: from the widest outer haze to the brightest
        // inner spine. Widths are fractions of an AU, alphas decay to 0
        // 70% of the way along so the tip fades smoothly.
        const layers = [
          { wFrac: 0.026, r: 130, g: 165, bC: 220, a: 0.40 },
          { wFrac: 0.018, r: 165, g: 200, bC: 240, a: 0.55 },
          { wFrac: 0.011, r: 205, g: 225, bC: 250, a: 0.70 },
          { wFrac: 0.006, r: 235, g: 245, bC: 255, a: 0.85 },
          { wFrac: 0.0025, r: 255, g: 255, bC: 255, a: 0.95 }
        ];
        for (const ly of layers) {
          const baseW = _AU_SIM_UNITS * ly.wFrac;
          const c = (a) => `rgba(${ly.r},${ly.g},${ly.bC},${a})`;
          const grad = ctx.createLinearGradient(b.x, b.y, tipX, tipY);
          grad.addColorStop(0,    c(ly.a));
          grad.addColorStop(0.55, c(ly.a * 0.45));
          grad.addColorStop(1,    c(0));
          ctx.fillStyle = grad;
          ctx.beginPath();
          ctx.moveTo(b.x + px * baseW, b.y + py * baseW);
          ctx.lineTo(b.x - px * baseW, b.y - py * baseW);
          ctx.lineTo(tipX, tipY);
          ctx.closePath();
          ctx.fill();
        }
        // Coma — bluish glow around the nucleus.
        const haloR = Math.max(b.radius * 8, _AU_SIM_UNITS * 0.003);
        const halo = ctx.createRadialGradient(b.x, b.y, 0, b.x, b.y, haloR);
        halo.addColorStop(0,    'rgba(255, 255, 255, 0.95)');
        halo.addColorStop(0.30, 'rgba(200, 225, 255, 0.55)');
        halo.addColorStop(0.70, 'rgba(140, 175, 230, 0.20)');
        halo.addColorStop(1,    'rgba(80, 110, 180, 0)');
        ctx.fillStyle = halo;
        ctx.beginPath();
        ctx.arc(b.x, b.y, haloR, 0, Math.PI * 2);
        ctx.fill();
        // Nucleus core
        ctx.fillStyle = '#ffffff';
        ctx.beginPath();
        ctx.arc(b.x, b.y, Math.max(b.radius, 0.6), 0, Math.PI * 2);
        ctx.fill();
        return;
      }

      // Non-realistic: simpler two-gradient tail.
      const baseW = Math.max(b.radius * 8, _AU_SIM_UNITS * 0.005);
      const grad = ctx.createLinearGradient(b.x, b.y, tipX, tipY);
      grad.addColorStop(0,   'rgba(190, 215, 255, 0.85)');
      grad.addColorStop(0.3, 'rgba(190, 215, 255, 0.45)');
      grad.addColorStop(1,   'rgba(190, 215, 255, 0)');
      ctx.fillStyle = grad;
      ctx.beginPath();
      ctx.moveTo(b.x + px * baseW, b.y + py * baseW);
      ctx.lineTo(b.x - px * baseW, b.y - py * baseW);
      ctx.lineTo(tipX, tipY);
      ctx.closePath();
      ctx.fill();
      const innerW = baseW * 0.45;
      const grad2 = ctx.createLinearGradient(b.x, b.y, tipX, tipY);
      grad2.addColorStop(0, 'rgba(255, 255, 255, 0.55)');
      grad2.addColorStop(1, 'rgba(255, 255, 255, 0)');
      ctx.fillStyle = grad2;
      ctx.beginPath();
      ctx.moveTo(b.x + px * innerW, b.y + py * innerW);
      ctx.lineTo(b.x - px * innerW, b.y - py * innerW);
      ctx.lineTo(tipX, tipY);
      ctx.closePath();
      ctx.fill();
    }
  }
  // Non-realistic nucleus
  ctx.save();
  ctx.shadowColor = '#aaccff';
  ctx.shadowBlur = 6;
  ctx.fillStyle = b.color || '#eaf2ff';
  ctx.beginPath();
  ctx.arc(b.x, b.y, Math.max(b.radius, 0.5), 0, Math.PI * 2);
  ctx.fill();
  ctx.restore();
}

function drawTrails() {
  if (!showTrails) return;
  // Keep the trail stroke at a constant screen-space width regardless of zoom,
  // so AU-scale orbits stay visible even when the camera is zoomed far out.
  const screenLineWidth = 1.2 / viewZoom;
  // Rounded joins/caps soften the visible angle between sparse samples so the
  // orbit reads as a curve instead of a sequence of line segments.
  ctx.lineJoin = 'round';
  ctx.lineCap  = 'round';
  for (const b of bodies) {
    if (b.trail.length < 2) continue;
    // The trail array can grow up to ~2× TRAIL_LEN between trims (see step()),
    // so start from the most recent TRAIL_LEN samples and stride to keep the
    // line count manageable at high time-warp.
    const start = Math.max(0, b.trail.length - TRAIL_LEN);
    const step = TRAIL_RENDER_STRIDE;
    const last = b.trail.length - 1;
    ctx.beginPath();
    // Quadratic-curve smoothing through the captured points: each pair of
    // consecutive samples (i, i+1) becomes a quadratic Bezier where the
    // control point is sample i and the endpoint is the midpoint of i and i+1.
    // This rounds off the discrete physics-step corners visually without
    // adding extra samples.
    ctx.moveTo(b.trail[start].x, b.trail[start].y);
    for (let i = start + step; i + step <= last; i += step) {
      const x0 = b.trail[i].x, y0 = b.trail[i].y;
      const xn = b.trail[i + step].x, yn = b.trail[i + step].y;
      ctx.quadraticCurveTo(x0, y0, (x0 + xn) * 0.5, (y0 + yn) * 0.5);
    }
    // Always close the line at the most recent sample so the head reads as
    // attached to the body, regardless of stride.
    ctx.lineTo(b.trail[last].x, b.trail[last].y);
    // Comet trails are deliberately brighter + thicker + more opaque than
    // normal orbit lines so the elliptical path reads at AU zoom.
    if (b.isComet) {
      ctx.strokeStyle = '#b8d8ff';
      ctx.lineWidth = screenLineWidth * 1.8;
      ctx.globalAlpha = 0.55;
    } else {
      ctx.strokeStyle = b.color;
      ctx.lineWidth = b.isSun ? 0 : screenLineWidth;
      ctx.globalAlpha = 0.3;
    }
    ctx.stroke();
    ctx.globalAlpha = 1;
  }
}

function drawMergeEffects() {
  for (let e = mergeEffects.length - 1; e >= 0; e--) {
    const eff = mergeEffects[e];
    if (!paused) {
      eff.age++;
      for (const p of eff.particles) {
        p.x += p.vx;
        p.y += p.vy;
        p.life -= 0.025;
      }
      eff.particles = eff.particles.filter(p => p.life > 0);
    }
    if (eff.particles.length === 0) { mergeEffects.splice(e, 1); continue; }
    for (const p of eff.particles) {
      ctx.globalAlpha = p.life * 0.8;
      ctx.fillStyle = eff.color;
      ctx.beginPath();
      ctx.arc(p.x, p.y, 2 * p.life, 0, Math.PI * 2);
      ctx.fill();
    }
    ctx.globalAlpha = 1;
  }
}

// 3D variant: same effect lifecycle but particle positions are projected
// individually to screen space so they sit at the correct depth.
function drawMergeEffects3D() {
  ctx.setTransform(RENDER_DPR, 0, 0, RENDER_DPR, 0, 0);
  for (let e = mergeEffects.length - 1; e >= 0; e--) {
    const eff = mergeEffects[e];
    if (!paused) {
      eff.age++;
      for (const p of eff.particles) {
        p.x += p.vx;
        p.y += p.vy;
        p.life -= 0.025;
      }
      eff.particles = eff.particles.filter(p => p.life > 0);
    }
    if (eff.particles.length === 0) { mergeEffects.splice(e, 1); continue; }
    const ez = eff.z || 0;
    for (const p of eff.particles) {
      const proj = project3DScreen(p.x, p.y, ez);
      ctx.globalAlpha = p.life * 0.8;
      ctx.fillStyle = eff.color;
      ctx.beginPath();
      ctx.arc(proj.sx, proj.sy, 2 * p.life * Math.max(0.1, proj.scale), 0, Math.PI * 2);
      ctx.fill();
    }
    ctx.globalAlpha = 1;
  }
}

// ---- Camera (follows the primary sun until the user pans/zooms) ----
let viewX = 0, viewY = 0;     // world-space point centered on screen
let viewZoom = 1;             // 1 = default; >1 zooms in
let autoFollow = true;

// ---- 3D Mode ----
// When is3D is true, bodies carry z + vz and rendering applies a perspective
// projection with yaw/pitch camera rotation. The default solar system lives
// in the z=0 plane, so 3D mode initially just tilts the view; z gradients
// appear once bodies are dragged or created with z motion.
let is3D = false;
let cameraYaw = 0;            // rotation around vertical (Y) axis, radians
let cameraPitch = 0;          // rotation around horizontal (X) axis, radians
const PERSPECTIVE_FOCAL = 1500;

function project3D(wx, wy, wz) {
  const dx = wx - viewX, dy = wy - viewY, dz = (wz || 0);
  // Yaw around Y axis (left/right camera turn)
  const cy = Math.cos(cameraYaw), sy = Math.sin(cameraYaw);
  const x1 = dx * cy + dz * sy;
  const z1 = -dx * sy + dz * cy;
  // Pitch around X axis (up/down camera tilt)
  const cp = Math.cos(cameraPitch), sp = Math.sin(cameraPitch);
  const y2 = dy * cp - z1 * sp;
  const z2 = dy * sp + z1 * cp;
  // Perspective is applied in screen-space depth (world z × viewZoom). Because
  // the simulator spans world distances from a few units to many millions, a
  // fixed world-space focal would collapse anything past a few thousand units
  // to a single pixel. Scaling the depth by viewZoom keeps the perspective
  // sensible whether the view is zoomed into a single planet or out to Pluto.
  const screenZ = z2 * viewZoom;
  const denom = Math.max(50, PERSPECTIVE_FOCAL + screenZ);
  const perspective = PERSPECTIVE_FOCAL / denom;
  return { x: x1, y: y2, z: z2, perspective };
}

// 3D screen-space projection that also folds in the user's 2D zoom.
function project3DScreen(wx, wy, wz) {
  const p = project3D(wx, wy, wz);
  const w = canvas.clientWidth, h = canvas.clientHeight;
  const totalScale = viewZoom * p.perspective;
  return { sx: w / 2 + p.x * totalScale, sy: h / 2 + p.y * totalScale, scale: totalScale, depth: p.z };
}

// Set up the canvas transform so drawing at world-space (wx, wy) lands at
// its projected screen position with the correct perspective scale. Caller
// must wrap with ctx.save() / ctx.restore().
function applyEntity3DTransform(wx, wy, wz) {
  const w = canvas.clientWidth, h = canvas.clientHeight;
  const p = project3D(wx, wy, wz);
  const totalScale = viewZoom * p.perspective;
  ctx.setTransform(RENDER_DPR, 0, 0, RENDER_DPR, 0, 0);
  ctx.translate(w / 2 + p.x * totalScale, h / 2 + p.y * totalScale);
  ctx.scale(totalScale, totalScale);
  ctx.translate(-wx, -wy);
  return p;
}

function screenToWorld(sx, sy) {
  const rect = canvas.getBoundingClientRect();
  const w = canvas.clientWidth, h = canvas.clientHeight;
  if (is3D) {
    // Inverse projection into the z=0 world plane. Solves for the (X, Y, 0)
    // world point whose projected screen position equals (sx, sy). This is
    // what dragging / spawning expects to land "in the orbital plane".
    const nx = (sx - rect.left - w / 2) / viewZoom;
    const ny = (sy - rect.top - h / 2) / viewZoom;
    // Forward transform (with z=0):
    //   x' =  dx*cos(yaw)
    //   y' =  dy*cos(pitch) + dx*sin(yaw)*sin(pitch)
    // We need a non-perspective inverse here — perspective with z=0 collapses
    // to scale=1, so the linear inverse below is exact for the orbital plane.
    const cy = Math.cos(cameraYaw), sy_ = Math.sin(cameraYaw);
    const cp = Math.cos(cameraPitch), sp = Math.sin(cameraPitch);
    // From x' = dx*cy  →  dx = x'/cy (yaw avoided when cy≈0 by falling back)
    if (Math.abs(cy) < 1e-6 || Math.abs(cp) < 1e-6) {
      return { x: viewX + nx, y: viewY + ny };
    }
    const dx = nx / cy;
    const dy = (ny - dx * sy_ * sp) / cp;
    return { x: viewX + dx, y: viewY + dy };
  }
  return {
    x: (sx - rect.left - w / 2) / viewZoom + viewX,
    y: (sy - rect.top - h / 2) / viewZoom + viewY
  };
}

// ---- Main loop ----
function loop(t) {
  const w = canvas.clientWidth, h = canvas.clientHeight;
  ctx.clearRect(0, 0, w, h);

  // If a Universe galaxy exists, anything outside its disc is pure black
  // (no bluish nebula tint, no starfield). The disc is computed in screen
  // space so the background tracks the camera as you pan/zoom.
  const universe = galaxies.find(g => g.type === 'universe');
  let universeDisc = null;
  if (universe) {
    universeDisc = {
      sx: (universe.x - viewX) * viewZoom + w / 2,
      sy: (universe.y - viewY) * viewZoom + h / 2,
      sr: universe.radius * viewZoom
    };
  }

  // Pure-black canvas. Background is uniformly black now (was bluish-tinted
  // inside Universe discs); stars are drawn on top inside the clip block.
  ctx.fillStyle = '#000000';
  ctx.fillRect(0, 0, w, h);

  // Advance animTime only when running, scaled by the speed multiplier so
  // animations slow with the simulation (and speed up at higher multipliers).
  const realDt = lastLoopTime > 0 ? (t - lastLoopTime) : 16.67;
  if (!paused) animTime += realDt * speedMul;

  ctx.save();
  if (universeDisc) {
    ctx.beginPath();
    ctx.arc(universeDisc.sx, universeDisc.sy, universeDisc.sr, 0, Math.PI * 2);
    ctx.clip();
  }
  // Pure-black space + stars on top. (The earlier bluish #0a0a1a nebula tint
  // was removed at the user's request.)
  drawStars(animTime);
  ctx.restore();

  if (!paused) {
    // Physics steps are capped so extreme fast-forward (10,000×+) doesn't
    // freeze the frame; per-step dt is also clamped for integrator stability.
    // simTime (which drives stellar evolution and lifespans) advances
    // independently so fast-forwarded ages still progress correctly.
    const steps = Math.max(1, Math.min(Math.round(speedMul * 2), 100));
    const dt = Math.min(speedMul / steps, 8);
    for (let i = 0; i < steps; i++) step(dt);
    simTime += realDt * speedMul;
    checkStellarEvolution();
    checkBlackHoleCapture();
    checkMagnetarConversion();
    checkGalaxyMerges();
    updateBetelgeuseRadii();
    updateRigelStars();
    updateSmallStars();
    updateBTypeStars();
    updateOTypeStars();
    updateATypeStars();
    updateFTypeStars();
    updateGTypeStars();
    updateKTypeStars();
    updateMTypeStars();
    updateKSuperGiantStars();
    updateRockets(speedMul);
    trackEarthOrbits();
  }
  // Zoom-check runs every frame (even paused) so it works while inspecting
  checkRigelBlind();
  lastLoopTime = t;

  // Auto-follow the most massive sun (until the user pans/zooms manually)
  if (autoFollow) {
    const suns = bodies.filter(b => b.isSun);
    if (suns.length > 0) {
      const primarySun = suns.reduce((a, b) => a.mass >= b.mass ? a : b);
      viewX = primarySun.x;
      viewY = primarySun.y;
    }
  }

  // Selection bookkeeping (used by both 2D and 3D paths below)
  const bodyA = selectedBodyAId ? bodies.find(b => b.id === selectedBodyAId) : null;
  const bodyB = selectedBodyBId ? bodies.find(b => b.id === selectedBodyBId) : null;
  if (selectedBodyAId && !bodyA) selectedBodyAId = null;
  if (selectedBodyBId && !bodyB) selectedBodyBId = null;

  if (is3D) {
    // ---- 3D render path ----
    // Galaxies are huge background discs — draw first with their own transform.
    for (const g of galaxies) {
      ctx.save();
      applyEntity3DTransform(g.x, g.y, 0);
      if (g.type === 'universe') drawUniverse(g);
      else if (g.type === 'laniakea') drawLaniakea(g);
      else drawGalaxy(g);
      ctx.restore();
    }

    // Depth-aware trail rendering. Each sun gets a projected depth value;
    // any trail point further from the camera than the FURTHEST sun is "in
    // back" (drawn before suns, so the sun disc occludes it). Everything
    // else is "in front" (drawn after suns and most planets).
    const projected = bodies.map(b => ({ body: b, depth: project3D(b.x, b.y, b.z || 0).z }));
    const sunsSorted    = projected.filter(p => p.body.isSun ).sort((a, b) => b.depth - a.depth);
    const planetsSorted = projected.filter(p => !p.body.isSun).sort((a, b) => b.depth - a.depth);
    // Cache the deepest sun's z so back-trail classification is one number.
    const maxSunDepth = sunsSorted.length ? Math.max(...sunsSorted.map(p => p.depth)) : -Infinity;

    // Walks a single body's trail and strokes only the segments whose
    // projected depth falls in the requested half-space ('back' or 'front').
    // Consecutive same-layer points share a sub-path; crossing the boundary
    // closes the current stroke and starts a fresh one on the other side.
    const drawBodyTrailLayer3D = (b, layer) => {
      if (b.trail.length < 2) return;
      const start = Math.max(0, b.trail.length - TRAIL_LEN);
      const step = TRAIL_RENDER_STRIDE;
      const last = b.trail.length - 1;
      let inPath = false;
      const strokeIfOpen = () => {
        if (!inPath) return;
        if (b.isComet) {
          ctx.strokeStyle = '#b8d8ff';
          ctx.lineWidth = 2.0;
          ctx.globalAlpha = 0.55;
        } else {
          ctx.strokeStyle = b.color;
          ctx.lineWidth = b.isSun ? 0 : 1.2;
          ctx.globalAlpha = 0.3;
        }
        ctx.stroke();
        ctx.globalAlpha = 1;
        inPath = false;
      };
      const visit = (idx) => {
        const pt = b.trail[idx];
        const proj = project3DScreen(pt.x, pt.y, pt.z || 0);
        const isBack = proj.depth > maxSunDepth;
        const want = (layer === 'back') === isBack;
        if (want) {
          if (!inPath) { ctx.beginPath(); ctx.moveTo(proj.sx, proj.sy); inPath = true; }
          else         { ctx.lineTo(proj.sx, proj.sy); }
        } else {
          strokeIfOpen();
        }
      };
      for (let i = start; i + step <= last; i += step) visit(i);
      visit(last);
      strokeIfOpen();
    };

    const drawTrailLayer3D = (layer) => {
      if (!showTrails) return;
      ctx.setTransform(RENDER_DPR, 0, 0, RENDER_DPR, 0, 0);
      ctx.lineJoin = 'round';
      ctx.lineCap  = 'round';
      for (const b of bodies) drawBodyTrailLayer3D(b, layer);
    };

    // Order: back-of-sun trails → suns → front-of-sun trails → asteroids
    // (batched) → planets / comets / moons (each with its own 3D transform).
    drawTrailLayer3D('back');
    for (const { body } of sunsSorted) {
      ctx.save();
      applyEntity3DTransform(body.x, body.y, body.z || 0);
      drawBody(body, animTime);
      ctx.restore();
    }
    drawTrailLayer3D('front');
    drawAsteroidsBatched3D();
    for (const { body } of planetsSorted) {
      if (body.isAsteroid) continue;  // already batched above
      ctx.save();
      applyEntity3DTransform(body.x, body.y, body.z || 0);
      drawBody(body, animTime);
      ctx.restore();
    }

    // Rockets: each gets its own per-entity transform.
    for (const r of rockets) {
      ctx.save();
      applyEntity3DTransform(r.x, r.y, r.z || 0);
      drawSingleRocket(r, animTime);
      ctx.restore();
    }

    // Merge effects in screen space
    drawMergeEffects3D();

    // Selection rings
    const drawSelRing3D = (b, color) => {
      ctx.save();
      applyEntity3DTransform(b.x, b.y, b.z || 0);
      ctx.strokeStyle = color;
      ctx.lineWidth = 1.5;
      ctx.setLineDash([4, 4]);
      ctx.globalAlpha = 0.6 + 0.3 * Math.sin(animTime * 0.005);
      ctx.beginPath();
      ctx.arc(b.x, b.y, getEffectiveRadius(b) + 6, 0, Math.PI * 2);
      ctx.stroke();
      ctx.restore();
    };
    if (bodyA) drawSelRing3D(bodyA, '#34d399');
    if (bodyB) drawSelRing3D(bodyB, '#7dd3fc');
    if (bodyA && bodyB && bodyA !== bodyB) updateEquation(bodyA, bodyB);
    else if (!bodyA || !bodyB) clearEquation();

    // Velocity vectors: project endpoints individually
    if (showVectors) {
      ctx.setTransform(RENDER_DPR, 0, 0, RENDER_DPR, 0, 0);
      for (const b of bodies) {
        const speed = Math.sqrt(b.vx * b.vx + b.vy * b.vy + (b.vz || 0) * (b.vz || 0));
        if (speed < 0.01) continue;
        const tipWX = b.x + b.vx * VEL_ARROW_SCALE;
        const tipWY = b.y + b.vy * VEL_ARROW_SCALE;
        const tipWZ = (b.z || 0) + (b.vz || 0) * VEL_ARROW_SCALE;
        const baseP = project3DScreen(b.x, b.y, b.z || 0);
        const tipP = project3DScreen(tipWX, tipWY, tipWZ);
        const angle = Math.atan2(tipP.sy - baseP.sy, tipP.sx - baseP.sx);

        ctx.save();
        ctx.strokeStyle = 'rgba(255,255,255,0.5)';
        ctx.lineWidth = 2;
        ctx.beginPath();
        ctx.moveTo(baseP.sx, baseP.sy);
        ctx.lineTo(tipP.sx, tipP.sy);
        ctx.stroke();
        const headLen = 8;
        ctx.fillStyle = 'rgba(255,255,255,0.7)';
        ctx.beginPath();
        ctx.moveTo(tipP.sx, tipP.sy);
        ctx.lineTo(tipP.sx - headLen * Math.cos(angle - 0.4), tipP.sy - headLen * Math.sin(angle - 0.4));
        ctx.lineTo(tipP.sx - headLen * Math.cos(angle + 0.4), tipP.sy - headLen * Math.sin(angle + 0.4));
        ctx.closePath();
        ctx.fill();
        ctx.fillStyle = b.color || '#fff';
        ctx.globalAlpha = 0.85;
        ctx.beginPath();
        ctx.arc(tipP.sx, tipP.sy, 5, 0, Math.PI * 2);
        ctx.fill();
        ctx.strokeStyle = '#fff';
        ctx.lineWidth = 1;
        ctx.globalAlpha = 0.5;
        ctx.stroke();
        ctx.restore();
      }
    }

    // Restore identity so anything after (FPS overlay etc.) draws in screen space.
    ctx.setTransform(RENDER_DPR, 0, 0, RENDER_DPR, 0, 0);
  } else {
    // ---- 2D render path (existing behavior) ----
    ctx.save();
    ctx.translate(w / 2, h / 2);
    ctx.scale(viewZoom, viewZoom);
    ctx.translate(-viewX, -viewY);

    drawGalaxies();

    // Suns first — drawn UNDER the trails so the sun doesn't paint over
    // the orbit lines passing through its disc.
    for (const b of bodies) { if (b.isSun) drawBody(b, animTime); }
    drawTrails();
    // Asteroids batched separately — flat discs grouped by color, no per-body
    // drawBody overhead. This is the big asteroid-belt perf path.
    drawAsteroidsBatched2D();
    // Planets / moons / comets / anything else on top of trails + asteroids.
    for (const b of bodies) {
      if (b.isSun || b.isAsteroid) continue;
      drawBody(b, animTime);
    }

    drawRockets(animTime);
    drawMergeEffects();

    const drawSelRing = (b, color) => {
      ctx.save();
      ctx.strokeStyle = color;
      ctx.lineWidth = 1.5;
      ctx.setLineDash([4, 4]);
      ctx.globalAlpha = 0.6 + 0.3 * Math.sin(animTime * 0.005);
      ctx.beginPath();
      ctx.arc(b.x, b.y, getEffectiveRadius(b) + 6, 0, Math.PI * 2);
      ctx.stroke();
      ctx.restore();
    };
    if (bodyA) drawSelRing(bodyA, '#34d399'); // green = A
    if (bodyB) drawSelRing(bodyB, '#7dd3fc'); // cyan  = B
    if (bodyA && bodyB && bodyA !== bodyB) updateEquation(bodyA, bodyB);
    else if (!bodyA || !bodyB) clearEquation();

    // Draw velocity vectors
    if (showVectors) {
      for (const b of bodies) {
        const speed = Math.sqrt(b.vx * b.vx + b.vy * b.vy);
        if (speed < 0.01) continue;
        const tipX = b.x + b.vx * VEL_ARROW_SCALE;
        const tipY = b.y + b.vy * VEL_ARROW_SCALE;
        const angle = Math.atan2(b.vy, b.vx);

        ctx.save();
        // Arrow line
        ctx.strokeStyle = 'rgba(255,255,255,0.5)';
        ctx.lineWidth = 2;
        ctx.beginPath();
        ctx.moveTo(b.x, b.y);
        ctx.lineTo(tipX, tipY);
        ctx.stroke();

        // Arrowhead
        const headLen = 8;
        ctx.fillStyle = 'rgba(255,255,255,0.7)';
        ctx.beginPath();
        ctx.moveTo(tipX, tipY);
        ctx.lineTo(tipX - headLen * Math.cos(angle - 0.4), tipY - headLen * Math.sin(angle - 0.4));
        ctx.lineTo(tipX - headLen * Math.cos(angle + 0.4), tipY - headLen * Math.sin(angle + 0.4));
        ctx.closePath();
        ctx.fill();

        // Draggable tip handle
        ctx.fillStyle = b.color || '#fff';
        ctx.globalAlpha = 0.85;
        ctx.beginPath();
        ctx.arc(tipX, tipY, 5, 0, Math.PI * 2);
        ctx.fill();
        ctx.strokeStyle = '#fff';
        ctx.lineWidth = 1;
        ctx.globalAlpha = 0.5;
        ctx.stroke();

        ctx.restore();
      }
    }

    ctx.restore(); // end camera transform
  }

  // Rigel blind overlay sits on top of the camera transform in screen space
  drawBlindOverlay();

  // FPS
  frameCount++;
  if (t - lastFpsTime > 500) {
    fps = Math.round(frameCount / ((t - lastFpsTime) / 1000));
    frameCount = 0;
    lastFpsTime = t;
    document.getElementById('status-fps').textContent = 'FPS: ' + fps;
    // Update stellar phase labels
    for (const b of bodies) {
      if (b.isSun) {
        const el = document.getElementById('phase-' + b.id);
        if (el) el.textContent = getPhaseLabel(b);
      }
    }
  }
  document.getElementById('status-bodies').textContent = 'Bodies: ' + bodies.length;

  requestAnimationFrame(loop);
}

// ---- Controls ----
function buildControls() {
  // Suns
  const sunEl = document.getElementById('sun-controls');
  const suns = bodies.filter(b => b.isSun);
  if (suns.length === 0) {
    sunEl.innerHTML = '<p style="color:#555;font-size:0.8em;padding:8px">No suns. Click "Add Sun" to create one.</p>';
  } else {
    let sunHtml = '';
    for (const s of suns) {
      const vmul = s.velMul !== undefined ? s.velMul : 1;
      const sunLockCls = s.locked ? 'lock-btn locked' : 'lock-btn';
      const sunLockIcon = s.locked ? '🔒' : '🔓';
      sunHtml += `
      <div class="body-card" id="card-${s.id}">
        <div class="body-card-header">
          <span class="body-name"><span class="body-dot" onclick="cameraGoTo('${s.id}')" style="color:${s.color};background:${s.color};cursor:pointer" title="Focus camera"></span><span onclick="renameBody('${s.id}')" style="cursor:pointer" title="Click to rename">${s.name}</span></span>
          <div class="card-actions">
            <button class="orbit-btn" onclick="orbitBody('${s.id}')" title="Orbit another body">⟳</button>
            <button class="${sunLockCls}" onclick="toggleLock('${s.id}')" title="${s.locked ? 'Unlock' : 'Lock in place'}">${sunLockIcon}</button>
            <button class="remove-btn" onclick="removeSun('${s.id}')" title="Remove">✕</button>
          </div>
        </div>
        <div style="font-size:0.7em;color:#777;margin-bottom:6px;letter-spacing:0.3px" id="phase-${s.id}">${getPhaseLabel(s)}</div>
        <div class="slider-group">
          <div class="slider-label"><span>Mass</span><span class="slider-value" id="mass-val-${s.id}">${formatMass(s.mass)}</span></div>
          <input type="range" min="1.9031" max="14" step="0.01" value="${Math.log10(Math.max(80, s.mass))}"
            oninput="updateSunMass('${s.id}', Math.pow(10, parseFloat(this.value)))">
        </div>
        <div class="slider-group">
          <div class="slider-label"><span>Velocity</span><span class="slider-value" id="vel-val-${s.id}">${vmul.toFixed(2)}×</span></div>
          <input type="range" min="0" max="3" step="0.05" value="${vmul}"
            oninput="updateSunVel('${s.id}',this.value)">
        </div>
      </div>`;
    }
    sunEl.innerHTML = sunHtml;
  }

  // Planets
  const pc = document.getElementById('planet-controls');
  // Asteroids are excluded from the body card list — a belt of hundreds
  // would overwhelm the panel and they have no per-instance settings to tweak.
  const planets = bodies.filter(b => !b.isSun && !b.isAsteroid);
  if (planets.length === 0) {
    pc.innerHTML = '<p style="color:#555;font-size:0.8em;padding:8px">No planets. Click "Add Planet" to create one.</p>';
    populateBodySelect();
    return;
  }
  let html = '';
  for (const p of planets) {
    const vmul = p.velMul !== undefined ? p.velMul : 1;
    const isMoon = p.isMoon === true;
    const isDwarfStar   = !isMoon && p.mass > 50;
    const nameLow = (p.name || '').toLowerCase();
    const isDwarfPlanet = !isMoon && (
      (p.mass >= DWARF_PLANET_MIN_MASS && p.mass <= DWARF_PLANET_MAX_MASS) ||
      NAMED_DWARF_PLANETS.has(nameLow)
    );
    const isPlanet      = !isMoon && !isDwarfStar && !isDwarfPlanet;
    const planetLockCls = p.locked ? 'lock-btn locked' : 'lock-btn';
    const planetLockIcon = p.locked ? '🔒' : '🔓';
    let typeLabel = '';
    if (isDwarfStar)        typeLabel = '<div style="font-size:0.7em;color:#a78bfa;margin-bottom:6px;letter-spacing:0.3px">◐ Dwarf Star</div>';
    else if (isDwarfPlanet) typeLabel = '<div style="font-size:0.7em;color:#9ca3af;margin-bottom:6px;letter-spacing:0.3px">◌ Dwarf Planet</div>';
    else if (isMoon)        typeLabel = '<div style="font-size:0.7em;color:#a0a4ad;margin-bottom:6px;letter-spacing:0.3px">🌑 Moon</div>';
    else if (isPlanet)      typeLabel = '<div style="font-size:0.7em;color:#7dd3fc;margin-bottom:6px;letter-spacing:0.3px">🪐 Planet</div>';
    html += `
      <div class="body-card" id="card-${p.id}">
        <div class="body-card-header">
          <span class="body-name"><span class="body-dot" onclick="cameraGoTo('${p.id}')" style="color:${p.color};background:${p.color};cursor:pointer" title="Focus camera"></span><span onclick="renameBody('${p.id}')" style="cursor:pointer" title="Click to rename">${p.name}</span></span>
          <div class="card-actions">
            <button class="moon-btn" onclick="addMoonTo('${p.id}')" title="Add a moon orbiting this planet">🌑</button>
            <button class="orbit-btn" onclick="orbitBody('${p.id}')" title="Orbit another body">⟳</button>
            <button class="${planetLockCls}" onclick="toggleLock('${p.id}')" title="${p.locked ? 'Unlock' : 'Lock in place'}">${planetLockIcon}</button>
            <button class="remove-btn" onclick="removePlanet('${p.id}')" title="Remove">✕</button>
          </div>
        </div>
        ${typeLabel}
        <div class="slider-group">
          <div class="slider-label"><span>Mass</span><span class="slider-value" id="mass-val-${p.id}">${fmtPlanetMass(p.mass)}</span></div>
          <input type="range" min="-7" max="1.9" step="0.01" value="${Math.log10(Math.max(1e-7, p.mass))}"
            oninput="updatePlanetMass('${p.id}', Math.pow(10, parseFloat(this.value)))">
        </div>
        <div class="slider-group">
          <div class="slider-label"><span>Velocity</span><span class="slider-value" id="vel-val-${p.id}">${vmul.toFixed(2)}×</span></div>
          <input type="range" min="0.1" max="3" step="0.05" value="${vmul}"
            oninput="updatePlanetVel('${p.id}',this.value)">
        </div>
      </div>`;
  }
  pc.innerHTML = html;
  populateBodySelect();
}

function updateSunMass(id, v) {
  const sun = bodies.find(b => b.id === id);
  if (sun) {
    const newMass = parseFloat(v);
    sun.mass = newMass;
    sun.radius = 28 + Math.cbrt(sun.mass / 1000) * 4;
    const el = document.getElementById('mass-val-' + id);
    if (el) el.textContent = formatMass(sun.mass);
    // Black holes stay as black holes
    const p = sun.stellarPhase;
    if (p === 'black-hole' || p === 'evaporating') {
      sun.radius = 12 + Math.cbrt(sun.mass / 1000) * 3;
      return;
    }
    // Reset other evolved phases back to main sequence
    const evolved = ['white-dwarf','black-dwarf','red-giant','neutron-star','nebula','supernova','collapsing'];
    if (evolved.includes(p)) {
      sun.stellarPhase = 'main-sequence';
      sun.createdAtSim = simTime;
      delete sun.whiteDwarfAtSim;
      delete sun.redGiantAtSim;
      delete sun.phaseAtSim;
    }
    // Mass dictates star color (red → orange → yellow → light blue → dark blue)
    sun.color = getStarColor(sun.mass);
    const card = document.getElementById('card-' + id);
    if (card) {
      const dot = card.querySelector('.body-dot');
      if (dot) { dot.style.color = sun.color; dot.style.background = sun.color; }
    }
  }
}

function updateSunVel(id, v) {
  const s = bodies.find(b => b.id === id);
  if (s) {
    const oldMul = s.velMul || 1;
    const newMul = parseFloat(v);
    if (oldMul > 0.001) {
      const scale = newMul / oldMul;
      s.vx *= scale;
      s.vy *= scale;
    }
    s.velMul = newMul;
    const el = document.getElementById('vel-val-' + id);
    if (el) el.textContent = newMul.toFixed(2) + '×';
  }
}

function removeSun(id) {
  // If this body is the centre of a galaxy, remove the galaxy too so we
  // don't leave an orphan visual without its anchor.
  galaxies = galaxies.filter(g => g.centerBodyId !== id);
  const idx = bodies.findIndex(b => b.id === id);
  if (idx !== -1) {
    bodies.splice(idx, 1);
    buildControls();
  }
}

// Format a planet's mass for the slider readout. Real Sun:planet ratios span
// 7+ orders of magnitude (Pluto ≈ 7e-6 → dwarf stars > 50), so the formatter
// switches to scientific notation for very small values.
function fmtPlanetMass(m) {
  if (m >= 1)    return m.toFixed(2);
  if (m >= 0.01) return m.toFixed(3);
  return m.toExponential(2);
}

// Jupiter mass in sim units. Sun mass = 1000; Sun:Jupiter mass ratio ≈ 1047.35.
const JUPITER_MASS_SIM = 1000 / 1047.35;
// Planet spawner allowed mass band, in sim units.
//   Min: 0.0000002514 × Sun mass = 2.514e-7 × 1000 = 2.514e-4 sim units (~Mars-class).
//   Max: 8 × Jupiter mass                          ≈ 7.638 sim units (sub-deuterium-burning).
const PLANET_MIN_MASS = 2.514e-7 * 1000;
const PLANET_MAX_MASS = 8 * JUPITER_MASS_SIM;
// Dwarf-planet (brown-dwarf-ish) band: 13–80 × Jupiter mass.
const DWARF_PLANET_MIN_MASS = 13 * JUPITER_MASS_SIM;
const DWARF_PLANET_MAX_MASS = 80 * JUPITER_MASS_SIM;
// Real solar-system dwarf planets. Names matched case-insensitively in the
// body-card classifier so a body called "Pluto" / "Ceres" / etc. always
// reads as ◌ Dwarf Planet, regardless of how the mass-band knobs are set.
const NAMED_DWARF_PLANETS = new Set([
  'pluto', 'ceres', 'eris', 'haumea', 'makemake', 'sedna', 'gonggong', 'quaoar', 'orcus'
]);

function updatePlanetMass(id, v) {
  const p = bodies.find(b => b.id === id);
  if (p) {
    const nameLow = (p.name || '').toLowerCase();
    const nameDwarf = NAMED_DWARF_PLANETS.has(nameLow);
    const wasDwarfStar = p.mass > 50;
    const wasDwarfPlanet = (p.mass >= DWARF_PLANET_MIN_MASS && p.mass <= DWARF_PLANET_MAX_MASS) || nameDwarf;
    p.mass = Math.max(1e-8, parseFloat(v));
    p.radius = 3 + Math.cbrt(p.mass) * 2.2;
    const el = document.getElementById('mass-val-' + id);
    if (el) el.textContent = fmtPlanetMass(p.mass);
    // Re-render controls when crossing the dwarf-star or dwarf-planet threshold
    const isDwarfStar = p.mass > 50;
    const isDwarfPlanet = (p.mass >= DWARF_PLANET_MIN_MASS && p.mass <= DWARF_PLANET_MAX_MASS) || nameDwarf;
    if (wasDwarfStar !== isDwarfStar || wasDwarfPlanet !== isDwarfPlanet) buildControls();
  }
}

function updatePlanetVel(id, v) {
  const p = bodies.find(b => b.id === id);
  if (p) {
    const oldMul = p.velMul || 1;
    const newMul = parseFloat(v);
    const scale = newMul / oldMul;
    p.vx *= scale;
    p.vy *= scale;
    p.velMul = newMul;
    const el = document.getElementById('vel-val-' + id);
    if (el) el.textContent = newMul.toFixed(2) + '×';
  }
}

function addSun() {
  showAddSunModal();
}

function showAddSunModal() {
  const defaultName = 'Sun ' + nextSunId;
  const defaultColor = '#ffb347';

  const overlay = document.createElement('div');
  overlay.id = 'add-sun-overlay';
  overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.7);z-index:20000;display:flex;align-items:center;justify-content:center;backdrop-filter:blur(6px)';

  overlay.innerHTML = `
    <div style="background:linear-gradient(160deg,rgba(20,20,45,0.97),rgba(12,12,30,0.99));border:1px solid rgba(255,255,255,0.1);border-radius:16px;padding:28px;width:320px;box-shadow:0 20px 60px rgba(0,0,0,0.7);font-family:'Inter',sans-serif">
      <h3 style="margin:0 0 20px;color:#fff;font-size:1.15em;font-weight:700">☀ New Sun</h3>
      <div style="margin-bottom:14px">
        <label style="display:block;font-size:0.75em;color:#888;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px">Name</label>
        <input id="new-sun-name" type="text" value="${defaultName}" style="width:100%;padding:10px 12px;border-radius:8px;border:1px solid rgba(255,255,255,0.12);background:rgba(255,255,255,0.06);color:#fff;font-family:'Inter',sans-serif;font-size:0.95em;outline:none" />
      </div>
      <div style="margin-bottom:20px">
        <label style="display:block;font-size:0.75em;color:#888;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px">Color</label>
        <div style="display:flex;align-items:center;gap:10px">
          <input id="new-sun-color" type="color" value="${defaultColor}" style="width:48px;height:36px;border:none;border-radius:8px;cursor:pointer;background:transparent" />
          <span id="new-sun-color-label" style="color:#aaa;font-size:0.85em;font-family:monospace">${defaultColor}</span>
        </div>
      </div>
      <div style="display:flex;gap:8px;justify-content:flex-end">
        <button id="sun-modal-cancel" style="padding:8px 18px;border-radius:8px;border:1px solid rgba(255,255,255,0.1);background:rgba(255,255,255,0.04);color:#aaa;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em">Cancel</button>
        <button id="sun-modal-create" style="padding:8px 18px;border-radius:8px;border:1px solid rgba(255,180,70,0.3);background:rgba(255,180,70,0.12);color:#ffb347;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em;font-weight:600">Create</button>
      </div>
    </div>`;

  document.body.appendChild(overlay);
  const nameInput = document.getElementById('new-sun-name');
  nameInput.select();

  document.getElementById('new-sun-color').addEventListener('input', function() {
    document.getElementById('new-sun-color-label').textContent = this.value;
  });

  document.getElementById('sun-modal-cancel').addEventListener('click', () => overlay.remove());
  overlay.addEventListener('click', (e) => { if (e.target === overlay) overlay.remove(); });

  document.getElementById('sun-modal-create').addEventListener('click', () => {
    const name = nameInput.value.trim() || defaultName;
    const color = document.getElementById('new-sun-color').value;
    spawnSun(name, color);
    overlay.remove();
  });

  nameInput.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') document.getElementById('sun-modal-create').click();
    if (e.key === 'Escape') overlay.remove();
  });
}

function spawnSun(name, color) {
  // Place near the most massive sun with a slight offset
  const primarySun = bodies.filter(b => b.isSun).sort((a, b) => b.mass - a.mass)[0];
  const cx0 = primarySun ? primarySun.x + 200 + Math.random() * 100 : canvas.clientWidth / 2;
  const cy0 = primarySun ? primarySun.y + (Math.random() - 0.5) * 200 : canvas.clientHeight / 2;

  // Easter egg: named supermassive black holes spawn pre-collapsed.
  // (NAMED_BHS hoisted to module scope so renameBody can use it too.)
  const normName = (name || '').trim().toLowerCase();
  if (NAMED_BHS[normName]) {
    const cfg = NAMED_BHS[normName];
    const pos = findFreeSpawnPos(cx0, cy0, cfg.radius);
    bodies.push({
      id: 'sun-' + nextSunId,
      name: name,
      isSun: true,
      x: pos.x, y: pos.y, vx: 0, vy: 0,
      mass: cfg.mass,
      radius: cfg.radius,
      color: '#000000', trail: [], velMul: 1,
      createdAtSim: simTime,
      stellarPhase: 'black-hole', phaseAtSim: simTime,
      accretionRing: []
    });
    nextSunId++;
    buildControls();
    triggerMergeFlash();
    return;
  }

  const sunRadius = 28 + Math.cbrt(500 / 1000) * 4;
  const pos = findFreeSpawnPos(cx0, cy0, sunRadius);
  bodies.push({
    id: 'sun-' + nextSunId,
    name: name,
    isSun: true,
    x: pos.x, y: pos.y, vx: 0, vy: 0,
    mass: 500, radius: sunRadius,
    color: getStarColor(500), trail: [], velMul: 1,
    createdAtSim: simTime
  });
  nextSunId++;
  buildControls();
}

function removePlanet(id) {
  // Same orphan-galaxy cleanup as for suns
  galaxies = galaxies.filter(g => g.centerBodyId !== id);
  const idx = bodies.findIndex(b => b.id === id);
  if (idx !== -1) {
    bodies.splice(idx, 1);
    buildControls();
  }
}

function addPlanet() {
  showAddPlanetModal();
}

function showAddPlanetModal() {
  const defaultColor = PALETTE[nextPlanetId % PALETTE.length];
  const defaultName = 'Planet ' + nextPlanetId;

  // Create modal overlay
  const overlay = document.createElement('div');
  overlay.id = 'add-planet-overlay';
  overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.7);z-index:20000;display:flex;align-items:center;justify-content:center;backdrop-filter:blur(6px)';

  const logMin = Math.log10(PLANET_MIN_MASS);
  const logMax = Math.log10(PLANET_MAX_MASS);
  const defaultLog = (logMin + logMax) / 2;
  const defaultMass = Math.pow(10, defaultLog);
  overlay.innerHTML = `
    <div style="background:linear-gradient(160deg,rgba(20,20,45,0.97),rgba(12,12,30,0.99));border:1px solid rgba(255,255,255,0.1);border-radius:16px;padding:28px;width:320px;box-shadow:0 20px 60px rgba(0,0,0,0.7);font-family:'Inter',sans-serif">
      <h3 style="margin:0 0 20px;color:#fff;font-size:1.15em;font-weight:700">✦ New Planet</h3>
      <div style="margin-bottom:14px">
        <label style="display:block;font-size:0.75em;color:#888;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px">Name</label>
        <input id="new-planet-name" type="text" value="${defaultName}" style="width:100%;padding:10px 12px;border-radius:8px;border:1px solid rgba(255,255,255,0.12);background:rgba(255,255,255,0.06);color:#fff;font-family:'Inter',sans-serif;font-size:0.95em;outline:none" />
      </div>
      <div style="margin-bottom:14px">
        <label style="display:flex;justify-content:space-between;font-size:0.75em;color:#888;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px"><span>Mass</span><span id="new-planet-mass-val" style="color:#bbb;font-variant-numeric:tabular-nums"></span></label>
        <input id="new-planet-mass" type="range" min="${logMin}" max="${logMax}" step="0.01" value="${defaultLog}" style="width:100%;cursor:pointer" />
        <div style="font-size:0.65em;color:#666;margin-top:3px">${fmtPlanetMass(PLANET_MIN_MASS)} → ${fmtPlanetMass(PLANET_MAX_MASS)} (2.514×10⁻⁷ M☉ → 8 M♃)</div>
      </div>
      <div style="margin-bottom:14px">
        <label style="display:flex;justify-content:space-between;font-size:0.75em;color:#888;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px"><span>Distance</span><span id="new-planet-dist-val" style="color:#bbb;font-variant-numeric:tabular-nums"></span></label>
        <input id="new-planet-dist" type="range" min="-1.3" max="2.5" step="0.01" value="0" style="width:100%;cursor:pointer" />
        <div style="font-size:0.65em;color:#666;margin-top:3px">0.05 AU → ~316 AU (log scale; 1.0 = Earth distance)</div>
      </div>
      <div style="margin-bottom:20px">
        <label style="display:block;font-size:0.75em;color:#888;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px">Color</label>
        <div style="display:flex;align-items:center;gap:10px">
          <input id="new-planet-color" type="color" value="${defaultColor}" style="width:48px;height:36px;border:none;border-radius:8px;cursor:pointer;background:transparent" />
          <span id="new-planet-color-label" style="color:#aaa;font-size:0.85em;font-family:monospace">${defaultColor}</span>
        </div>
      </div>
      <div style="display:flex;gap:8px;justify-content:flex-end">
        <button id="modal-cancel" style="padding:8px 18px;border-radius:8px;border:1px solid rgba(255,255,255,0.1);background:rgba(255,255,255,0.04);color:#aaa;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em">Cancel</button>
        <button id="modal-create" style="padding:8px 18px;border-radius:8px;border:1px solid rgba(80,220,120,0.3);background:rgba(80,220,120,0.12);color:#6ee7a0;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em;font-weight:600">Create</button>
      </div>
    </div>`;

  document.body.appendChild(overlay);

  // Focus name input
  const nameInput = document.getElementById('new-planet-name');
  nameInput.select();

  // Update color label on change
  document.getElementById('new-planet-color').addEventListener('input', function() {
    document.getElementById('new-planet-color-label').textContent = this.value;
  });

  // Update mass readout live as the user drags the slider
  const massInput = document.getElementById('new-planet-mass');
  const massVal   = document.getElementById('new-planet-mass-val');
  function refreshMassLabel() {
    const m = Math.pow(10, parseFloat(massInput.value));
    massVal.textContent = fmtPlanetMass(m);
  }
  massInput.addEventListener('input', refreshMassLabel);
  refreshMassLabel();

  // Distance slider: log-scale value is in AU, -1.3 → 2.5 (≈ 0.05 → 316 AU).
  const distInput = document.getElementById('new-planet-dist');
  const distVal   = document.getElementById('new-planet-dist-val');
  function refreshDistLabel() {
    const au = Math.pow(10, parseFloat(distInput.value));
    distVal.textContent = (au >= 10 ? au.toFixed(1) : au.toFixed(2)) + ' AU';
  }
  distInput.addEventListener('input', refreshDistLabel);
  refreshDistLabel();

  // Cancel
  document.getElementById('modal-cancel').addEventListener('click', () => overlay.remove());
  overlay.addEventListener('click', (e) => { if (e.target === overlay) overlay.remove(); });

  // Create
  document.getElementById('modal-create').addEventListener('click', () => {
    const name = nameInput.value.trim() || defaultName;
    const color = document.getElementById('new-planet-color').value;
    const mass  = Math.pow(10, parseFloat(massInput.value));
    const distAU = Math.pow(10, parseFloat(distInput.value));
    spawnPlanet(name, color, mass, distAU);
    overlay.remove();
  });

  // Enter key to create
  nameInput.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') { document.getElementById('modal-create').click(); }
    if (e.key === 'Escape') { overlay.remove(); }
  });
}

// Asteroid mass + size bands, in sim units.
//
// Mass range (per user spec): 1.57×10¹² tons → 1.57×10¹⁵ tons.
//   1 sim mass unit = Sun mass / 1000 = 1.989×10²⁷ kg = 1.989×10²⁴ tons,
//   so the band in sim units is 7.89×10⁻¹³ → 7.89×10⁻¹⁰.
//
// Size range (per user spec): 1 m → 1000 km.
//   1 sim length unit = Sun radius / 28 = 695,700 km / 28 ≈ 24,846 km,
//   so the band is 4.02×10⁻⁸ → 4.02×10⁻².
//
// Each asteroid picks a single log-uniform "size factor" in [0, 1] and uses
// it for BOTH mass and radius — bigger rocks are heavier, smaller ones are
// lighter, matching the way the user paired the bounds.
const ASTEROID_MASS_MIN_SIM   = 1.57e12 * 1000 / 1.989e27;  // ≈ 7.89e-13
const ASTEROID_MASS_MAX_SIM   = 1.57e15 * 1000 / 1.989e27;  // ≈ 7.89e-10
const ASTEROID_RADIUS_MIN_SIM = 0.001 / 24846;              // 1 m,    ≈ 4.02e-8
const ASTEROID_RADIUS_MAX_SIM = 1000  / 24846;              // 1000 km,≈ 4.02e-2

// Asteroid belt spawn. Picks K "clump anchors" around the ring and spawns
// asteroids tightly around each one (Box–Muller Gaussians on both angle and
// radius) so the belt reads as a handful of dense knots instead of a uniform
// thin ring. Each asteroid gets the circular orbital velocity for its actual
// distance plus a small randomization for natural eccentricity.
// Asteroids are flagged `isAsteroid` so they skip trails, body cards, and
// the equation-bar dropdown.
function spawnAsteroidBelt(count = 500, centerAU = 2.7, radialSigmaAU = 0.08) {
  const sun = bodies.find(b => b.isSun);
  if (!sun) return;
  const cx = sun.x, cy = sun.y;
  const sunMass = sun.mass;
  const greys = ['#7d7060', '#8b7e6c', '#9a8a7a', '#a89080', '#aaa', '#857668', '#736655', '#a09080'];
  const logRMin = Math.log10(ASTEROID_RADIUS_MIN_SIM);
  const logRMax = Math.log10(ASTEROID_RADIUS_MAX_SIM);
  const logMMin = Math.log10(ASTEROID_MASS_MIN_SIM);
  const logMMax = Math.log10(ASTEROID_MASS_MAX_SIM);

  // Standard-normal sample via Box–Muller. Used to give each clump a fuzzy
  // Gaussian halo in both radius and angle.
  const gauss = () => {
    const u1 = Math.random() || 1e-9;
    const u2 = Math.random();
    return Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);
  };

  // Pick a handful of clump centers around the ring.
  const NUM_CLUMPS = 8;
  const ANGULAR_SIGMA = 0.04;  // ≈ 2.3°  → tight angular cluster
  const clumpAngles = [];
  for (let i = 0; i < NUM_CLUMPS; i++) {
    clumpAngles.push(Math.random() * Math.PI * 2);
  }

  for (let i = 0; i < count; i++) {
    const clumpAngle = clumpAngles[i % NUM_CLUMPS];
    const angle  = clumpAngle + gauss() * ANGULAR_SIGMA;
    const auDist = centerAU   + gauss() * radialSigmaAU;
    if (auDist <= 0) continue;
    const dist   = _AU_SIM_UNITS * auDist;
    const orbV   = Math.sqrt(G_BASE * sunMass / dist);
    const speedJitter = 0.96 + Math.random() * 0.08;   // tighter velocity spread = clumps drift less
    const color  = greys[Math.floor(Math.random() * greys.length)];
    // Shared size factor so radius and mass correlate (bigger = heavier).
    const sizeFactor = Math.random();
    const radius = Math.pow(10, logRMin + sizeFactor * (logRMax - logRMin));
    const mass   = Math.pow(10, logMMin + sizeFactor * (logMMax - logMMin));
    bodies.push({
      id: 'asteroid-' + (nextAsteroidId++),
      name: 'Asteroid ' + nextAsteroidId,
      isSun: false,
      isAsteroid: true,
      x: cx + Math.cos(angle) * dist,
      y: cy + Math.sin(angle) * dist,
      vx: -Math.sin(angle) * orbV * speedJitter,
      vy:  Math.cos(angle) * orbV * speedJitter,
      mass,
      radius,
      color,
      trail: [],
      velMul: 1
    });
  }
  buildControls();
}

function addAsteroidBelt() {
  spawnAsteroidBelt();
}

// Wipe every asteroid currently in the scene (leaves suns, planets, moons
// untouched). Useful when a belt has filled up and you want a clean view.
function removeAsteroidBelt() {
  const before = bodies.length;
  bodies = bodies.filter(b => !b.isAsteroid);
  if (bodies.length !== before) buildControls();
}

// Comet mass + size bands, in sim units.
//   Mass: 5×10⁹ kg → 5×10¹² kg = 2.51×10⁻¹⁸ → 2.51×10⁻¹⁵ sim units.
//   Radius: 0.5 km → 10 km        = 2.01×10⁻⁵ → 4.02×10⁻⁴ sim units.
const COMET_MASS_MIN_SIM   = 5e9  / 1.989e27;
const COMET_MASS_MAX_SIM   = 5e12 / 1.989e27;
const COMET_RADIUS_MIN_SIM = 0.5  / 24846;
const COMET_RADIUS_MAX_SIM = 10   / 24846;

// Real-world named comets. periodYears must be ≥ 0; orbit shape is recovered
// from period + eccentricity via Kepler's third law in spawnComet().
const NAMED_COMETS = {
  'halley':         { periodYears: 76,    eccentricity: 0.967 },
  // Easy to extend (e.g. 'hale-bopp': { periodYears: 2533, eccentricity: 0.995 }).
};

// Names that resolve to Shoemaker–Levy 9 (collision-course comet → Jupiter).
// Normalized by lower-casing and stripping whitespace / dashes / underscores.
const SL9_NAME_KEYS = new Set([
  'shoemakerlevy9', 'shoemakerlevy', 'sl9', 'shoemakerlevynine'
]);
function _normCometName(s) {
  return (s || '').toLowerCase().replace(/[\s\-_]/g, '');
}

// Spawn a Shoemaker–Levy 9-style comet inbound to Jupiter. The real S-L 9
// impacted Jupiter in 1994 after being shredded by tidal forces on a prior
// pass; we model the post-shred bare nucleus and just hurl it in.
function spawnShoemakerLevy9() {
  const jupiter = bodies.find(b => (b.name || '').toLowerCase() === 'jupiter');
  if (!jupiter) { alert('No body named "Jupiter" — name a planet Jupiter first.'); return; }
  // Start ~80 Jupiter-radii away, with velocity pointing roughly at Jupiter
  // (inheriting Jupiter's orbital velocity so the collision happens in
  // Jupiter's frame, not the Sun's).
  const startDist = Math.max(jupiter.radius * 80, _AU_SIM_UNITS * 0.05);
  const angle = Math.random() * Math.PI * 2;
  const sx = jupiter.x + Math.cos(angle) * startDist;
  const sy = jupiter.y + Math.sin(angle) * startDist;
  const dx = jupiter.x - sx, dy = jupiter.y - sy;
  const dist = Math.sqrt(dx * dx + dy * dy);
  const ux = dx / dist, uy = dy / dist;
  // Inward speed: half escape velocity at start distance — guarantees impact
  // once gravity gets involved, and gives a dramatic approach.
  const vEsc  = Math.sqrt(2 * G_BASE * jupiter.mass / startDist);
  const vIn   = vEsc * 0.5;
  const sun = bodies.find(b => b.isSun);
  const sunMass = sun ? sun.mass : 1000;
  // Mass + radius — pick a mid-size comet (around the average of the band).
  const lerpLog = (a0, a1, sf) => Math.pow(10, Math.log10(a0) + sf * (Math.log10(a1) - Math.log10(a0)));
  const mass   = lerpLog(COMET_MASS_MIN_SIM,   COMET_MASS_MAX_SIM,   0.6);
  const radius = lerpLog(COMET_RADIUS_MIN_SIM, COMET_RADIUS_MAX_SIM, 0.6);
  const id = nextCometId++;
  bodies.push({
    id: 'comet-' + id,
    name: 'Shoemaker-Levy 9',
    isSun: false,
    isComet: true,
    x: sx, y: sy,
    vx: jupiter.vx + ux * vIn,
    vy: jupiter.vy + uy * vIn,
    mass, radius,
    color: '#eaf2ff',
    trail: [], velMul: 1
  });
  buildControls();
}

// Spawn a single comet on an eccentric oval orbit around the primary sun.
// We place it at aphelion and give it the vis-viva velocity for that point
// (perpendicular to the sun-comet vector), which produces a clean ellipse
// with the chosen semi-major axis and eccentricity — exactly the shape in
// the user's reference picture. Pass a name string ("halley", etc.) to
// reproduce a real comet's orbital period.
function spawnComet(nameOverride) {
  // Special-case: Shoemaker–Levy 9 short-circuits to a Jupiter-impactor.
  if (nameOverride && SL9_NAME_KEYS.has(_normCometName(nameOverride))) {
    spawnShoemakerLevy9();
    return;
  }
  const sun = bodies.find(b => b.isSun);
  if (!sun) return;
  const sunMass = sun.mass;
  let a_AU, e;
  const named = nameOverride && NAMED_COMETS[nameOverride.toLowerCase()];
  if (named) {
    // Solve a from period via Kepler: T² = 4π² · a³ / (G · M).
    // 1 sim year = _EARTH_ORBIT_PERIOD_DT physics-dt at 1× speed.
    const T = named.periodYears * _EARTH_ORBIT_PERIOD_DT;
    const a3 = (T * T) * G_BASE * sunMass / (4 * Math.PI * Math.PI);
    const aSim = Math.cbrt(a3);
    a_AU = aSim / _AU_SIM_UNITS;
    e = named.eccentricity;
  } else {
    // Highly elliptical orbit, semi-major axis 8–38 AU, e in [0.65, 0.95].
    a_AU = 8 + Math.random() * 30;
    e    = 0.65 + Math.random() * 0.30;
  }
  const a = _AU_SIM_UNITS * a_AU;
  const r_apo = a * (1 + e);
  const v_apo = Math.sqrt(G_BASE * sunMass * (1 - e) / (a * (1 + e)));
  const angle = Math.random() * Math.PI * 2;

  // Mass + radius correlated via a single log-uniform size factor.
  const sf = Math.random();
  const lerpLog = (a0, a1) => Math.pow(10, Math.log10(a0) + sf * (Math.log10(a1) - Math.log10(a0)));
  const mass   = lerpLog(COMET_MASS_MIN_SIM,   COMET_MASS_MAX_SIM);
  const radius = lerpLog(COMET_RADIUS_MIN_SIM, COMET_RADIUS_MAX_SIM);

  const id = nextCometId++;
  // Preserve the user-provided casing for named comets ("Halley", not "halley").
  const finalName = nameOverride ? nameOverride : 'Comet ' + id;
  bodies.push({
    id: 'comet-' + id,
    name: finalName,
    isSun: false,
    isComet: true,
    x: sun.x + Math.cos(angle) * r_apo,
    y: sun.y + Math.sin(angle) * r_apo,
    vx: -Math.sin(angle) * v_apo,
    vy:  Math.cos(angle) * v_apo,
    mass,
    radius,
    color: '#eaf2ff',
    trail: [],
    velMul: 1
  });
  buildControls();
}

function addComet() { spawnComet(); }

function removeComets() {
  const before = bodies.length;
  bodies = bodies.filter(b => !b.isComet);
  if (bodies.length !== before) buildControls();
}

function spawnPlanet(name, color, massOverride, distAU) {
  const sun = bodies.find(b => b.isSun);
  const cx = sun ? sun.x : canvas.clientWidth / 2;
  const cy = sun ? sun.y : canvas.clientHeight / 2;
  const sunMass = sun ? sun.mass : 1000;

  // Distance: if the caller specified an AU value (Add Planet modal), use it
  // exactly; otherwise roll a random distance in the inner-system range.
  const distAUFinal = (isFinite(distAU) && distAU > 0)
    ? distAU
    : (0.3 + Math.random() * 4.7);
  const dist = _AU_SIM_UNITS * distAUFinal;
  const angle = Math.random() * Math.PI * 2;
  // Mass clamped to the planet spawner's allowed range
  // [2.514e-7 × Sun, 8 × Jupiter]. If no explicit mass was passed, roll one
  // log-uniformly inside the band so the slider's default still produces a
  // varied mix of small/large planets.
  const mass = massOverride != null
    ? Math.max(PLANET_MIN_MASS, Math.min(PLANET_MAX_MASS, massOverride))
    : (() => {
        const logMin = Math.log10(PLANET_MIN_MASS);
        const logMax = Math.log10(PLANET_MAX_MASS);
        return Math.pow(10, logMin + Math.random() * (logMax - logMin));
      })();
  const planetRadius = 3 + Math.cbrt(mass) * 2.2;
  // Find a free spot near the desired orbit point and re-derive orbital
  // velocity based on the actual distance from the sun after nudging.
  const pos = findFreeSpawnPos(cx + Math.cos(angle) * dist, cy + Math.sin(angle) * dist, planetRadius);
  const actDx = pos.x - cx, actDy = pos.y - cy;
  const actDist = Math.sqrt(actDx * actDx + actDy * actDy);
  const actAngle = Math.atan2(actDy, actDx);
  const orbitalV = actDist > 0 ? Math.sqrt(G_BASE * sunMass / actDist) : 0;

  const planet = {
    id: 'planet-' + (nextPlanetId),
    name: name,
    isSun: false,
    x: pos.x,
    y: pos.y,
    vx: -Math.sin(actAngle) * orbitalV,
    vy: Math.cos(actAngle) * orbitalV,
    mass, radius: planetRadius,
    color, trail: [], velMul: 1
  };
  bodies.push(planet);
  nextPlanetId++;
  buildControls();
  applyEarthFeatures(planet);
}

// Give every existing planet its own moon in one click. Each moon gets a
// procedurally-picked moonlike grey/brown color so they're distinguishable.
const MOON_COLORS = ['#b0b0b0', '#9ca3af', '#a89080', '#c2a99a', '#8c8c8c', '#bfae9b'];

// Naming rule for a new moon: "Moon" repeated (depth) times, suffixed with
// "of <root planet name>". Depth 1 → "Moon of Earth"; depth 2 → "Moon Moon of
// Earth"; depth 3 → "Moon Moon Moon of Earth"; etc.
function moonNameFor(parent) {
  const depth = parent.isMoon ? (parent.moonDepth || 1) + 1 : 1;
  const root  = parent.isMoon ? (parent.rootPlanetName || parent.name) : parent.name;
  return new Array(depth).fill('Moon').join(' ') + ' of ' + root;
}

function addMoonTo(planetId) {
  const planet = bodies.find(b => b.id === planetId && !b.isSun);
  if (!planet) return;
  const color = MOON_COLORS[nextPlanetId % MOON_COLORS.length];
  spawnMoon(moonNameFor(planet), color, planet.id);
}

function addMoon() {
  const planets = bodies.filter(b => !b.isSun);
  if (planets.length === 0) {
    alert('Add a planet first — moons need a planet to orbit.');
    return;
  }
  planets.forEach((p, i) => {
    const color = MOON_COLORS[(nextPlanetId + i) % MOON_COLORS.length];
    spawnMoon(moonNameFor(p), color, p.id);
  });
}

// ---- Creator panel ----
// Per-type defaults for the Creator UI. log10(mass) is the slider value so
// the same slider covers planets (mass ~1) and supermassive BHs (mass 1e14).
const CREATOR_DEFAULTS = {
  sun:       { logMass: 3,     color: '#ffb347' },  // 1000
  redgiant:  { logMass: 3.18,  color: '#ff4422' },  // ~1500 (in the 501-2500 RG band)
  planet:    { logMass: 0.7,   color: '#5dade2' },  // ~5
  moon:      { logMass: -0.3,  color: '#c0c0c0' },  // ~0.5
  dwarf:     { logMass: 1.8,   color: '#a78bfa' },  // ~63
  blackhole: { logMass: 5,     color: '#000000' },  // 100,000
  neutron:   { logMass: 3.4,   color: '#ccddff' }   // ~2500
};

function onCreatorTypeChange() {
  const type = document.getElementById('creator-type').value;
  const cfg = CREATOR_DEFAULTS[type];
  if (!cfg) return;
  const massInput = document.getElementById('creator-mass');
  const colorInput = document.getElementById('creator-color');
  massInput.value = cfg.logMass;
  colorInput.value = cfg.color;
  onCreatorMassInput(cfg.logMass);
  document.getElementById('creator-color-label').textContent = cfg.color;
}

function onCreatorMassInput(logVal) {
  const m = Math.pow(10, parseFloat(logVal));
  const label = document.getElementById('creator-mass-val');
  if (label) {
    label.textContent = m >= 1e6 ? (m / 1e6).toFixed(2) + 'M'
                      : m >= 1000 ? (m / 1000).toFixed(2) + 'k'
                      : m >= 1   ? m.toFixed(1)
                                 : m.toFixed(2);
  }
}

function createCustomBody() {
  // Creator section is gated by login; the controls aren't even in the DOM
  // unless the user has authenticated, but check defensively in case this is
  // wired into something else.
  if (!creatorAuthed) {
    showCreatorLogin();
    return;
  }
  const type   = document.getElementById('creator-type').value;
  const name   = (document.getElementById('creator-name').value || '').trim();
  const logVal = parseFloat(document.getElementById('creator-mass').value);
  const mass   = Math.max(0.01, Math.pow(10, logVal));
  const color  = document.getElementById('creator-color').value || '#ffffff';

  if (type === 'moon') {
    const parents = bodies.filter(b => !b.isSun);
    if (parents.length === 0) {
      alert('Add a planet first — moons need a planet to orbit.');
      return;
    }
    const parent = parents.sort((a, b) => b.mass - a.mass)[0];
    const finalName = name || moonNameFor(parent);
    spawnMoon(finalName, color, parent.id);
    const moons = bodies.filter(b => !b.isSun && b.name === finalName);
    if (moons.length) moons[moons.length - 1].mass = mass;
    return;
  }

  if (type === 'planet' || type === 'dwarf') {
    const finalName = name || ('Planet ' + nextPlanetId);
    spawnPlanet(finalName, color);
    const planets = bodies.filter(b => !b.isSun);
    const newPlanet = planets[planets.length - 1];
    if (newPlanet) {
      newPlanet.mass = mass;
      newPlanet.radius = 3 + Math.cbrt(newPlanet.mass) * 2.2;
    }
    buildControls();
    return;
  }

  // Stars, neutron stars, and black holes share the body schema.
  const finalName = name || ('Sun ' + nextSunId);
  const r = 28 + Math.cbrt(mass / 1000) * 4;
  const angle = Math.random() * Math.PI * 2;
  const dist = 150 + Math.random() * 100;
  const cx0 = viewX + Math.cos(angle) * dist;
  const cy0 = viewY + Math.sin(angle) * dist;
  const pos = findFreeSpawnPos(cx0, cy0, r);
  const body = {
    id: 'sun-' + nextSunId,
    name: finalName,
    isSun: true,
    x: pos.x, y: pos.y, vx: 0, vy: 0,
    mass: mass,
    radius: r,
    color: color,
    trail: [], velMul: 1,
    createdAtSim: simTime,
    stellarPhase: 'main-sequence'
  };
  if (type === 'blackhole') {
    body.stellarPhase = 'black-hole';
    body.phaseAtSim = simTime;
    body.accretionRing = [];
    body.color = '#000000';
    body.radius = Math.max(r, 12 + Math.cbrt(mass / 1000) * 3);
  } else if (type === 'neutron') {
    body.stellarPhase = 'neutron-star';
    body.phaseAtSim = simTime;
    body.neutronStartSim = simTime;
    body.radius = 5;
  } else if (type === 'redgiant') {
    // Born straight in the red-giant phase — skips the main sequence.
    body.stellarPhase = 'red-giant';
    body.phaseAtSim = simTime;
    body.redGiantAtSim = simTime;
    // 10% chance it's a red super giant (matches the main-sequence path's roll).
    if (Math.random() < 0.1) body.redSuperGiant = true;
  }
  bodies.push(body);
  nextSunId++;
  buildControls();
  triggerMergeFlash();
}

// Render the Creator section: either a "login to unlock" prompt or the full
// custom-body designer, depending on creatorAuthed. Called on init and any
// time the auth state flips.
function renderCreatorSection() {
  const el = document.getElementById('creator-content');
  if (!el) return;
  if (!creatorAuthed) {
    el.innerHTML = `
      <div style="font-size:0.7em;color:#777;margin-bottom:10px;line-height:1.5">
        Locked — sign in to design custom bodies with full control over type, mass, and color.
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="showCreatorLogin()" style="flex:1">🔐 Creator Login</button>
      </div>`;
    return;
  }
  el.innerHTML = `
    <div style="font-size:0.7em;color:#6ee7a0;margin-bottom:8px">Signed in as Creator</div>
    <div style="font-size:0.7em;color:#777;margin-bottom:10px;line-height:1.5">Design a custom body with full control over its type, mass, and color.</div>
    <div class="slider-group">
      <div class="slider-label"><span>Type</span></div>
      <select id="creator-type" onchange="onCreatorTypeChange()" style="width:100%;background:rgba(255,255,255,0.06);border:1px solid rgba(255,255,255,0.12);border-radius:6px;color:#ccc;padding:6px 8px;font-family:'Inter',sans-serif;font-size:0.85em;outline:none;cursor:pointer">
        <option value="sun">☀ Sun (main sequence)</option>
        <option value="redgiant">🔴 Red Giant</option>
        <option value="planet">🪐 Planet</option>
        <option value="moon">🌑 Moon</option>
        <option value="dwarf">◐ Dwarf Star</option>
        <option value="blackhole">🕳️ Black Hole</option>
        <option value="neutron">💫 Neutron Star</option>
      </select>
    </div>
    <div class="slider-group">
      <div class="slider-label"><span>Name</span></div>
      <input id="creator-name" type="text" placeholder="Auto" style="width:100%;background:rgba(255,255,255,0.06);border:1px solid rgba(255,255,255,0.12);border-radius:6px;color:#ccc;padding:6px 8px;font-family:'Inter',sans-serif;font-size:0.85em;outline:none" />
    </div>
    <div class="slider-group">
      <div class="slider-label"><span>Mass</span><span class="slider-value" id="creator-mass-val">1000</span></div>
      <input id="creator-mass" type="range" min="0" max="14" step="0.01" value="3" oninput="onCreatorMassInput(this.value)" />
    </div>
    <div class="slider-group">
      <div class="slider-label"><span>Color</span></div>
      <div style="display:flex;align-items:center;gap:8px">
        <input id="creator-color" type="color" value="#ffb347" style="width:40px;height:28px;border:none;border-radius:6px;cursor:pointer;background:transparent" />
        <span id="creator-color-label" style="color:#aaa;font-size:0.75em;font-family:monospace">#ffb347</span>
      </div>
    </div>
    <div class="btn-row">
      <button class="btn add-btn" onclick="createCustomBody()" style="flex:1" title="Spawn a body using the type, name, mass, and color set above.">✦ Create</button>
      <button class="btn" onclick="creatorLogout()" title="Sign out of the Creator section">⎋</button>
    </div>`;
  // Re-bind the color picker live-update hook now that the input is in the DOM.
  const cc = document.getElementById('creator-color');
  if (cc) cc.addEventListener('input', () => {
    const lbl = document.getElementById('creator-color-label');
    if (lbl) lbl.textContent = cc.value;
  });
}

function showCreatorLogin() {
  if (document.getElementById('creator-login-overlay')) return;
  const overlay = document.createElement('div');
  overlay.id = 'creator-login-overlay';
  overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.7);z-index:20000;display:flex;align-items:center;justify-content:center;backdrop-filter:blur(6px)';
  overlay.innerHTML = `
    <div style="background:linear-gradient(160deg,rgba(20,20,45,0.97),rgba(12,12,30,0.99));border:1px solid rgba(255,255,255,0.1);border-radius:16px;padding:28px;width:340px;box-shadow:0 20px 60px rgba(0,0,0,0.7);font-family:'Inter',sans-serif">
      <h3 style="margin:0 0 18px;color:#fff;font-size:1.15em;font-weight:700">🔐 Creator Login</h3>
      <div style="margin-bottom:18px">
        <label style="display:block;font-size:0.75em;color:#888;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px">Password</label>
        <input id="creator-password" type="password" autocomplete="off" placeholder="••••••••" style="width:100%;padding:10px 12px;border-radius:8px;border:1px solid rgba(255,255,255,0.12);background:rgba(255,255,255,0.06);color:#fff;font-family:'Inter',sans-serif;font-size:0.95em;outline:none" />
        <div id="creator-login-error" style="display:none;color:#ff8888;font-size:0.78em;margin-top:6px">Incorrect password.</div>
      </div>
      <div style="display:flex;gap:8px;justify-content:flex-end">
        <button id="creator-login-cancel" style="padding:8px 18px;border-radius:8px;border:1px solid rgba(255,255,255,0.1);background:rgba(255,255,255,0.04);color:#aaa;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em">Cancel</button>
        <button id="creator-login-submit" style="padding:8px 18px;border-radius:8px;border:1px solid rgba(110,231,160,0.3);background:rgba(110,231,160,0.12);color:#6ee7a0;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em;font-weight:600">Unlock</button>
      </div>
    </div>`;
  document.body.appendChild(overlay);
  const passInput = document.getElementById('creator-password');
  passInput.focus();
  const close = () => overlay.remove();
  const attempt = () => {
    if ((passInput.value || '') === CREATOR_PASSWORD) {
      creatorAuthed = true;
      try { localStorage.setItem('creatorAuthed', '1'); } catch (_) {}
      renderCreatorSection();
      close();
    } else {
      document.getElementById('creator-login-error').style.display = 'block';
    }
  };
  document.getElementById('creator-login-cancel').addEventListener('click', close);
  document.getElementById('creator-login-submit').addEventListener('click', attempt);
  overlay.addEventListener('click', (e) => { if (e.target === overlay) close(); });
  passInput.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') attempt();
    if (e.key === 'Escape') close();
  });
}

function creatorLogout() {
  creatorAuthed = false;
  try { localStorage.removeItem('creatorAuthed'); } catch (_) {}
  renderCreatorSection();
}

function showAddMoonModal() {
  // Moons orbit planets, not stars — only planets are valid parents.
  const planets = bodies.filter(b => !b.isSun);
  if (planets.length === 0) {
    alert('Add a planet first — moons need a planet to orbit.');
    return;
  }
  const defaultName = 'Moon ' + nextPlanetId;
  const defaultColor = '#b0b0b0';

  const overlay = document.createElement('div');
  overlay.id = 'add-moon-overlay';
  overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.7);z-index:20000;display:flex;align-items:center;justify-content:center;backdrop-filter:blur(6px)';

  // Parent options: only planets (so the moon truly orbits a planet)
  const parentOpts = planets.map(b =>
    `<option value="${b.id}">✦ ${b.name}</option>`
  ).join('');

  // Default parent: the heaviest planet
  const defaultParent = planets.slice().sort((a, b) => b.mass - a.mass)[0];

  overlay.innerHTML = `
    <div style="background:linear-gradient(160deg,rgba(20,20,45,0.97),rgba(12,12,30,0.99));border:1px solid rgba(255,255,255,0.1);border-radius:16px;padding:28px;width:340px;box-shadow:0 20px 60px rgba(0,0,0,0.7);font-family:'Inter',sans-serif">
      <h3 style="margin:0 0 18px;color:#fff;font-size:1.15em;font-weight:700">🌑 New Moon</h3>
      <div style="margin-bottom:14px">
        <label style="display:block;font-size:0.75em;color:#888;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px">Name</label>
        <input id="new-moon-name" type="text" value="${defaultName}" style="width:100%;padding:10px 12px;border-radius:8px;border:1px solid rgba(255,255,255,0.12);background:rgba(255,255,255,0.06);color:#fff;font-family:'Inter',sans-serif;font-size:0.95em;outline:none" />
      </div>
      <div style="margin-bottom:14px">
        <label style="display:block;font-size:0.75em;color:#888;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px">Orbits</label>
        <select id="new-moon-parent" style="width:100%;padding:9px 12px;border-radius:8px;border:1px solid rgba(255,255,255,0.12);background:rgba(255,255,255,0.06);color:#fff;font-family:'Inter',sans-serif;font-size:0.95em;outline:none">${parentOpts}</select>
      </div>
      <div style="margin-bottom:20px">
        <label style="display:block;font-size:0.75em;color:#888;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px">Color</label>
        <div style="display:flex;align-items:center;gap:10px">
          <input id="new-moon-color" type="color" value="${defaultColor}" style="width:48px;height:36px;border:none;border-radius:8px;cursor:pointer;background:transparent" />
          <span id="new-moon-color-label" style="color:#aaa;font-size:0.85em;font-family:monospace">${defaultColor}</span>
        </div>
      </div>
      <div style="display:flex;gap:8px;justify-content:flex-end">
        <button id="moon-modal-cancel" style="padding:8px 18px;border-radius:8px;border:1px solid rgba(255,255,255,0.1);background:rgba(255,255,255,0.04);color:#aaa;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em">Cancel</button>
        <button id="moon-modal-create" style="padding:8px 18px;border-radius:8px;border:1px solid rgba(180,180,180,0.35);background:rgba(180,180,180,0.16);color:#ddd;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em;font-weight:600">Create</button>
      </div>
    </div>`;

  document.body.appendChild(overlay);
  const nameInput = document.getElementById('new-moon-name');
  nameInput.select();
  document.getElementById('new-moon-parent').value = defaultParent.id;
  document.getElementById('new-moon-color').addEventListener('input', function() {
    document.getElementById('new-moon-color-label').textContent = this.value;
  });
  const close = () => overlay.remove();
  document.getElementById('moon-modal-cancel').addEventListener('click', close);
  overlay.addEventListener('click', (e) => { if (e.target === overlay) close(); });
  const submit = () => {
    const name = nameInput.value.trim() || defaultName;
    const color = document.getElementById('new-moon-color').value;
    const parentId = document.getElementById('new-moon-parent').value;
    spawnMoon(name, color, parentId);
    close();
  };
  document.getElementById('moon-modal-create').addEventListener('click', submit);
  nameInput.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') submit();
    if (e.key === 'Escape') close();
  });
}

function spawnMoon(name, color, parentId) {
  const parent = bodies.find(b => b.id === parentId);
  if (!parent) return;
  const mass = 0.1 + Math.random() * 0.4;          // dwarf-planet range
  const moonRadius = 3 + Math.cbrt(mass) * 2.2;
  // Aim for a tight orbit close to the parent's surface
  const dist = parent.radius + 25 + Math.random() * 25;
  const angle = Math.random() * Math.PI * 2;
  const pos = findFreeSpawnPos(parent.x + Math.cos(angle) * dist, parent.y + Math.sin(angle) * dist, moonRadius);
  const actDx = pos.x - parent.x, actDy = pos.y - parent.y;
  const actDist = Math.sqrt(actDx * actDx + actDy * actDy);
  const actAngle = Math.atan2(actDy, actDx);
  const orbV = actDist > 0 ? Math.sqrt(G_BASE * parent.mass / actDist) : 0;
  const moon = {
    id: 'planet-' + nextPlanetId,
    name, isSun: false,
    x: pos.x, y: pos.y,
    // Inherit parent's drift so the moon orbits in the parent's frame
    vx: (parent.vx || 0) + (-Math.sin(actAngle)) * orbV,
    vy: (parent.vy || 0) + ( Math.cos(actAngle)) * orbV,
    mass, radius: moonRadius,
    color, trail: [], velMul: 1,
    isMoon: true,
    moonDepth: parent.isMoon ? (parent.moonDepth || 1) + 1 : 1,
    // Snapshot the root planet's name so nested moons can suffix it
    rootPlanetName: parent.isMoon ? (parent.rootPlanetName || parent.name) : parent.name
  };
  bodies.push(moon);
  nextPlanetId++;
  buildControls();
  applyEarthFeatures(moon);
}

function togglePause() {
  paused = !paused;
  const btn = document.getElementById('btn-pause');
  btn.textContent = paused ? '▶ Play' : '⏸ Pause';
  btn.classList.toggle('active', paused);
}

function toggleThreeD() {
  is3D = !is3D;
  const btn = document.getElementById('btn-3d');
  if (btn) btn.classList.toggle('active', is3D);
  if (is3D) {
    // Default to a slight overhead tilt so the user immediately sees a 3D
    // perspective instead of an unchanged top-down view.
    if (cameraPitch === 0 && cameraYaw === 0) {
      cameraPitch = -0.55;
    }
  } else {
    // Reset camera angles so 2D doesn't carry over a rotated view.
    cameraYaw = 0;
    cameraPitch = 0;
    syncCameraSliders();
  }
}

// Push current camera angles into the sliders (after a mouse-drag rotation
// or a toggle-off) so the UI stays in sync.
function syncCameraSliders() {
  const t = document.getElementById('tilt-slider');
  const tv = document.getElementById('tilt-val');
  const y = document.getElementById('yaw-slider');
  const yv = document.getElementById('yaw-val');
  if (t && tv) {
    const deg = Math.round(-cameraPitch * 180 / Math.PI);
    t.value = String(deg);
    tv.textContent = deg + '°';
  }
  if (y && yv) {
    const deg = Math.round(cameraYaw * 180 / Math.PI);
    y.value = String(deg);
    yv.textContent = deg + '°';
  }
}

// Tilt slider — degrees of pitch (negative cameraPitch = looking down, which
// is the natural "tilt forward" feel). Auto-enables 3D when nonzero.
function setCameraTiltDeg(v) {
  const deg = parseFloat(v);
  cameraPitch = -(deg * Math.PI / 180);
  const tv = document.getElementById('tilt-val');
  if (tv) tv.textContent = Math.round(deg) + '°';
  if (deg !== 0 && !is3D) toggleThreeD();
}

// Rotate slider — degrees of yaw. Auto-enables 3D when nonzero.
function setCameraYawDeg(v) {
  const deg = parseFloat(v);
  cameraYaw = deg * Math.PI / 180;
  const yv = document.getElementById('yaw-val');
  if (yv) yv.textContent = Math.round(deg) + '°';
  if (deg !== 0 && !is3D) toggleThreeD();
}

function resetSim() {
  mergeEffects = [];
  rockets = [];
  galaxies = [];
  simTime = 0;
  createDefaultBodies();
  initialState = deepCopy(bodies);
  buildControls();
  // Reset camera back to auto-follow at 1× zoom
  recenterView();
}

function toggleTrails() {
  showTrails = !showTrails;
  const btn = document.getElementById('btn-trails');
  btn.classList.toggle('active', showTrails);
  if (!showTrails) {
    for (const b of bodies) b.trail = [];
  }
}

// Opt-in toggle: records and renders trails for asteroids too. Off by
// default because 200+ trails are expensive. When turned off, existing
// asteroid trails are cleared.
function toggleAsteroidTrails() {
  asteroidTrailsEnabled = !asteroidTrailsEnabled;
  const btn = document.getElementById('btn-asteroid-trails');
  if (btn) btn.classList.toggle('active', asteroidTrailsEnabled);
  if (!asteroidTrailsEnabled) {
    for (const b of bodies) if (b.isAsteroid) b.trail = [];
  }
}

function fmtSpeedMul(x) {
  if (x >= 1e15) return (x / 1e15).toFixed(2) + 'Q×';   // quadrillion
  if (x >= 1e12) return (x / 1e12).toFixed(2) + 'T×';   // trillion
  if (x >= 1e9)  return (x / 1e9).toFixed(2)  + 'B×';   // billion
  if (x >= 1e6)  return (x / 1e6).toFixed(2)  + 'M×';
  if (x >= 1e3)  return (x / 1e3).toFixed(2)  + 'k×';
  if (x >= 100)  return x.toFixed(0) + '×';
  if (x >= 10)   return x.toFixed(1) + '×';
  return x.toFixed(2) + '×';
}

// Top of admin slider — 10^19 multiplier so a single real second covers
// roughly 833 quadrillion years of sim time.
const SPEED_CAP_MAX = 1e19;

function applySpeed(mul) {
  speedMul = Math.max(0.01, Math.min(SPEED_CAP_MAX, mul));
  const sv = document.getElementById('speed-val');
  if (sv) sv.textContent = fmtSpeedMul(speedMul);
  const av = document.getElementById('admin-speed-val');
  if (av) av.textContent = fmtSpeedMul(speedMul);
  const ss = document.getElementById('speed-slider');
  if (ss) {
    const log = Math.log10(speedMul);
    // Regular slider tops out at 1e11.
    if (log >= -0.6 && log <= 11) ss.value = log;
  }
  const as = document.getElementById('admin-speed-slider');
  if (as) as.value = Math.log10(speedMul);
}

// Global speed slider (log scale, 0.25× → 100,000,000,000×).
function setSpeedLog(v) {
  applySpeed(Math.pow(10, parseFloat(v)));
}

// Admin speed slider (log scale, 0.25× → 10,000,000,000,000,000,000×).
function setAdminSpeed(v) {
  applySpeed(Math.pow(10, parseFloat(v)));
}

// Back-compat: older saves call setSpeed(numericMul) directly.
function setSpeed(v) { applySpeed(parseFloat(v)); }

function fmtExagMul(x) {
  if (x >= 1e6) return (x / 1e6).toFixed(2) + 'M×';
  if (x >= 1e3) return (x / 1e3).toFixed(2) + 'k×';
  if (x >= 100) return x.toFixed(0) + '×';
  if (x >= 10)  return x.toFixed(1) + '×';
  return x.toFixed(2) + '×';
}

// Size-exaggeration slider (log scale, 1× → 1,000,000×). Visual-only.
function setSizeExaggerationLog(v) {
  sizeExaggeration = Math.max(1, Math.min(1e6, Math.pow(10, parseFloat(v))));
  const el = document.getElementById('size-exag-val');
  if (el) el.textContent = fmtExagMul(sizeExaggeration);
}

// AU rescale — admin UI handlers. Applies a multiplier to the current AU
// (e.g. 2 doubles AU, 0.5 halves it). The setAuMultiplier function takes
// care of recomputing G, rescaling bodies/velocities/trails, and adjusting
// the camera so the view stays roughly the same on screen.
function adminApplyAuMul() {
  const input = document.getElementById('admin-au-input');
  if (!input) return;
  const k = parseFloat(input.value);
  if (!isFinite(k) || k <= 0) { input.value = ''; return; }
  setAuMultiplier(k);
  input.value = '';
  refreshAuReadout();
}
function adminApplyAuMulFixed(k) {
  setAuMultiplier(k);
  refreshAuReadout();
}
function refreshAuReadout() {
  const el = document.getElementById('admin-au-val');
  if (el) el.textContent = _AU_SIM_UNITS.toFixed(0) + ' sim units';
}

function toggleVectors() {
  showVectors = !showVectors;
  document.getElementById('btn-vectors').classList.toggle('active', showVectors);
}

// Click on a body's icon dot teleports the camera to that body.
function cameraGoTo(id) {
  const b = bodies.find(x => x.id === id);
  if (!b) return;
  autoFollow = false;
  viewX = b.x;
  viewY = b.y;
}

// Show a picker modal listing every other body; clicking one runs setOrbit.
function orbitBody(id) {
  const b = bodies.find(x => x.id === id);
  if (!b) return;
  const others = bodies.filter(x => x !== b);
  if (others.length === 0) return;
  const existing = document.getElementById('orbit-overlay');
  if (existing) existing.remove();
  const overlay = document.createElement('div');
  overlay.id = 'orbit-overlay';
  overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.7);z-index:20000;display:flex;align-items:center;justify-content:center;backdrop-filter:blur(6px)';
  const list = others.map(o =>
    `<button class="btn" style="justify-content:flex-start;width:100%;margin-bottom:4px" onclick="setOrbit('${id}','${o.id}');document.getElementById('orbit-overlay').remove()">` +
      `<span style="display:inline-block;width:10px;height:10px;border-radius:50%;background:${o.color};box-shadow:0 0 6px ${o.color};margin-right:8px"></span>` +
      `${o.name}` +
    `</button>`
  ).join('');
  overlay.innerHTML = `
    <div style="background:linear-gradient(160deg,rgba(20,20,45,0.97),rgba(12,12,30,0.99));border:1px solid rgba(255,255,255,0.1);border-radius:16px;padding:24px;width:360px;max-height:80vh;overflow-y:auto;box-shadow:0 20px 60px rgba(0,0,0,0.7);font-family:'Inter',sans-serif">
      <h3 style="margin:0 0 6px;color:#fff;font-size:1.1em;font-weight:700">⟳ Orbit which body?</h3>
      <div style="font-size:0.78em;color:#888;margin-bottom:14px">${b.name} will be given a circular orbit around the chosen body.</div>
      <div>${list}</div>
      <div style="display:flex;justify-content:flex-end;margin-top:12px">
        <button onclick="document.getElementById('orbit-overlay').remove()" style="padding:8px 14px;border-radius:8px;border:1px solid rgba(255,255,255,0.1);background:rgba(255,255,255,0.04);color:#aaa;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em">Cancel</button>
      </div>
    </div>`;
  document.body.appendChild(overlay);
  overlay.addEventListener('click', (e) => { if (e.target === overlay) overlay.remove(); });
}

// Give `b` the circular orbital velocity for orbiting `t` at their current
// separation, expressed in `t`'s reference frame. Direction is counterclockwise.
function setOrbit(bodyId, targetId) {
  const b = bodies.find(x => x.id === bodyId);
  const t = bodies.find(x => x.id === targetId);
  if (!b || !t || b === t) return;
  const dx = t.x - b.x;
  const dy = t.y - b.y;
  const dist = Math.sqrt(dx * dx + dy * dy);
  if (dist < 1) return;
  const orbV = Math.sqrt(G_BASE * t.mass / dist);
  // Tangent perpendicular to the radius vector (counterclockwise)
  b.vx = (t.vx || 0) + (-dy / dist) * orbV;
  b.vy = (t.vy || 0) + ( dx / dist) * orbV;
  b.velMul = 1;
  // Locked bodies don't integrate, so unlock if needed so the orbit takes effect
  if (b.locked) b.locked = false;
  b.trail = [];
  buildControls();
}

function renameBody(id) {
  const b = bodies.find(x => x.id === id);
  if (!b) return;
  const next = prompt('Rename body:', b.name || '');
  if (next == null) return;
  const trimmed = next.trim();
  if (!trimmed) return;
  b.name = trimmed;

  const normName = trimmed.toLowerCase();
  // Named supermassive black hole? Convert this body in place.
  if (NAMED_BHS[normName]) {
    const cfg = NAMED_BHS[normName];
    b.isSun = true;
    b.mass = cfg.mass;
    b.radius = cfg.radius;
    b.color = '#000000';
    b.stellarPhase = 'black-hole';
    b.phaseAtSim = simTime;
    b.createdAtSim = simTime;
    b.accretionRing = [];
    b.vx = 0; b.vy = 0;
    b.trail = [];
    // Clear any leftover evolution / earth-like state
    delete b.continents;
    delete b.strangeMatter;
    delete b.magnetar;
    delete b.magnetarRolled;
    delete b.neutronResolved;
    delete b.whiteDwarfAtSim;
    delete b.redGiantAtSim;
    delete b.nebulaResolved;
    triggerMergeFlash();
    buildControls();
    return;
  }

  // Renaming an existing comet to "Shoemaker-Levy 9" reseats it on an
  // inbound trajectory toward Jupiter (if a body named "Jupiter" exists).
  if (b.isComet && SL9_NAME_KEYS.has(_normCometName(trimmed))) {
    const jupiter = bodies.find(s => (s.name || '').toLowerCase() === 'jupiter');
    if (jupiter) {
      const startDist = Math.max(jupiter.radius * 80, _AU_SIM_UNITS * 0.05);
      const angle = Math.random() * Math.PI * 2;
      b.x = jupiter.x + Math.cos(angle) * startDist;
      b.y = jupiter.y + Math.sin(angle) * startDist;
      const dx = jupiter.x - b.x, dy = jupiter.y - b.y;
      const dist = Math.sqrt(dx * dx + dy * dy);
      const ux = dx / dist, uy = dy / dist;
      const vEsc = Math.sqrt(2 * G_BASE * jupiter.mass / startDist);
      const vIn  = vEsc * 0.5;
      b.vx = jupiter.vx + ux * vIn;
      b.vy = jupiter.vy + uy * vIn;
      if (b.z  !== undefined) b.z  = 0;
      if (b.vz !== undefined) b.vz = 0;
      b.trail = [];
      buildControls();
      return;
    }
  }

  // Named-comet rename — reshape orbit to match the real comet's period.
  // Only applies to existing comets, since we'd otherwise re-purpose
  // arbitrary bodies into icy snowballs.
  if (b.isComet && NAMED_COMETS[normName]) {
    const sun = bodies.find(s => s.isSun);
    if (sun) {
      const cfg = NAMED_COMETS[normName];
      const sunMass = sun.mass;
      const T  = cfg.periodYears * _EARTH_ORBIT_PERIOD_DT;
      const a3 = (T * T) * G_BASE * sunMass / (4 * Math.PI * Math.PI);
      const a  = Math.cbrt(a3);
      const e  = cfg.eccentricity;
      const r_apo = a * (1 + e);
      const v_apo = Math.sqrt(G_BASE * sunMass * (1 - e) / (a * (1 + e)));
      const angle = Math.random() * Math.PI * 2;
      b.x  = sun.x + Math.cos(angle) * r_apo;
      b.y  = sun.y + Math.sin(angle) * r_apo;
      b.vx = -Math.sin(angle) * v_apo;
      b.vy =  Math.cos(angle) * v_apo;
      b.z  = 0; b.vz = 0;
      b.trail = [];
      buildControls();
      return;
    }
  }

  // Earth-like rename → grow continents if it doesn't have them yet
  if (isEarthLike(b) && !b.continents) {
    b.continents = [];
    const n = 3 + Math.floor(Math.random() * 3);
    for (let i = 0; i < n; i++) {
      b.continents.push({
        angle: Math.random() * Math.PI * 2,
        distFrac: Math.random() * 0.5,
        sizeFrac: 0.18 + Math.random() * 0.14,
        shade: Math.random()
      });
    }
  }
  buildControls();
}

function toggleLock(id) {
  const b = bodies.find(b => b.id === id);
  if (!b) return;
  b.locked = !b.locked;
  if (b.locked) {
    b.vx = 0;
    b.vy = 0;
    b.trail = [];
  }
  // Update the button in place without rebuilding the whole panel
  const card = document.getElementById('card-' + id);
  if (card) {
    const btn = card.querySelector('.lock-btn');
    if (btn) {
      btn.classList.toggle('locked', b.locked);
      btn.textContent = b.locked ? '🔒' : '🔓';
      btn.title = b.locked ? 'Unlock' : 'Lock in place';
    }
  }
}

// ---- Save system (localStorage-backed; per-browser, not networked) ----
// Anyone on this browser can pick an email and save the current universe.
// Browsing shows every save in localStorage regardless of email — that's
// how the "look at other systems" affordance works without a server.
let saveUserEmail = null;
try { saveUserEmail = localStorage.getItem('gravity_save_email') || null; } catch (_) {}

const SAVES_KEY = 'gravity_saves';

function loadAllSaves() {
  try { return JSON.parse(localStorage.getItem(SAVES_KEY) || '[]'); }
  catch (_) { return []; }
}
function writeAllSaves(saves) {
  try { localStorage.setItem(SAVES_KEY, JSON.stringify(saves)); }
  catch (e) { alert('Could not write to localStorage: ' + e.message); }
}

function showSaveLogin() {
  if (document.getElementById('save-login-overlay')) return;
  const overlay = document.createElement('div');
  overlay.id = 'save-login-overlay';
  overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.7);z-index:20000;display:flex;align-items:center;justify-content:center;backdrop-filter:blur(6px)';
  overlay.innerHTML = `
    <div style="background:linear-gradient(160deg,rgba(20,20,45,0.97),rgba(12,12,30,0.99));border:1px solid rgba(255,255,255,0.1);border-radius:16px;padding:28px;width:340px;box-shadow:0 20px 60px rgba(0,0,0,0.7);font-family:'Inter',sans-serif">
      <h3 style="margin:0 0 14px;color:#fff;font-size:1.15em;font-weight:700">🌌 Sign in to save</h3>
      <div style="font-size:0.78em;color:#888;margin-bottom:14px">Saves are stored locally in your browser; anyone on this browser will see them when they Browse.</div>
      <input id="save-email-input" type="email" placeholder="email@example.com" style="width:100%;padding:10px 12px;border-radius:8px;border:1px solid rgba(255,255,255,0.12);background:rgba(255,255,255,0.06);color:#fff;font-family:'Inter',sans-serif;font-size:0.95em;outline:none;margin-bottom:14px" />
      <div style="display:flex;gap:8px;justify-content:flex-end">
        <button id="save-login-cancel" style="padding:8px 18px;border-radius:8px;border:1px solid rgba(255,255,255,0.1);background:rgba(255,255,255,0.04);color:#aaa;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em">Cancel</button>
        <button id="save-login-submit" style="padding:8px 18px;border-radius:8px;border:1px solid rgba(125,211,252,0.3);background:rgba(125,211,252,0.12);color:#7dd3fc;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em;font-weight:600">Sign in</button>
      </div>
    </div>`;
  document.body.appendChild(overlay);
  const input = document.getElementById('save-email-input');
  input.value = saveUserEmail || '';
  input.focus();
  const close = () => overlay.remove();
  const submit = () => {
    const v = (input.value || '').trim().toLowerCase();
    if (!v || v.indexOf('@') < 0) return;
    saveUserEmail = v;
    try { localStorage.setItem('gravity_save_email', v); } catch (_) {}
    renderSaveSection();
    close();
  };
  document.getElementById('save-login-cancel').addEventListener('click', close);
  document.getElementById('save-login-submit').addEventListener('click', submit);
  overlay.addEventListener('click', (e) => { if (e.target === overlay) close(); });
  input.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') submit();
    if (e.key === 'Escape') close();
  });
}

function saveLogout() {
  saveUserEmail = null;
  try { localStorage.removeItem('gravity_save_email'); } catch (_) {}
  renderSaveSection();
}

// ---- Serialize / deserialize the universe ----
// Trails are cleared on save (they're ephemeral). Rockets and merge effects
// are not persisted — they re-create themselves during normal play.
function serializeUniverse() {
  return {
    version: 1,
    bodies: bodies.map(b => {
      const copy = Object.assign({}, b);
      copy.trail = [];
      // Sets and circular refs aren't JSON-friendly; drop them.
      // (Only rockets carry Sets, and we don't save rockets.)
      return copy;
    }),
    view:    { viewX, viewY, viewZoom, autoFollow },
    timing:  { simTime, nextPlanetId, nextSunId },
    toggles: { paused, showTrails, showVectors, starAfterlifeEnabled, speedMul }
  };
}

function deserializeUniverse(s) {
  if (!s || !s.bodies) return false;
  bodies      = s.bodies.map(b => Object.assign({}, b, { trail: [] }));
  rockets     = [];
  mergeEffects = [];
  if (s.view) {
    viewX      = s.view.viewX;
    viewY      = s.view.viewY;
    viewZoom   = s.view.viewZoom;
    autoFollow = s.view.autoFollow;
  }
  if (s.timing) {
    simTime       = s.timing.simTime || 0;
    nextPlanetId  = s.timing.nextPlanetId || 1;
    nextSunId     = s.timing.nextSunId || 1;
  }
  if (s.toggles) {
    paused                = !!s.toggles.paused;
    showTrails            = s.toggles.showTrails !== false;
    showVectors           = !!s.toggles.showVectors;
    starAfterlifeEnabled  = s.toggles.starAfterlifeEnabled !== false;
    speedMul              = s.toggles.speedMul || 1;
  }
  // Reset two-body selection — bodies in the new universe have different ids
  selectedBodyAId = null;
  selectedBodyBId = null;
  // Refresh UI to match
  buildControls();
  const pBtn = document.getElementById('btn-pause');
  if (pBtn) { pBtn.textContent = paused ? '▶ Play' : '⏸ Pause'; pBtn.classList.toggle('active', paused); }
  const tBtn = document.getElementById('btn-trails');
  if (tBtn) tBtn.classList.toggle('active', showTrails);
  const vBtn = document.getElementById('btn-vectors');
  if (vBtn) vBtn.classList.toggle('active', showVectors);
  const aBtn = document.getElementById('btn-afterlife');
  if (aBtn) aBtn.classList.toggle('active', starAfterlifeEnabled);
  applySpeed(speedMul);
  return true;
}

function saveCurrentUniverse() {
  if (!saveUserEmail) { showSaveLogin(); return; }
  const defaultName = 'Universe ' + new Date().toLocaleString();
  const name = prompt('Name this universe:', defaultName);
  if (!name) return;
  const all = loadAllSaves();
  const entry = {
    id: 'save-' + Date.now() + '-' + Math.random().toString(36).slice(2, 8),
    email: saveUserEmail,
    name: name.trim(),
    when: Date.now(),
    state: serializeUniverse()
  };
  all.push(entry);
  writeAllSaves(all);
  renderSaveSection();
}

function deleteSave(id) {
  if (!confirm('Delete this universe permanently?')) return;
  const all = loadAllSaves().filter(s => s.id !== id);
  writeAllSaves(all);
  const existing = document.getElementById('save-browse-overlay');
  if (existing) { existing.remove(); showSaveBrowser(); }
  renderSaveSection();
}

function loadSaveById(id) {
  const all = loadAllSaves();
  const entry = all.find(s => s.id === id);
  if (!entry) return;
  if (!deserializeUniverse(entry.state)) {
    alert('That save looks corrupted.');
    return;
  }
  const existing = document.getElementById('save-browse-overlay');
  if (existing) existing.remove();
}

function showSaveBrowser() {
  if (document.getElementById('save-browse-overlay')) return;
  const all = loadAllSaves().slice().sort((a, b) => b.when - a.when);
  const overlay = document.createElement('div');
  overlay.id = 'save-browse-overlay';
  overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.7);z-index:20000;display:flex;align-items:center;justify-content:center;backdrop-filter:blur(6px)';
  const rows = all.length === 0
    ? `<div style="color:#888;font-size:0.85em;padding:14px 0">No saved universes yet.</div>`
    : all.map(s => {
        const own = saveUserEmail && s.email === saveUserEmail;
        const date = new Date(s.when).toLocaleString();
        const bodyCount = (s.state && s.state.bodies && s.state.bodies.length) || 0;
        return `
          <div style="display:flex;align-items:center;gap:10px;padding:10px 12px;border:1px solid rgba(255,255,255,0.07);border-radius:10px;margin-bottom:6px">
            <div style="flex:1;min-width:0">
              <div style="font-weight:600;color:#e8eef5;font-size:0.92em;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">${escapeHtml(s.name)}</div>
              <div style="font-size:0.7em;color:#888;margin-top:2px">${escapeHtml(s.email)} · ${date} · ${bodyCount} bodies</div>
            </div>
            <button onclick="loadSaveById('${s.id}')" style="padding:6px 12px;border-radius:6px;border:1px solid rgba(125,211,252,0.3);background:rgba(125,211,252,0.12);color:#7dd3fc;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.78em">Open</button>
            ${own ? `<button onclick="deleteSave('${s.id}')" style="padding:6px 10px;border-radius:6px;border:1px solid rgba(255,80,80,0.25);background:rgba(255,80,80,0.10);color:#ff8888;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.78em">Delete</button>` : ''}
          </div>`;
      }).join('');
  overlay.innerHTML = `
    <div style="background:linear-gradient(160deg,rgba(20,20,45,0.97),rgba(12,12,30,0.99));border:1px solid rgba(255,255,255,0.1);border-radius:16px;padding:24px;width:480px;max-height:80vh;overflow-y:auto;box-shadow:0 20px 60px rgba(0,0,0,0.7);font-family:'Inter',sans-serif">
      <h3 style="margin:0 0 6px;color:#fff;font-size:1.1em;font-weight:700">🌌 Universes</h3>
      <div style="font-size:0.78em;color:#888;margin-bottom:14px">Open one to load and edit. Saves are stored in this browser.</div>
      ${rows}
      <div style="display:flex;justify-content:flex-end;margin-top:14px">
        <button onclick="document.getElementById('save-browse-overlay').remove()" style="padding:8px 14px;border-radius:8px;border:1px solid rgba(255,255,255,0.1);background:rgba(255,255,255,0.04);color:#aaa;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em">Close</button>
      </div>
    </div>`;
  document.body.appendChild(overlay);
  overlay.addEventListener('click', (e) => { if (e.target === overlay) overlay.remove(); });
}

function renderSaveSection() {
  const el = document.getElementById('save-content');
  if (!el) return;
  if (saveUserEmail) {
    el.innerHTML = `
      <div style="font-size:0.7em;color:#7dd3fc;margin-bottom:8px">Signed in as ${escapeHtml(saveUserEmail)}</div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="saveCurrentUniverse()">💾 Save</button>
        <button class="btn" onclick="showSaveBrowser()">📂 Browse</button>
      </div>
      <div class="btn-row">
        <button class="btn reset-btn" onclick="saveLogout()">Sign out</button>
      </div>`;
  } else {
    el.innerHTML = `
      <div class="btn-row">
        <button class="btn" onclick="showSaveLogin()">🌌 Sign in to save</button>
        <button class="btn" onclick="showSaveBrowser()">📂 Browse</button>
      </div>`;
  }
}

// ---- Admin: gated spawn tools ----
// Any (email, password) pair below is accepted. Emails are compared
// case-insensitively (the login form lowercases input before checking).
const ADMIN_CREDENTIALS = {
  'ajt3317@gmail.com':              '1Aj2Likes3Bananas4And5Apples',
  's590035@stjohns.k12.fl.us':      'Dogs5',
  'aaravsubramanian@gmail.com':     'sigma123',
  's581457@stjohns.k12.fl.us':      'sigmaboi55',
  's598834@stjohns.k12.fl.us':      '8crab6own1',
  's588693@stjohns.k12.fl.us':      'mipno2.0shinbazooka',
  's596094@stjohns.k12.fl.us':      'dingdongrapper123',
  's596391@stjohns.k12.fl.us':      '2016NYC',
  's568106@stjohns.k12.fl.us':      'TheOman'
};
// Back-compat alias for any old code that references ADMIN_EMAIL directly.
const ADMIN_EMAIL = 'ajt3317@gmail.com';
let adminAuthed = false;
let adminAuthedEmail = '';
try {
  const stored = localStorage.getItem('adminAuthed');
  if (stored && ADMIN_CREDENTIALS[stored.toLowerCase()] !== undefined) {
    adminAuthed = true;
    adminAuthedEmail = stored.toLowerCase();
  }
} catch (_) {}

// Creator login: a single shared password unlocks the custom-body Creator
// section. Stored in localStorage so the unlock persists across reloads.
const CREATOR_PASSWORD = 'asdfg';
let creatorAuthed = false;
try {
  if (localStorage.getItem('creatorAuthed') === '1') creatorAuthed = true;
} catch (_) {}

function pickAdminSpawnPos(effectiveRadius) {
  const angle = Math.random() * Math.PI * 2;
  const dist = 150 + Math.random() * 100;
  const cx = viewX + Math.cos(angle) * dist;
  const cy = viewY + Math.sin(angle) * dist;
  return findFreeSpawnPos(cx, cy, effectiveRadius || 30);
}

// Pick a position for a new galaxy of `type` that doesn't overlap any
// existing galaxy of the same type. Used for huge visual-only galaxies
// (Universe, Laniakea, ...) since they're not collision-checked elsewhere.
function pickGalaxySpawnPos(type, newRadius) {
  const existing = galaxies.filter(g => g.type === type);
  if (existing.length === 0) {
    return { x: viewX, y: viewY };
  }
  // Try a few random angles around the most recent one, far enough out that
  // the new disc won't overlap any existing same-type disc.
  const anchor = existing[existing.length - 1];
  const minSep = (g) => (newRadius + g.radius) * 1.10;
  for (let i = 0; i < 24; i++) {
    const ang = Math.random() * Math.PI * 2;
    const d = minSep(anchor) + Math.random() * newRadius * 0.5;
    const x = anchor.x + Math.cos(ang) * d;
    const y = anchor.y + Math.sin(ang) * d;
    let ok = true;
    for (const g of existing) {
      if (Math.hypot(x - g.x, y - g.y) < minSep(g)) { ok = false; break; }
    }
    if (ok) return { x, y };
  }
  // Fallback: deterministic offset from the anchor.
  const ang = (existing.length * 1.7) % (Math.PI * 2);
  return { x: anchor.x + Math.cos(ang) * newRadius * 2.5,
           y: anchor.y + Math.sin(ang) * newRadius * 2.5 };
}

function makeContinents() {
  const continents = [];
  const n = 3 + Math.floor(Math.random() * 3);
  for (let i = 0; i < n; i++) {
    continents.push({
      angle: Math.random() * Math.PI * 2,
      distFrac: Math.random() * 0.5,
      sizeFrac: 0.18 + Math.random() * 0.14,
      shade: Math.random()
    });
  }
  return continents;
}

// Lines up every body in the scene edge-to-edge along a horizontal row,
// ordered smallest → biggest by real radius (visual size exaggeration is
// not used). Velocities are zeroed, trails wiped, and the camera is fit
// to the resulting row so the size comparison is visible at a glance.
// The simulation is paused to keep the lineup intact.
function adminLineUpBodies() {
  if (!adminAuthed) return;
  if (bodies.length === 0) return;
  const sorted = [...bodies].sort((a, b) => a.radius - b.radius);
  let totalWidth = 0;
  for (const b of sorted) totalWidth += b.radius * 2;
  // Place each body left-to-right, centered on the current camera focus.
  const cx = viewX, cy = viewY;
  let cursor = cx - totalWidth / 2;
  for (const b of sorted) {
    b.x = cursor + b.radius;
    b.y = cy;
    b.vx = 0; b.vy = 0;
    if (b.z  !== undefined) b.z  = 0;
    if (b.vz !== undefined) b.vz = 0;
    b.trail = [];
    cursor += b.radius * 2;
  }
  // Pause so the row holds; user can hit Play to release the line into
  // mutual gravity if they want to see chaos unfold.
  if (!paused) togglePause();
  // Fit the camera to the row.
  fitCameraToObject(cx, cy, totalWidth / 2);
  buildControls();
}

function adminSpawn(kind) {
  if (!adminAuthed) return;
  switch (kind) {
    case 'halley': {
      // Real Halley's Comet — 76-year period, e ≈ 0.967. spawnComet() solves
      // the semi-major axis from the period via Kepler's third law.
      spawnComet('Halley');
      return;
    }
    case 'star': {
      const mass = 1000;
      const r = 28 + Math.cbrt(mass / 1000) * 4;
      const pos = pickAdminSpawnPos(r);
      bodies.push({
        id: 'sun-' + nextSunId, name: 'Star ' + nextSunId, isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass, radius: r,
        color: getStarColor(mass), trail: [], velMul: 1,
        createdAtSim: simTime, stellarPhase: 'main-sequence'
      });
      nextSunId++;
      break;
    }
    case 'blackhole': {
      const mass = 5000;
      const r = 12 + Math.cbrt(mass / 1000) * 3;
      const pos = pickAdminSpawnPos(r);
      bodies.push({
        id: 'sun-' + nextSunId, name: 'Black Hole ' + nextSunId, isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass, radius: r,
        color: '#000000', trail: [], velMul: 1,
        createdAtSim: simTime,
        stellarPhase: 'black-hole', phaseAtSim: simTime, accretionRing: []
      });
      nextSunId++;
      break;
    }
    case 'neutron':
    case 'strange':
    case 'magnetar': {
      const prefix = kind === 'magnetar' ? 'Magnetar ' : kind === 'strange' ? 'Strange NS ' : 'Neutron Star ';
      const pos = pickAdminSpawnPos(5);
      const ns = {
        id: 'sun-' + nextSunId, name: prefix + nextSunId, isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass: 500, radius: 5,
        color: '#ccddff', trail: [], velMul: 1,
        createdAtSim: simTime,
        stellarPhase: 'neutron-star', phaseAtSim: simTime,
        neutronResolved: false
      };
      if (kind === 'strange') ns.strangeMatter = true;
      if (kind === 'magnetar') { ns.magnetar = true; ns.magnetarRolled = true; }
      bodies.push(ns);
      nextSunId++;
      if (kind === 'magnetar') magnetarBurst(ns);
      else if (kind === 'strange') strangeMatterBurst(ns);
      break;
    }
    case 'planet':
    case 'dwarf':
    case 'lifeplanet': {
      const mass = kind === 'dwarf' ? 75 : 5;
      const r = 3 + Math.cbrt(mass) * 2.2;
      const pos = pickAdminSpawnPos(r);
      const baseName = kind === 'lifeplanet' ? 'Earth' : kind === 'dwarf' ? 'Dwarf' : 'Planet';
      const planet = {
        id: 'planet-' + nextPlanetId,
        name: baseName + ' ' + nextPlanetId,
        isSun: false,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass, radius: r,
        color: PALETTE[nextPlanetId % PALETTE.length],
        trail: [], velMul: 1
      };
      if (kind === 'lifeplanet') planet.continents = makeContinents();
      bodies.push(planet);
      nextPlanetId++;
      break;
    }
    case 'forcerocket': {
      // Find an existing planet with life; if none, mint a new life planet
      // and use that as the launch site.
      let home = bodies.find(b => !b.isSun && b.continents && b.continents.length);
      if (!home) {
        const mass = 5;
        const r = 3 + Math.cbrt(mass) * 2.2;
        const pos = pickAdminSpawnPos(r);
        home = {
          id: 'planet-' + nextPlanetId,
          name: 'Earth ' + nextPlanetId,
          isSun: false,
          x: pos.x, y: pos.y, vx: 0, vy: 0,
          mass, radius: r,
          color: PALETTE[nextPlanetId % PALETTE.length],
          trail: [], velMul: 1,
          continents: makeContinents()
        };
        bodies.push(home);
        nextPlanetId++;
      }
      spawnRocket(home);
      break;
    }
    case 'redsupergiant': {
      const mass = 1500;
      const r = 28 + Math.cbrt(mass / 1000) * 4;
      // Red super giant disc is 10× the base at spawn → use that for overlap
      const pos = pickAdminSpawnPos(r * 10);
      bodies.push({
        id: 'sun-' + nextSunId,
        name: 'Red Super Giant ' + nextSunId,
        isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass,
        radius: r,
        color: '#ff4422',
        trail: [], velMul: 1,
        createdAtSim: simTime,
        stellarPhase: 'red-giant',
        redGiantAtSim: simTime,
        redSuperGiant: true
      });
      nextSunId++;
      break;
    }
    case 'bluesupergiant': {
      const mass = 5000;
      const r = 28 + Math.cbrt(mass / 1000) * 4;
      // Blue super giant is 30× the base — match for overlap
      const pos = pickAdminSpawnPos(r * 30);
      bodies.push({
        id: 'sun-' + nextSunId,
        name: 'Blue Super Giant ' + nextSunId,
        isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass,
        radius: r,
        color: '#3a7aff',
        trail: [], velMul: 1,
        createdAtSim: simTime,
        stellarPhase: 'blue-super-giant',
        phaseAtSim: simTime
      });
      nextSunId++;
      break;
    }
    case 'ksupergiant': {
      const mass = 1500; // mid Path B mass — would normally become a red giant
      const baseR = 28 + Math.cbrt(mass / 1000) * 4;
      // K super giant is 100-150× sun radius — use the upper end for overlap
      const pos = pickAdminSpawnPos(SUN_NOMINAL_RADIUS * 150);
      bodies.push({
        id: 'sun-' + nextSunId,
        name: 'K Super Giant ' + nextSunId,
        isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass,
        radius: baseR,
        color: '#ff9a45',
        trail: [], velMul: 1,
        createdAtSim: simTime,
        stellarPhase: 'k-super-giant',
        kSuperAtSim: simTime
      });
      nextSunId++;
      break;
    }
    case 'j1407b': {
      const mass = 15;
      const r = 3 + Math.cbrt(mass) * 2.2;
      // Effective radius for overlap-checking includes the massive rings —
      // they extend out to ~28 × scale × b.radius. Otherwise the rings
      // would always overlap something.
      const pos = pickAdminSpawnPos(r);
      bodies.push({
        id: 'planet-' + nextPlanetId,
        name: 'J1407b',
        isSun: false,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass, radius: r,
        color: '#caa987',
        trail: [], velMul: 1
      });
      nextPlanetId++;
      break;
    }
    case 'roxs42bb':
    case 'hd100546b': {
      const isRoxs = kind === 'roxs42bb';
      const displayName = isRoxs ? 'ROXs 42Bb' : 'HD 100546b';
      const mass = 15;
      const r = 3 + Math.cbrt(mass) * 2.2;
      // Effective radius reflects the name-based size override so the
      // big planet doesn't spawn inside another body.
      const effR = JUPITER_RADIUS * (isRoxs ? 2.5 : 7);
      const pos = pickAdminSpawnPos(effR);
      bodies.push({
        id: 'planet-' + nextPlanetId,
        name: displayName,
        isSun: false,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass, radius: r,
        color: isRoxs ? '#a87a52' : '#d4825a',
        trail: [], velMul: 1
      });
      nextPlanetId++;
      break;
    }
    case 'rocket': {
      // Forcefully launch a rocket from any planet that currently has life
      // (continents). Picks one at random if multiple exist; if none, alerts.
      const lifePlanets = bodies.filter(b => !b.isSun && b.continents && b.continents.length > 0);
      if (lifePlanets.length === 0) {
        alert('No planet with life. Name one Earth/Terra/Gaia (or wait for a rocket to seed life on a landing) and try again.');
        return;
      }
      const home = lifePlanets[Math.floor(Math.random() * lifePlanets.length)];
      spawnRocket(home);
      break;
    }
    case 'betelgeuse': {
      const mass = 1000;
      const r = 28 + Math.cbrt(mass / 1000) * 4;
      // Effective radius for overlap-checking uses the final visible size
      // (b.radius × 35 from RSG rendering at full expansion).
      const finalR = r * BETELGEUSE_MAX_MUL * 35;
      const pos = pickAdminSpawnPos(finalR);
      bodies.push({
        id: 'sun-' + nextSunId,
        name: 'Betelgeuse',
        isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass, radius: r,
        color: BETELGEUSE_COLOR,
        trail: [], velMul: 1,
        createdAtSim: simTime,
        // Start straight in the Red Super Giant phase, full expansion
        stellarPhase: 'red-giant',
        redSuperGiant: true,
        redGiantAtSim: simTime - 10000
      });
      nextSunId++;
      break;
    }
    case 'rigel': {
      const mass = 1000;
      const r = 28 + Math.cbrt(mass / 1000) * 4;
      // Overlap-checking uses the final 80× Rigel radius.
      const finalR = r * RIGEL_SIZE_MUL;
      const pos = pickAdminSpawnPos(finalR);
      bodies.push({
        id: 'sun-' + nextSunId,
        name: 'Rigel',
        isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass, radius: r,
        color: RIGEL_COLOR,
        trail: [], velMul: 1,
        createdAtSim: simTime,
        stellarPhase: 'main-sequence'
      });
      nextSunId++;
      break;
    }
    case 'smallstar': {
      const mass = 1000;
      const r = 28 + Math.cbrt(mass / 1000) * 4;
      const finalR = r * SMALLSTAR_SIZE_MUL;
      const pos = pickAdminSpawnPos(finalR);
      bodies.push({
        id: 'sun-' + nextSunId,
        name: '2MASS J0523-1403',
        isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass, radius: r,
        color: getStarColor(mass),
        trail: [], velMul: 1,
        createdAtSim: simTime,
        stellarPhase: 'main-sequence'
      });
      nextSunId++;
      break;
    }
    case 'askap1935':
    case 'askap1839': {
      const lptName = kind === 'askap1935' ? 'ASKAP J1935+2148' : 'ASKAP J1839-075';
      const pos = pickAdminSpawnPos(5);
      bodies.push({
        id: 'sun-' + nextSunId,
        name: lptName,
        isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass: 500, radius: 5,
        color: '#ccddff',
        trail: [], velMul: 1,
        createdAtSim: simTime,
        stellarPhase: 'neutron-star',
        phaseAtSim: simTime,
        neutronResolved: false
      });
      nextSunId++;
      break;
    }
    case 'milkyway': {
      // 700 billion × the Sun's nominal radius (32 → ≈ 2.24e13 world units).
      // Spawn Sagittarius A at the centre and lock the galaxy to it so they
      // move together if Sgr A ever does.
      const cfg = NAMED_BHS['sagittarius a'];
      const galaxyRadius = 32 * 700_000_000_000;
      const pos = pickAdminSpawnPos(cfg.radius);
      const sagA = {
        id: 'sun-' + nextSunId,
        name: 'Sagittarius A',
        isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass: cfg.mass,
        radius: cfg.radius,
        color: '#000000',
        trail: [], velMul: 1,
        createdAtSim: simTime,
        stellarPhase: 'black-hole',
        phaseAtSim: simTime,
        accretionRing: []
      };
      bodies.push(sagA);
      nextSunId++;
      galaxies.push({
        type: 'milkyway',
        x: pos.x, y: pos.y,
        radius: galaxyRadius,
        rotation: 0,
        centerBodyId: sagA.id
      });
      buildControls();
      triggerMergeFlash();
      fitCameraToObject(pos.x, pos.y, galaxyRadius);
      break;
    }
    case 'universe': {
      // The observable universe: a CMB-style sphere 6.3e23× the sun's radius.
      // It already contains everything else (galaxies, planets, etc.) since
      // it dwarfs the entire scene. No physics body — purely visual.
      const universeRadius = SUN_NOMINAL_RADIUS * 6.3e23;
      const pos = pickGalaxySpawnPos('universe', universeRadius);
      galaxies.push({
        type: 'universe',
        x: pos.x, y: pos.y,
        radius: universeRadius,
        rotation: 0
      });
      buildControls();
      fitCameraToObject(pos.x, pos.y, universeRadius);
      break;
    }
    case 'laniakea': {
      // Laniakea Supercluster — the gravitational basin containing the Milky
      // Way, Andromeda, and ~100,000 other galaxies. Radius = 3.5 billion
      // times the sun's radius.
      const laniakeaRadius = SUN_NOMINAL_RADIUS * 3_500_000_000;
      const pos = pickGalaxySpawnPos('laniakea', laniakeaRadius);
      galaxies.push({
        type: 'laniakea',
        x: pos.x, y: pos.y,
        radius: laniakeaRadius,
        rotation: 0
      });
      buildControls();
      fitCameraToObject(pos.x, pos.y, laniakeaRadius);
      break;
    }
    case 'milkdromeda': {
      // Milkdromeda — the elliptical remnant of the Milky Way / Andromeda
      // collision. Same radius as Andromeda, central BH of 200M solar masses.
      const galaxyRadius = 32 * 700_000_000_000 * 2;
      const mergedMass = 3_000_000_000_000 * 1000; // 3 trillion solar masses → 3e15 sim
      const formulaR = 12 + Math.cbrt(mergedMass / 1000) * 3;
      const bhRadius = Math.max(formulaR, 10000);
      const pos = pickAdminSpawnPos(bhRadius);
      const bh = {
        id: 'sun-' + nextSunId,
        name: 'Milkdromeda',
        isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass: mergedMass,
        radius: bhRadius,
        color: '#000000',
        trail: [], velMul: 1,
        createdAtSim: simTime,
        stellarPhase: 'black-hole',
        phaseAtSim: simTime,
        accretionRing: []
      };
      bodies.push(bh);
      nextSunId++;
      galaxies.push({
        type: 'milkdromeda',
        x: pos.x, y: pos.y,
        radius: galaxyRadius,
        rotation: 0,
        centerBodyId: bh.id
      });
      buildControls();
      triggerMergeFlash();
      fitCameraToObject(pos.x, pos.y, galaxyRadius);
      break;
    }
    case 'andromeda': {
      // Andromeda is 2× the Milky Way's radius — viewed nearly edge-on at
      // ~77° tilt. M31* sits at the centre and the galaxy follows it.
      const galaxyRadius = 32 * 700_000_000_000 * 2;
      const m31cfg = NAMED_BHS['m31*'];
      const pos = pickAdminSpawnPos(m31cfg.radius);
      const m31 = {
        id: 'sun-' + nextSunId,
        name: 'M31*',
        isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass: m31cfg.mass,
        radius: m31cfg.radius,
        color: '#000000',
        trail: [], velMul: 1,
        createdAtSim: simTime,
        stellarPhase: 'black-hole',
        phaseAtSim: simTime,
        accretionRing: []
      };
      bodies.push(m31);
      nextSunId++;
      galaxies.push({
        type: 'andromeda',
        x: pos.x, y: pos.y,
        radius: galaxyRadius,
        rotation: Math.PI / 4,
        centerBodyId: m31.id
      });
      buildControls();
      triggerMergeFlash();
      fitCameraToObject(pos.x, pos.y, galaxyRadius);
      break;
    }
    case 'sagittariusa':
    case 'ton618':
    case 'phoenixa':
    case 'm31star': {
      const key = kind === 'sagittariusa' ? 'sagittarius a'
                : kind === 'ton618'       ? 'ton 618'
                : kind === 'phoenixa'     ? 'phoenix a'
                                          : 'm31*';
      const displayName = kind === 'sagittariusa' ? 'Sagittarius A'
                        : kind === 'ton618'       ? 'TON 618'
                        : kind === 'phoenixa'     ? 'Phoenix A'
                                                  : 'M31*';
      const cfg = NAMED_BHS[key];
      const pos = pickAdminSpawnPos(cfg.radius);
      bodies.push({
        id: 'sun-' + nextSunId,
        name: displayName,
        isSun: true,
        x: pos.x, y: pos.y, vx: 0, vy: 0,
        mass: cfg.mass,
        radius: cfg.radius,
        color: '#000000',
        trail: [], velMul: 1,
        createdAtSim: simTime,
        stellarPhase: 'black-hole',
        phaseAtSim: simTime,
        accretionRing: []
      });
      nextSunId++;
      triggerMergeFlash();
      break;
    }
  }
  buildControls();
}

function showAdminLogin() {
  if (document.getElementById('admin-login-overlay')) return;
  const overlay = document.createElement('div');
  overlay.id = 'admin-login-overlay';
  overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.7);z-index:20000;display:flex;align-items:center;justify-content:center;backdrop-filter:blur(6px)';
  overlay.innerHTML = `
    <div style="background:linear-gradient(160deg,rgba(20,20,45,0.97),rgba(12,12,30,0.99));border:1px solid rgba(255,255,255,0.1);border-radius:16px;padding:28px;width:340px;box-shadow:0 20px 60px rgba(0,0,0,0.7);font-family:'Inter',sans-serif">
      <h3 style="margin:0 0 18px;color:#fff;font-size:1.15em;font-weight:700">🛡 Admin Login</h3>
      <div style="margin-bottom:14px">
        <label style="display:block;font-size:0.75em;color:#888;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px">Email</label>
        <input id="admin-email" type="email" autocomplete="off" placeholder="email@example.com" style="width:100%;padding:10px 12px;border-radius:8px;border:1px solid rgba(255,255,255,0.12);background:rgba(255,255,255,0.06);color:#fff;font-family:'Inter',sans-serif;font-size:0.95em;outline:none" />
      </div>
      <div style="margin-bottom:18px">
        <label style="display:block;font-size:0.75em;color:#888;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px">Password</label>
        <input id="admin-password" type="password" autocomplete="off" placeholder="••••••••" style="width:100%;padding:10px 12px;border-radius:8px;border:1px solid rgba(255,255,255,0.12);background:rgba(255,255,255,0.06);color:#fff;font-family:'Inter',sans-serif;font-size:0.95em;outline:none" />
        <div id="admin-login-error" style="display:none;color:#ff8888;font-size:0.78em;margin-top:6px">Incorrect email or password.</div>
      </div>
      <div style="display:flex;gap:8px;justify-content:flex-end">
        <button id="admin-login-cancel" style="padding:8px 18px;border-radius:8px;border:1px solid rgba(255,255,255,0.1);background:rgba(255,255,255,0.04);color:#aaa;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em">Cancel</button>
        <button id="admin-login-submit" style="padding:8px 18px;border-radius:8px;border:1px solid rgba(125,211,252,0.3);background:rgba(125,211,252,0.12);color:#7dd3fc;cursor:pointer;font-family:'Inter',sans-serif;font-size:0.85em;font-weight:600">Login</button>
      </div>
    </div>`;
  document.body.appendChild(overlay);
  const emailInput = document.getElementById('admin-email');
  const passInput = document.getElementById('admin-password');
  emailInput.focus();
  const close = () => overlay.remove();
  const attempt = () => {
    const email = (emailInput.value || '').trim().toLowerCase();
    const pw = passInput.value || '';
    if (ADMIN_CREDENTIALS[email] !== undefined && ADMIN_CREDENTIALS[email] === pw) {
      adminAuthed = true;
      adminAuthedEmail = email;
      try { localStorage.setItem('adminAuthed', email); } catch (_) {}
      renderAdminSection();
      close();
    } else {
      document.getElementById('admin-login-error').style.display = 'block';
    }
  };
  document.getElementById('admin-login-cancel').addEventListener('click', close);
  document.getElementById('admin-login-submit').addEventListener('click', attempt);
  overlay.addEventListener('click', (e) => { if (e.target === overlay) close(); });
  const onKey = (e) => {
    if (e.key === 'Enter') attempt();
    if (e.key === 'Escape') close();
  };
  emailInput.addEventListener('keydown', onKey);
  passInput.addEventListener('keydown', onKey);
}

function adminLogout() {
  adminAuthed = false;
  adminAuthedEmail = '';
  try { localStorage.removeItem('adminAuthed'); } catch (_) {}
  renderAdminSection();
}

function renderAdminSection() {
  const el = document.getElementById('admin-content');
  if (!el) return;
  if (adminAuthed) {
    const speedLog = Math.log10(Math.max(0.01, speedMul));
    el.innerHTML = `
      <div style="font-size:0.7em;color:#7dd3fc;margin-bottom:8px">Signed in as ${adminAuthedEmail || ADMIN_EMAIL}</div>
      <div class="slider-group">
        <div class="slider-label"><span>⏩ Time Warp</span><span class="slider-value" id="admin-speed-val">${fmtSpeedMul(speedMul)}</span></div>
        <input type="range" id="admin-speed-slider" min="-0.6" max="19" step="0.01" value="${speedLog}" oninput="setAdminSpeed(this.value)">
        <div style="font-size:0.65em;color:#666;margin-top:2px">0.25× → 10,000,000,000,000,000,000×</div>
      </div>
      <div class="slider-group">
        <div class="slider-label"><span>📏 AU Scale</span><span class="slider-value" id="admin-au-val">${_AU_SIM_UNITS.toFixed(0)} sim units</span></div>
        <div style="display:flex;gap:6px;margin-top:4px">
          <input type="text" id="admin-au-input" placeholder="multiplier (e.g. 0.5, 2)" style="flex:1;background:rgba(255,255,255,0.06);border:1px solid rgba(255,255,255,0.18);color:#ccc;border-radius:6px;padding:5px 8px;font-family:'Inter',sans-serif;font-size:0.78em;outline:none">
          <button class="btn add-btn" onclick="adminApplyAuMul()" style="padding:5px 10px;font-size:0.78em">Apply ×</button>
        </div>
        <div class="btn-row" style="margin-top:6px">
          <button class="btn" onclick="adminApplyAuMulFixed(0.1)" style="flex:1;padding:4px;font-size:0.72em">×0.1</button>
          <button class="btn" onclick="adminApplyAuMulFixed(0.5)" style="flex:1;padding:4px;font-size:0.72em">×0.5</button>
          <button class="btn" onclick="adminApplyAuMulFixed(2)"   style="flex:1;padding:4px;font-size:0.72em">×2</button>
          <button class="btn" onclick="adminApplyAuMulFixed(10)"  style="flex:1;padding:4px;font-size:0.72em">×10</button>
        </div>
        <div style="font-size:0.65em;color:#666;margin-top:2px">Multiplies current AU. Rescales every body, velocity, trail; G is retuned so orbits keep their 1-year period.</div>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('star')">☀ Star</button>
        <button class="btn add-btn" onclick="adminSpawn('blackhole')">🕳️ Black Hole</button>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('neutron')">💫 Neutron Star</button>
        <button class="btn add-btn" onclick="adminSpawn('strange')">🟢 Strange NS</button>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('magnetar')">⚡ Magnetar</button>
        <button class="btn add-btn" onclick="adminSpawn('planet')">✦ Planet</button>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('dwarf')">◐ Dwarf Star</button>
        <button class="btn add-btn" onclick="adminSpawn('lifeplanet')">🌍 Life Planet</button>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('forcerocket')">🚀 Launch Rocket</button>
        <button class="btn add-btn" onclick="adminSpawn('halley')" title="Halley's Comet — 76-year orbital period, eccentricity 0.967. Semi-major axis is solved from the period via Kepler's third law against the current G and Sun mass.">☄ Halley's Comet</button>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminLineUpBodies()" title="Line up every body in the scene edge-to-edge, smallest → biggest. Velocities are zeroed and the simulation is paused so you can size-compare them; press Play to release the line back into gravity." style="grid-column:1/-1;background:rgba(125,211,252,0.12);border-color:rgba(125,211,252,0.3);color:#7dd3fc">📏 Line Up Bodies (smallest → biggest)</button>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('redsupergiant')">🔴 Red Super Giant</button>
        <button class="btn add-btn" onclick="adminSpawn('bluesupergiant')">🔵 Blue Super Giant</button>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('ksupergiant')">🟠 K Super Giant</button>
      </div>
      <div style="font-size:0.7em;color:#555;text-transform:uppercase;letter-spacing:1.2px;margin:10px 0 4px">Named supermassives</div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('sagittariusa')">🕳️ Sagittarius A</button>
        <button class="btn add-btn" onclick="adminSpawn('ton618')">🕳️ TON 618</button>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('phoenixa')">🕳️ Phoenix A</button>
        <button class="btn add-btn" onclick="adminSpawn('m31star')">🕳️ M31*</button>
      </div>
      <div style="font-size:0.7em;color:#555;text-transform:uppercase;letter-spacing:1.2px;margin:10px 0 4px">Galaxies</div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('milkyway')">🌌 Milky Way</button>
        <button class="btn add-btn" onclick="adminSpawn('andromeda')">🌠 Andromeda</button>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('milkdromeda')">💫 Milkdromeda</button>
      </div>
      <div style="font-size:0.7em;color:#555;text-transform:uppercase;letter-spacing:1.2px;margin:10px 0 4px">Cosmic structure</div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('laniakea')">🕸 Laniakea Supercluster</button>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('universe')">🌌 Universe</button>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('rocket')">🚀 Launch Rocket</button>
      </div>
      <div style="font-size:0.7em;color:#555;text-transform:uppercase;letter-spacing:1.2px;margin:10px 0 4px">Named stars</div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('betelgeuse')">🔴 Betelgeuse</button>
        <button class="btn add-btn" onclick="adminSpawn('rigel')">🔵 Rigel</button>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('smallstar')">🟤 2MASS J0523-1403</button>
      </div>
      <div style="font-size:0.7em;color:#555;text-transform:uppercase;letter-spacing:1.2px;margin:10px 0 4px">Long-period transients</div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('askap1935')">🐌 ASKAP J1935+2148</button>
        <button class="btn add-btn" onclick="adminSpawn('askap1839')">🐌 ASKAP J1839-075</button>
      </div>
      <div style="font-size:0.7em;color:#555;text-transform:uppercase;letter-spacing:1.2px;margin:10px 0 4px">Named planets</div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('j1407b')">💍 J1407b</button>
        <button class="btn add-btn" onclick="adminSpawn('roxs42bb')">🪐 ROXs 42Bb</button>
      </div>
      <div class="btn-row">
        <button class="btn add-btn" onclick="adminSpawn('hd100546b')">🪐 HD 100546b</button>
      </div>
      <div class="btn-row">
        <button class="btn reset-btn" onclick="adminLogout()">Logout</button>
      </div>`;
  } else {
    el.innerHTML = `
      <div class="btn-row">
        <button class="btn" onclick="showAdminLogin()">🛡 Admin Login</button>
      </div>`;
  }
}

function toggleStarAfterlife() {
  starAfterlifeEnabled = !starAfterlifeEnabled;
  document.getElementById('btn-afterlife').classList.toggle('active', starAfterlifeEnabled);
}

function toggleFaces() {
  facesEnabled = !facesEnabled;
  const btn = document.getElementById('btn-faces');
  if (btn) btn.classList.toggle('active', facesEnabled);
}

// ---- Drag & select ----
let dragBody = null;
let dragArrowBody = null; // body whose arrow tip is being dragged
let dragGalaxy = null;    // a Universe/Laniakea galaxy being dragged
let isDragging = false;
let dragStartX = 0, dragStartY = 0;
let lastDragX = 0, lastDragY = 0;
let lastDragTime = 0;

// Pan state (dragging the view itself)
let panning = false;
let panStartX = 0, panStartY = 0;
let panStartViewX = 0, panStartViewY = 0;

function recenterView() {
  autoFollow = true;
  // Zoom to fit the most distant non-galaxy body (with margin) so the AU-scale
  // solar system is visible by default. Falls back to 1× when there's nothing
  // to fit (e.g. fresh empty scene).
  const cnv = document.getElementById('sim');
  const w = cnv ? cnv.clientWidth : 0;
  const h = cnv ? cnv.clientHeight : 0;
  const suns = bodies.filter(b => b.isSun);
  if (suns.length > 0 && bodies.length > 1 && w > 0 && h > 0) {
    const primarySun = suns.reduce((a, b) => a.mass >= b.mass ? a : b);
    let maxDist = 0;
    for (const b of bodies) {
      if (b === primarySun) continue;
      const dx = b.x - primarySun.x, dy = b.y - primarySun.y;
      const d = Math.sqrt(dx * dx + dy * dy);
      if (d > maxDist) maxDist = d;
    }
    if (maxDist > 0) {
      viewZoom = Math.max(1e-30, Math.min(Number.MAX_SAFE_INTEGER, (Math.min(w, h) * 0.45) / maxDist));
      return;
    }
  }
  viewZoom = 1;
}

// Pan + zoom the camera so a world-space disc of the given radius fits the
// viewport with a small margin. Used right after spawning huge objects
// (Universe, Laniakea, galaxies, ...) so they don't fall offscreen the
// instant they appear.
function fitCameraToObject(x, y, radius) {
  const cnv = document.getElementById('sim');
  if (!cnv) return;
  const w = cnv.clientWidth, h = cnv.clientHeight;
  if (!w || !h || !radius) return;
  // Aim for the diameter to occupy ~80% of the smaller viewport dimension.
  const targetZoom = (Math.min(w, h) * 0.8) / (radius * 2);
  viewZoom = Math.max(1e-30, Math.min(Number.MAX_SAFE_INTEGER, targetZoom));
  viewX = x;
  viewY = y;
  autoFollow = false;
}

function findBodyAtScreen(sx, sy) {
  const rect = canvas.getBoundingClientRect();
  const mx = sx - rect.left, my = sy - rect.top;
  if (is3D) {
    // Hit-test in screen space using the per-body projected position.
    let closest = null;
    let closestDist = Infinity;
    for (const b of bodies) {
      const proj = project3DScreen(b.x, b.y, b.z || 0);
      const dx = proj.sx - mx, dy = proj.sy - my;
      const dist = Math.sqrt(dx * dx + dy * dy);
      const hitRadius = Math.max(b.radius * proj.scale + 10, 18);
      if (dist < hitRadius && dist < closestDist) {
        closest = b;
        closestDist = dist;
      }
    }
    return closest;
  }
  const p = screenToWorld(sx, sy);
  // Hit radius is screen-space (so it stays clickable at any zoom)
  const padScreen = 10 / viewZoom;
  const minScreen = 18 / viewZoom;
  let closest = null;
  let closestDist = Infinity;
  for (const b of bodies) {
    const dx = b.x - p.x, dy = b.y - p.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    const hitRadius = Math.max(b.radius + padScreen, minScreen);
    if (dist < hitRadius && dist < closestDist) {
      closest = b;
      closestDist = dist;
    }
  }
  return closest;
}

// Find a draggable galaxy (Universe or Laniakea) whose center is near the
// click point in screen space. A small hit radius (30px) around the center
// means clicking anywhere ELSE inside the galaxy disc still pans the view,
// so the user isn't trapped when zoomed inside a huge object.
function findGalaxyAtScreen(sx, sy) {
  const w = canvas.clientWidth, h = canvas.clientHeight;
  const HIT_RADIUS = 30;
  let closest = null;
  let closestDist = Infinity;
  for (const g of galaxies) {
    if (g.type !== 'universe' && g.type !== 'laniakea') continue;
    let screenX, screenY;
    if (is3D) {
      const proj = project3DScreen(g.x, g.y, 0);
      screenX = proj.sx;
      screenY = proj.sy;
    } else {
      screenX = (g.x - viewX) * viewZoom + w / 2;
      screenY = (g.y - viewY) * viewZoom + h / 2;
    }
    const dx = sx - screenX, dy = sy - screenY;
    const d = Math.sqrt(dx * dx + dy * dy);
    if (d < HIT_RADIUS && d < closestDist) {
      closest = g;
      closestDist = d;
    }
  }
  return closest;
}

function findArrowTipAtScreen(sx, sy) {
  if (!showVectors) return null;
  if (is3D) {
    const rect = canvas.getBoundingClientRect();
    const mx = sx - rect.left, my = sy - rect.top;
    for (const b of bodies) {
      const tipWX = b.x + b.vx * VEL_ARROW_SCALE;
      const tipWY = b.y + b.vy * VEL_ARROW_SCALE;
      const tipWZ = (b.z || 0) + (b.vz || 0) * VEL_ARROW_SCALE;
      const proj = project3DScreen(tipWX, tipWY, tipWZ);
      const dx = proj.sx - mx, dy = proj.sy - my;
      if (Math.sqrt(dx * dx + dy * dy) < 12) return b;
    }
    return null;
  }
  const p = screenToWorld(sx, sy);
  const hitRadius = 10 / viewZoom;
  for (const b of bodies) {
    const tipX = b.x + b.vx * VEL_ARROW_SCALE;
    const tipY = b.y + b.vy * VEL_ARROW_SCALE;
    const dx = tipX - p.x, dy = tipY - p.y;
    if (Math.sqrt(dx * dx + dy * dy) < hitRadius) return b;
  }
  return null;
}

// 3D camera rotation drag state
let rotating3D = false;
let rotateStartX = 0, rotateStartY = 0;
let rotateStartYaw = 0, rotateStartPitch = 0;

canvas.addEventListener('contextmenu', function(e) {
  // Suppress the context menu so right-click can be used for 3D camera rotation
  if (is3D) e.preventDefault();
});

canvas.addEventListener('mousedown', function(e) {
  // 3D rotation: right-click drag, or Shift + left-click drag on empty space.
  if (is3D && (e.button === 2 || (e.button === 0 && e.shiftKey))) {
    rotating3D = true;
    rotateStartX = e.clientX;
    rotateStartY = e.clientY;
    rotateStartYaw = cameraYaw;
    rotateStartPitch = cameraPitch;
    canvas.style.cursor = 'move';
    e.preventDefault();
    return;
  }

  // Check arrow tips first
  const arrowBody = findArrowTipAtScreen(e.clientX, e.clientY);
  if (arrowBody) {
    dragArrowBody = arrowBody;
    isDragging = true;
    canvas.style.cursor = 'move';
    return;
  }

  const body = findBodyAtScreen(e.clientX, e.clientY);
  if (body) {
    dragBody = body;
    isDragging = false;
    dragStartX = e.clientX;
    dragStartY = e.clientY;
    lastDragX = e.clientX;
    lastDragY = e.clientY;
    lastDragTime = performance.now();
    canvas.style.cursor = 'grabbing';
    return;
  }

  // Universe / Laniakea center: pick up the whole galaxy.
  const galaxy = findGalaxyAtScreen(e.clientX, e.clientY);
  if (galaxy) {
    dragGalaxy = galaxy;
    isDragging = false;
    dragStartX = e.clientX;
    dragStartY = e.clientY;
    canvas.style.cursor = 'grabbing';
    return;
  }

  // Empty space: start panning the view
  panning = true;
  autoFollow = false;
  panStartX = e.clientX;
  panStartY = e.clientY;
  panStartViewX = viewX;
  panStartViewY = viewY;
  canvas.style.cursor = 'grabbing';
});

canvas.addEventListener('wheel', function(e) {
  e.preventDefault();
  const factor = e.deltaY < 0 ? 1.15 : 1 / 1.15;
  // No upper or lower bound on zoom — only floor at a tiny positive value so
  // 1 / viewZoom transforms don't blow up, and cap at MAX_SAFE_INTEGER so
  // pathological scroll bursts don't overflow.
  const newZoom = Math.max(1e-30, Math.min(Number.MAX_SAFE_INTEGER, viewZoom * factor));
  if (newZoom === viewZoom) return;

  // Keep the world point under the mouse fixed during zoom
  const before = screenToWorld(e.clientX, e.clientY);
  viewZoom = newZoom;
  const after = screenToWorld(e.clientX, e.clientY);
  viewX += before.x - after.x;
  viewY += before.y - after.y;
  autoFollow = false;
}, { passive: false });

canvas.addEventListener('mousemove', function(e) {
  // 3D rotation drag: ~0.6 radians per full canvas width.
  if (rotating3D) {
    const w = canvas.clientWidth || 1, h = canvas.clientHeight || 1;
    const dxs = e.clientX - rotateStartX;
    const dys = e.clientY - rotateStartY;
    cameraYaw = rotateStartYaw + (dxs / w) * Math.PI;
    cameraPitch = rotateStartPitch + (dys / h) * Math.PI;
    // Clamp pitch so users can't flip the camera fully upside down (gets disorienting)
    const PITCH_LIMIT = Math.PI / 2 - 0.05;
    if (cameraPitch > PITCH_LIMIT) cameraPitch = PITCH_LIMIT;
    if (cameraPitch < -PITCH_LIMIT) cameraPitch = -PITCH_LIMIT;
    if (typeof syncCameraSliders === 'function') syncCameraSliders();
    return;
  }

  // Pan: drag the view itself
  if (panning) {
    const dxs = e.clientX - panStartX;
    const dys = e.clientY - panStartY;
    viewX = panStartViewX - dxs / viewZoom;
    viewY = panStartViewY - dys / viewZoom;
    return;
  }

  // Arrow tip drag
  if (dragArrowBody) {
    const p = screenToWorld(e.clientX, e.clientY);
    dragArrowBody.vx = (p.x - dragArrowBody.x) / VEL_ARROW_SCALE;
    dragArrowBody.vy = (p.y - dragArrowBody.y) / VEL_ARROW_SCALE;
    return;
  }

  if (dragGalaxy) {
    const dx = e.clientX - dragStartX;
    const dy = e.clientY - dragStartY;
    if (Math.abs(dx) > 3 || Math.abs(dy) > 3) isDragging = true;
    if (isDragging) {
      const p = screenToWorld(e.clientX, e.clientY);
      dragGalaxy.x = p.x;
      dragGalaxy.y = p.y;
    }
    return;
  }

  if (!dragBody) {
    // Show appropriate cursor on hover
    const arrowHit = findArrowTipAtScreen(e.clientX, e.clientY);
    if (arrowHit) {
      canvas.style.cursor = 'move';
    } else {
      const body = findBodyAtScreen(e.clientX, e.clientY);
      if (body) {
        canvas.style.cursor = 'grab';
      } else if (findGalaxyAtScreen(e.clientX, e.clientY)) {
        canvas.style.cursor = 'grab';
      } else {
        canvas.style.cursor = 'crosshair';
      }
    }
    return;
  }

  const dx = e.clientX - dragStartX;
  const dy = e.clientY - dragStartY;
  if (Math.abs(dx) > 3 || Math.abs(dy) > 3) isDragging = true;

  if (isDragging) {
    const p = screenToWorld(e.clientX, e.clientY);
    dragBody.x = p.x;
    dragBody.y = p.y;
    dragBody.vx = 0;
    dragBody.vy = 0;
    dragBody.trail = [];

    // Track velocity for fling (in world units per frame)
    const now = performance.now();
    const dt = (now - lastDragTime) / 1000;
    if (dt > 0) {
      dragBody._flingVx = ((e.clientX - lastDragX) / viewZoom) / dt / 60;
      dragBody._flingVy = ((e.clientY - lastDragY) / viewZoom) / dt / 60;
    }
    lastDragX = e.clientX;
    lastDragY = e.clientY;
    lastDragTime = now;
  }
});

canvas.addEventListener('mouseup', function(e) {
  if (rotating3D) {
    rotating3D = false;
    canvas.style.cursor = 'crosshair';
    return;
  }
  if (panning) {
    panning = false;
    canvas.style.cursor = 'crosshair';
    return;
  }
  // Arrow drag release
  if (dragArrowBody) {
    dragArrowBody = null;
    isDragging = false;
    canvas.style.cursor = 'crosshair';
    return;
  }
  // Galaxy drag release
  if (dragGalaxy) {
    dragGalaxy = null;
    isDragging = false;
    canvas.style.cursor = 'crosshair';
    return;
  }

  if (dragBody) {
    if (isDragging) {
      // Locked bodies stay put on release; everything else gets a fling
      if (dragBody.locked) {
        dragBody.vx = 0;
        dragBody.vy = 0;
      } else {
        dragBody.vx = dragBody._flingVx || 0;
        dragBody.vy = dragBody._flingVy || 0;
      }
      delete dragBody._flingVx;
      delete dragBody._flingVy;
    } else {
      // It was a click, not a drag — no selection change needed
    }
    dragBody = null;
    isDragging = false;
    canvas.style.cursor = 'crosshair';
  } else {
    // Clicked empty space — no action needed
  }
});

// Cancel drag if mouse leaves canvas
canvas.addEventListener('mouseleave', function() {
  if (rotating3D) {
    rotating3D = false;
  }
  if (panning) {
    panning = false;
  }
  if (dragArrowBody) {
    dragArrowBody = null;
  }
  if (dragBody && isDragging) {
    if (dragBody.locked) {
      dragBody.vx = 0;
      dragBody.vy = 0;
    } else {
      dragBody.vx = dragBody._flingVx || 0;
      dragBody.vy = dragBody._flingVy || 0;
    }
    delete dragBody._flingVx;
    delete dragBody._flingVy;
  }
  dragBody = null;
  isDragging = false;
  canvas.style.cursor = 'crosshair';
});

// ---- Dropdown body select ----
// Two dropdowns: pick body A and body B to see the gravitational force
// between exactly those two bodies (not the nearest-neighbor pairing).
function populateBodySelect() {
  // Asteroids are excluded — hundreds of unselectable rocks would bury the
  // suns and planets the user actually cares about pairing.
  const opts = bodies.filter(b => !b.isAsteroid).map(b =>
    `<option value="${b.id}">${b.isSun ? '☀' : '✦'} ${b.name}</option>`
  ).join('');
  for (const which of ['a', 'b']) {
    const sel = document.getElementById('body-select-' + which);
    if (!sel) continue;
    const prevVal = sel.value;
    const placeholder = `<option value="">Body ${which.toUpperCase()}…</option>`;
    sel.innerHTML = placeholder + opts;
    if (prevVal && bodies.find(b => b.id === prevVal)) {
      sel.value = prevVal;
    } else {
      sel.value = '';
      if (which === 'a') selectedBodyAId = null;
      else selectedBodyBId = null;
    }
  }
  if (!selectedBodyAId || !selectedBodyBId) clearEquation();
}

function onBodySelectA(id) {
  selectedBodyAId = id || null;
  if (!selectedBodyAId) clearEquation();
}

function onBodySelectB(id) {
  selectedBodyBId = id || null;
  if (!selectedBodyBId) clearEquation();
}

// Compact number formatter that emits plain HTML — no MathJax round-trip.
function fmtEq(v) {
  const abs = Math.abs(v);
  if (!isFinite(v)) return '∞';
  if (abs !== 0 && (abs >= 1e5 || abs < 1e-3)) {
    const s = v.toExponential(2); // e.g. "1.35e+10"
    const [mantissa, expPart] = s.split('e');
    return mantissa + '×10<sup>' + parseInt(expPart, 10) + '</sup>';
  }
  if (abs >= 1000) return Math.round(v).toString();
  return v.toFixed(2);
}

function escapeHtml(s) {
  return String(s).replace(/[&<>"']/g, c => (
    { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]
  ));
}

function updateEquation(bodyA, bodyB) {
  if (!bodyA || !bodyB || bodyA === bodyB) { clearEquation(); return; }
  const dx = bodyB.x - bodyA.x, dy = bodyB.y - bodyA.y;
  const dz = (bodyB.z || 0) - (bodyA.z || 0);
  const r = Math.sqrt(dx * dx + dy * dy + dz * dz);
  if (r <= 0) { clearEquation(); return; }
  // Textbook form so the rendered equation balances. (The simulator adds a
  // small softening term internally for stability; at normal separations it
  // makes no visible difference.)
  const force = G_BASE * bodyA.mass * bodyB.mass / (r * r);

  const el = document.getElementById('eq-values');
  el.style.opacity = '1';
  el.style.color = '';

  // Plain HTML — instant. MathJax was burning ~50–150 ms per call and the
  // 120 ms debounce meant the result never appeared while running.
  el.innerHTML =
    `<span style="color:#34d399;font-weight:600">${fmtEq(force)}</span>` +
    ` = ${fmtEq(G_BASE)} · ` +
    `${fmtEq(bodyA.mass)}<span style="color:#777"> (${escapeHtml(bodyA.name)})</span> · ` +
    `${fmtEq(bodyB.mass)}<span style="color:#777"> (${escapeHtml(bodyB.name)})</span>` +
    ` / ${fmtEq(r)}<sup>2</sup>`;
}

function clearEquation() {
  const el = document.getElementById('eq-values');
  el.style.opacity = '0.4';
  el.style.color = '#555';
  el.innerHTML = 'Select two bodies to see values';
}

// ---- Init ----
document.getElementById('btn-trails').classList.add('active');
renderAdminSection();
renderSaveSection();
renderCreatorSection();
requestAnimationFrame(function firstFrame(t) {
  if (needsInit) {
    resize();
    createDefaultBodies();
    initialState = deepCopy(bodies);
    buildControls();
    needsInit = false;
    // AU-scale orbits put Earth ~145k units from the sun — start zoomed out
    // so the solar system is visible on first paint.
    recenterView();
  }
  loop(t);
});
