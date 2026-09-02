"use strict";
/* ======================================================================
   PART 1 — QP mutation engine (Derksen–Weyman–Zelevinsky mutation; the
   reduction step implements DWZ's Splitting Theorem via Lemmas 4.7-4.8,
   arXiv:0704.0649).
   ====================================================================== */
// Defined as a named factory rather than an IIFE so that its source can be
// handed to a Web Worker verbatim: QPEngine.toString() returns exactly the
// text below, which makeWorkerSource() drops into a Blob the worker is
// built from. Two consequences worth respecting when editing this:
//   * nothing in here may reference anything outside it (it will not exist
//     in the worker), and
//   * it carries its own 'use strict', since the file-level one does not
//     travel with the source text.
// It is also why this file must not be minified with name mangling.
function QPEngine() {
  'use strict';
  // ---------- Coefficient fields: exact rationals (Q), or a prime field F_p ----------
  // Every function below this point only ever touches coefficients through
  // fadd/fsub/fmul/fdiv/fneg/finv/fisZero/feq/fone/fzero/fToString/F. None
  // of it inspects {n,d} structurally, so setField() alone is enough to
  // make every computation — potentials, mutation, the linear-algebra
  // diagonalization — run over the new field with no other changes.
  function gcdBig(a, b) { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) { [a, b] = [b, a % b]; } return a; }
  function gcdNum(a, b) { a = a < 0 ? -a : a; b = b < 0 ? -b : b; while (b) { const t = a % b; a = b; b = t; } return a; }
  // Coefficients are {n, d} whose two components are either both plain
  // Numbers or both BigInts, and Numbers are the canonical form whenever
  // the value fits exactly in a double (|n|, d <= 2^53-1). BigInt
  // arithmetic is roughly 20x slower than Number arithmetic here and
  // allocates on every single operation, while the overwhelming majority
  // of coefficients in a QP computation are small integers. Every
  // operation below therefore tries the Number path first and redoes
  // itself in BigInt only when an intermediate would leave the exact
  // range; any BigInt result that fits comes back down. Because a value
  // has exactly ONE representation either way, equality and zero-testing
  // stay simple comparisons (they still tolerate a mixed pair, cheaply).
  const toBig = (v) => (typeof v === 'bigint' ? v : BigInt(v));
  const MAX_SAFE_BIG = BigInt(Number.MAX_SAFE_INTEGER);
  const isSafe = Number.isSafeInteger;

  function isPrime(nRaw) {
    const n = typeof nRaw === 'bigint' ? nRaw : BigInt(nRaw);
    if (n < 2n) return false;
    if (n < 4n) return true;
    if (n % 2n === 0n) return false;
    for (let i = 3n; i * i <= n; i += 2n) if (n % i === 0n) return false;
    return true;
  }

  function modInverse(aRaw, p) {
    let a = ((aRaw % p) + p) % p;
    if (a === 0n) throw new Error(`0 has no inverse mod ${p}`);
    let [oldR, r] = [a, p];
    let [oldS, s] = [1n, 0n];
    while (r !== 0n) {
      const q = oldR / r;
      [oldR, r] = [r, oldR - q * r];
      [oldS, s] = [s, oldS - q * s];
    }
    return ((oldS % p) + p) % p;
  }

  const RationalField = (() => {
    // Both components exact Numbers, d !== 0: reduce and fix the sign.
    function fromNum(n, d) {
      if (d < 0) { n = -n; d = -d; }
      if (d === 1) return { n, d: 1 };
      const g = gcdNum(n, d) || 1;
      return { n: n / g, d: d / g };
    }
    // Same in BigInt, demoting back to Numbers when the reduced value fits
    // — that demotion is what keeps the representation canonical.
    function fromBig(n, d) {
      if (d === 0n) throw new Error('division by zero');
      if (d < 0n) { n = -n; d = -d; }
      if (d !== 1n) { const g = gcdBig(n, d) || 1n; n /= g; d /= g; }
      if (n <= MAX_SAFE_BIG && -n <= MAX_SAFE_BIG && d <= MAX_SAFE_BIG) return { n: Number(n), d: Number(d) };
      return { n, d };
    }
    function make(n, d = 1) {
      if (typeof n === 'number' && typeof d === 'number') {
        if (d === 0) throw new Error('division by zero');
        if (isSafe(n) && isSafe(d)) return fromNum(n, d);
      }
      return fromBig(toBig(n), toBig(d));
    }
    const bothNum = (x, y) => typeof x.n === 'number' && typeof y.n === 'number';
    // isSafe() on an integer result is an exact overflow test: two exact
    // integer doubles whose true sum/product exceeds 2^53-1 always round
    // to something >= 2^53, which isSafe rejects. So a Number path that
    // passes these checks computed the exact value, and one that fails
    // falls through to BigInt with nothing lost.
    return {
      kind: 'Q', label: 'Q',
      make,
      add: (x, y) => {
        if (bothNum(x, y)) {
          if (x.d === 1 && y.d === 1) { const s = x.n + y.n; if (isSafe(s)) return { n: s, d: 1 }; }
          else {
            const a = x.n * y.d, b = y.n * x.d, d = x.d * y.d, s = a + b;
            if (isSafe(a) && isSafe(b) && isSafe(d) && isSafe(s)) return fromNum(s, d);
          }
        }
        return fromBig(toBig(x.n) * toBig(y.d) + toBig(y.n) * toBig(x.d), toBig(x.d) * toBig(y.d));
      },
      sub: (x, y) => {
        if (bothNum(x, y)) {
          if (x.d === 1 && y.d === 1) { const s = x.n - y.n; if (isSafe(s)) return { n: s, d: 1 }; }
          else {
            const a = x.n * y.d, b = y.n * x.d, d = x.d * y.d, s = a - b;
            if (isSafe(a) && isSafe(b) && isSafe(d) && isSafe(s)) return fromNum(s, d);
          }
        }
        return fromBig(toBig(x.n) * toBig(y.d) - toBig(y.n) * toBig(x.d), toBig(x.d) * toBig(y.d));
      },
      mul: (x, y) => {
        if (bothNum(x, y)) {
          const n = x.n * y.n, d = x.d * y.d;
          if (isSafe(n) && isSafe(d)) return (x.d === 1 && y.d === 1) ? { n, d: 1 } : fromNum(n, d);
        }
        return fromBig(toBig(x.n) * toBig(y.n), toBig(x.d) * toBig(y.d));
      },
      div: (x, y) => {
        if (y.n === 0 || y.n === 0n) throw new Error('division by zero');
        if (bothNum(x, y)) {
          const n = x.n * y.d, d = x.d * y.n;
          if (isSafe(n) && isSafe(d)) return fromNum(n, d);
        }
        return fromBig(toBig(x.n) * toBig(y.d), toBig(x.d) * toBig(y.n));
      },
      // Already reduced with d > 0, and negating changes neither — so this
      // needs no normalization pass at all, in either representation.
      neg: (x) => ({ n: -x.n, d: x.d }),
      inv: (x) => make(x.d, x.n),
      isZero: (x) => x.n === 0 || x.n === 0n,
      eq: (x, y) => x.n == y.n && x.d == y.d, // eslint-disable-line eqeqeq -- exact across Number/BigInt
      toString: (x) => (x.d === 1 || x.d === 1n ? String(x.n) : `${x.n}/${x.d}`),
    };
  })();

  // Extended Euclid in Number arithmetic. Only used when p < 2^26, where
  // every intermediate (q * s is bounded by ~2p, residue products by p^2)
  // stays well inside the exact-integer range of a double.
  function modInverseNum(aRaw, p) {
    let a = aRaw % p; if (a < 0) a += p;
    if (a === 0) throw new Error(`0 has no inverse mod ${p}`);
    let oldR = a, r = p, oldS = 1, s = 0;
    while (r !== 0) {
      const q = Math.floor(oldR / r);
      const tr = oldR - q * r; oldR = r; r = tr;
      const ts = oldS - q * s; oldS = s; s = ts;
    }
    return ((oldS % p) + p) % p;
  }

  // For p < 2^26 every residue, and every product of two residues, is an
  // exact double — so the whole field runs in plain Number arithmetic with
  // no BigInt allocation anywhere in the inner loop. Elements are still
  // {n, d} with d = 1, and n is always already reduced into [0, p), so the
  // operations below can take their inputs at face value; only make(),
  // which is the one entry point for foreign values, reduces.
  const SMALL_PRIME_LIMIT = 67108864n; // 2^26
  function makeSmallPrimeField(pBig) {
    const p = Number(pBig);
    const red = (n) => { const m = n % p; return m < 0 ? m + p : m; };
    const toRes = (v) => (typeof v === 'bigint' ? Number(((v % pBig) + pBig) % pBig) : red(v));
    function make(n, d = 1) {
      const dr = toRes(d);
      if (dr === 0) throw new Error(`denominator is 0 mod ${p}`);
      const nr = toRes(n);
      return { n: dr === 1 ? nr : (nr * modInverseNum(dr, p)) % p, d: 1 };
    }
    return {
      kind: 'Fp', p: pBig, label: `F_${p}`,
      make,
      add: (x, y) => { const s = x.n + y.n; return { n: s >= p ? s - p : s, d: 1 }; },
      sub: (x, y) => { const s = x.n - y.n; return { n: s < 0 ? s + p : s, d: 1 }; },
      mul: (x, y) => ({ n: (x.n * y.n) % p, d: 1 }),
      div: (x, y) => { if (y.n === 0) throw new Error('division by zero'); return { n: (x.n * modInverseNum(y.n, p)) % p, d: 1 }; },
      neg: (x) => ({ n: x.n === 0 ? 0 : p - x.n, d: 1 }),
      inv: (x) => { if (x.n === 0) throw new Error('division by zero'); return { n: modInverseNum(x.n, p), d: 1 }; },
      isZero: (x) => x.n === 0 || x.n === 0n,
      eq: (x, y) => x.n == y.n, // eslint-disable-line eqeqeq -- exact across Number/BigInt
      toString: (x) => String(x.n),
    };
  }

  function makePrimeField(pRaw) {
    const p = toBig(pRaw);
    if (!isPrime(p)) throw new Error(`${p} is not prime`);
    if (p < SMALL_PRIME_LIMIT) return makeSmallPrimeField(p);
    // p too large for exact double arithmetic: keep the BigInt field. Its
    // operations coerce, since the shared fone/fzero constants are Numbers.
    const reduce = (n) => { n = toBig(n) % p; return n < 0n ? n + p : n; };
    const x_isZero = (x) => x.n === 0n || x.n === 0;
    function make(n, d = 1n) {
      const dr = reduce(d);
      if (dr === 0n) throw new Error(`denominator is 0 mod ${p}`);
      return { n: reduce(toBig(n) * modInverse(dr, p)), d: 1n };
    }
    return {
      kind: 'Fp', p, label: `F_${p}`,
      make,
      add: (x, y) => ({ n: reduce(toBig(x.n) + toBig(y.n)), d: 1n }),
      sub: (x, y) => ({ n: reduce(toBig(x.n) - toBig(y.n)), d: 1n }),
      mul: (x, y) => ({ n: reduce(toBig(x.n) * toBig(y.n)), d: 1n }),
      div: (x, y) => { if (x_isZero(y)) throw new Error('division by zero'); return { n: reduce(toBig(x.n) * modInverse(toBig(y.n), p)), d: 1n }; },
      neg: (x) => ({ n: reduce(-toBig(x.n)), d: 1n }),
      inv: (x) => { if (x_isZero(x)) throw new Error('division by zero'); return { n: modInverse(toBig(x.n), p), d: 1n }; },
      isZero: (x) => x.n === 0n || x.n === 0,
      eq: (x, y) => x.n == y.n, // eslint-disable-line eqeqeq -- exact across Number/BigInt
      toString: (x) => x.n.toString(),
    };
  }

  let CoeffField = RationalField;
  function getField() { return CoeffField; }
  function setField(field) { CoeffField = field; }

  function F(n, d = 1) { return CoeffField.make(n, d); }
  const fadd = (x, y) => CoeffField.add(x, y);
  const fsub = (x, y) => CoeffField.sub(x, y);
  const fmul = (x, y) => CoeffField.mul(x, y);
  const fdiv = (x, y) => CoeffField.div(x, y);
  const fneg = (x) => CoeffField.neg(x);
  const finv = (x) => CoeffField.inv(x);
  const fisZero = (x) => CoeffField.isZero(x);
  const feq = (x, y) => CoeffField.eq(x, y);
  // 0 and 1 have the same {n,d} shape in every field this module supports,
  // so these stay valid across setField() calls with no redefinition. They
  // are Numbers: that is the canonical representation in Q and in every
  // small prime field, and the BigInt fallbacks coerce their inputs.
  const fone = { n: 1, d: 1 }, fzero = { n: 0, d: 1 };
  function fToString(x) { return CoeffField.toString(x); }
  function fParse(str) {
    str = String(str).trim();
    if (str === '' || str === '-' ) throw new Error('empty coefficient');
    const m = str.match(/^(-?\d+)\s*\/\s*(-?\d+)$/);
    if (m) return F(BigInt(m[1]), BigInt(m[2]));
    if (!/^-?\d+$/.test(str)) throw new Error('bad coefficient: ' + str);
    return F(BigInt(str));
  }

  function makeQuiver() { return { vertices: new Map(), arrows: new Map(), nextVertexId: 0, nextArrowId: 0 }; }
  function addVertex(Q, label, x = 0, y = 0) {
    const id = Q.nextVertexId++;
    Q.vertices.set(id, { id, label: label ?? String(id), x, y });
    return id;
  }
  function addArrow(Q, source, target, label) {
    const id = Q.nextArrowId++;
    Q.arrows.set(id, { id, label: label ?? defaultArrowLabel(id), source, target });
    return id;
  }
  function defaultArrowLabel(id) {
    const letters = 'abcdefghijklmnopqrstuvwxyz';
    const round = Math.floor(id / 26);
    const letter = letters[id % 26];
    return round === 0 ? letter : letter + (round + 1);
  }

  function canonicalWord(word) {
    // Pick one word in the equivalence class of words up to cyclical
    // equivalence: the lexicographically least rotation. Found by comparing
    // rotations in place through index arithmetic rather than materializing
    // them — the old version allocated n arrays of length n on every call,
    // and this is called on every single potAdd.
    const n = word.length;
    if (n < 2) return word.slice();
    let best = 0;
    for (let i = 1; i < n; i++) {
      for (let j = 0; j < n; j++) {
        const x = word[best + j < n ? best + j : best + j - n];
        const y = word[i + j < n ? i + j : i + j - n];
        if (x !== y) { if (y < x) best = i; break; }
      }
    }
    if (best === 0) return word.slice();
    const out = new Array(n);
    for (let j = 0; j < n; j++) out[j] = word[best + j < n ? best + j : best + j - n];
    return out;
  }
  function keyOf(word) { return word.join(','); }

  function potAdd(map, word, coeff) {
    // Add potentials and delete it if it's 0
    if (word.length < 2) return;
    const canon = canonicalWord(word);
    const key = keyOf(canon);
    const existing = map.get(key);
    const newCoeff = existing ? fadd(existing.coeff, coeff) : coeff;
    if (fisZero(newCoeff)) map.delete(key); else map.set(key, { word: canon, coeff: newCoeff });
  }
  function potTruncate(map, maxLen, truncated) {
    // In general, a potential lives in the completed path algebra. This removes the cycles of length > maxlen in the potential.
    // `truncated`, if given, gets its `.value` set to true whenever a term
    // actually gets dropped here — the most basic and most frequently-hit
    // of the several places this function's length cap silently discards
    // content, so callers that want to report it need this.
    const m = new Map();
    for (const [k, v] of map) { if (v.word.length <= maxLen) m.set(k, v); else if (truncated) truncated.value = true; }
    return m;
  }
  // Do two potentials (as term maps) hold exactly the same terms with the
  // same coefficients? Used to detect a fixed point of the splitting
  // iteration below (a round that no longer visibly changes anything at
  // the current length cap).
  function potEqual(a, b) {
    if (a.size !== b.size) return false;
    for (const [key, t] of a) {
      const o = b.get(key);
      if (!o || !feq(t.coeff, o.coeff)) return false;
    }
    return true;
  }
  // Partition of a potential's terms used by the splitting step (DWZ
  // Lemmas 4.7-4.8) below: current = Sum_k(gamma_k delta_k) + R, and this
  // splits R into u_k, v_k for EVERY pair k at once — a term goes into
  // u[k] if gamma_k is the highest-priority special arrow it contains
  // (priority is a fixed order over all 2N special arrows, ties among
  // repeats of the same arrow broken by position), into v[idx] if
  // delta_k is, and is otherwise left alone (it names no special arrow).
  // This is a genuine partition of R's terms, not a sum of one-sided
  // cyclic derivatives, which would double-count a term containing more
  // than one special arrow (e.g. both gamma_k and delta_k, or gamma_i and
  // gamma_j for i != j).
  function splitByPriority(current, pairs, priorityOf, roleOf) {
    const quadKeys = new Set(pairs.map(p => keyOf(canonicalWord([p.gamma, p.delta]))));
    const u = pairs.map(() => new Map()), v = pairs.map(() => new Map());
    for (const [key, t] of current) {
      if (quadKeys.has(key)) continue;
      const { word, coeff } = t;
      let bestPos = -1, bestPriority = Infinity;
      for (let i = 0; i < word.length; i++) {
        const pr = priorityOf.get(word[i]);
        if (pr !== undefined && pr < bestPriority) { bestPriority = pr; bestPos = i; }
      }
      if (bestPos === -1) continue; // names no special arrow
      const { kind, idx } = roleOf.get(word[bestPos]);
      const path = word.slice(bestPos + 1).concat(word.slice(0, bestPos));
      const bucket = (kind === 'gamma' ? u : v)[idx];
      const pkey = keyOf(path);
      const existing = bucket.get(pkey);
      const nc = existing ? fadd(existing.coeff, coeff) : coeff;
      if (fisZero(nc)) bucket.delete(pkey); else bucket.set(pkey, { path, coeff: nc });
    }
    return { u, v };
  }
  function applySubstitution(map, substitutions, maxLen, truncated) {
    // Replaces an arrow by a chosen substitution (linear combination of paths).
    // Used when replacing ab by [ab] and when deleting 2-cycles.
    // `truncated`, if given, gets its `.value` set to true whenever a
    // partial or final word is dropped purely for exceeding maxLen — a
    // whole substituted term can vanish this way (its length pushed past
    // the cap by a long replacement) without ever leaving behind a
    // recognizable "stray reference to a deleted arrow" for a caller to
    // spot on its own, so this is the only way such a drop gets reported.
    //
    // Expansion is a depth-first walk over the word writing into one shared
    // buffer, so a branch costs nothing until it completes a word: the
    // previous version copied the whole partial word (concat) at every
    // position of every branch. The walk visits the branches in the same
    // order as that version did, so terms still reach potAdd in the same
    // order and identical potentials come out.
    //
    // `map` is expected to be keyed the way every potential in this module
    // is — each key the canonical key of its own word — which is what lets
    // the untouched-term path below reuse a key instead of recomputing it.
    const out = new Map();
    const buf = [];
    // Shortest replacement of each substituted arrow, computed once for the
    // whole call rather than per term (a substitution set can hold thousands
    // of paths, so rescanning it per position was itself significant). An
    // arrow with no substitution stands for itself, so it counts 1; an arrow
    // substituted by nothing counts 0, because such a term produces no words
    // at all and that is not a length-cap drop.
    const minLenCache = new Map();
    const minLen = (id) => {
      let m = minLenCache.get(id);
      if (m !== undefined) return m;
      const s = substitutions.get(id);
      m = 1;
      if (s) {
        m = Infinity;
        for (const x of s) if (x.path.length < m) m = x.path.length;
        if (m === Infinity) m = 0;
      }
      minLenCache.set(id, m);
      return m;
    };
    const merge = (key, word, c) => {
      const existing = out.get(key);
      const nc = existing ? fadd(existing.coeff, c) : c;
      if (fisZero(nc)) out.delete(key); else out.set(key, { word, coeff: nc });
    };
    for (const [key, { word, coeff }] of map) {
      // A term naming none of the substituted arrows comes through the
      // expansion below completely unchanged, so hand it straight over.
      // Typically most of the potential: a diagonalization block touches
      // one vertex pair, and a splitting round touches only the 2N arrows
      // of its 2-cycles. Its word is already canonical (that is what the
      // key means), so this skips canonicalWord and the copying both.
      let touched = false;
      for (let i = 0; i < word.length; i++) if (substitutions.has(word[i])) { touched = true; break; }
      if (!touched) {
        if (word.length > maxLen) { if (truncated) truncated.value = true; continue; }
        if (word.length >= 2) merge(key, word, coeff);
        continue;
      }
      const n = word.length;
      // minRest[i] is the shortest the rest of the word can possibly become
      // from position i onwards. A branch whose length already exceeds the
      // cap once that minimum is added cannot finish under the cap, so it is
      // never entered — which is the whole game in the splitting rounds,
      // where phi(gamma) = gamma - v expands each occurrence into as many
      // ways as v has paths and the vast majority of the resulting words are
      // over-length. Without this, those words were built and then thrown
      // away: on a real 8-vertex quiver at maxLen 16, 96% of the expansion
      // was discarded and one substitution took 89 seconds.
      const minRest = new Array(n + 1);
      minRest[n] = 0;
      for (let i = n - 1; i >= 0; i--) minRest[i] = minRest[i + 1] + minLen(word[i]);
      const walk = (i, len, c) => {
        if (len > maxLen) { if (truncated) truncated.value = true; return; }
        if (i === n) { potAdd(out, buf.slice(0, len), c); return; }
        const subs = substitutions.get(word[i]);
        if (!subs) { buf[len] = word[i]; walk(i + 1, len + 1, c); return; }
        const room = maxLen - len - minRest[i + 1];
        for (const { path, coeff: pc } of subs) {
          // Skipped rather than descended into: the words this branch would
          // reach are exactly the over-length ones the walk used to build
          // and drop, so the drop is still reported. The paths are visited
          // in their original order (sorting them by length would prune a
          // little harder, but it changes the order words are produced, and
          // with it the order of the resulting potential).
          if (path.length > room) { if (truncated) truncated.value = true; continue; }
          for (let j = 0; j < path.length; j++) buf[len + j] = path[j];
          walk(i + 1, len + path.length, fmul(c, pc));
        }
      };
      walk(0, 0, coeff);
    }
    return out;
  }

  // ---------- Small Fraction-matrix helpers, for diagonalizing a bilinear form ----------
  function comboScale(combo, scalar) {
    const out = new Map();
    for (const [id, c] of combo) { const nc = fmul(c, scalar); if (!fisZero(nc)) out.set(id, nc); }
    return out;
  }
  function comboSub(a, b) {
    const out = new Map(a);
    for (const [id, c] of b) {
      const nc = fsub(out.get(id) || fzero, c);
      if (fisZero(nc)) out.delete(id); else out.set(id, nc);
    }
    return out;
  }
  // Gauss-Jordan inverse of a square Fraction matrix. Only needed for a
  // human-readable label on new "mixed" arrows — the substitution itself
  // (below) doesn't need it.
  function invertMatrix(M) {
    const n = M.length;
    const A = M.map(row => row.slice());
    const I = M.map((_, i) => M.map((_, j) => (i === j ? fone : fzero)));
    for (let col = 0; col < n; col++) {
      let piv = -1;
      for (let r = col; r < n; r++) if (!fisZero(A[r][col])) { piv = r; break; }
      if (piv === -1) throw new Error('singular matrix (internal error while diagonalizing)');
      if (piv !== col) { [A[piv], A[col]] = [A[col], A[piv]]; [I[piv], I[col]] = [I[col], I[piv]]; }
      const pv = A[col][col];
      for (let c = 0; c < n; c++) { A[col][c] = fdiv(A[col][c], pv); I[col][c] = fdiv(I[col][c], pv); }
      for (let r = 0; r < n; r++) {
        if (r === col) continue;
        const factor = A[r][col];
        if (fisZero(factor)) continue;
        for (let c = 0; c < n; c++) { A[r][c] = fsub(A[r][c], fmul(factor, A[col][c])); I[r][c] = fsub(I[r][c], fmul(factor, I[col][c])); }
      }
    }
    return I;
  }
  function comboLabel(combo) {
    const entries = [...combo.entries()].filter(([, c]) => !fisZero(c));
    if (entries.length === 0) return '0';
    let s = '';
    entries.forEach(([label, c], idx) => {
      const neg = c.n < 0;
      const absC = neg ? fneg(c) : c;
      const coeffStr = feq(absC, fone) ? '' : fToString(absC) + '·';
      s += (idx === 0 ? (neg ? '-' : '') : (neg ? ' - ' : ' + ')) + coeffStr + label;
    });
    return s;
  }

  // ---------- Arrow labels, computed on demand ----------
  // Naming a new arrow is display work, and it is expensive: a
  // diagonalization block's new arrows are defined by the columns of the
  // INVERSE of the change of basis (see diagonalizeQuadraticPart), and a
  // mutation's composite arrows carry names that grow with every round
  // ([[ab]c*] and worse). A block can create hundreds of arrows and a
  // mutation thousands, essentially none of which the user ever looks at —
  // so an arrow may instead be created with label: null plus a `labelDef`
  // recording how to name it, and labelOf() does the work the first time
  // (if ever) someone actually asks. Every read of an arrow's name, inside
  // this module and out, goes through labelOf.
  //
  // The definitions form a DAG over strictly older arrow objects (a
  // composite points at the two arrows it composes, a diagonalization
  // arrow at its block), so this always terminates; forcing a label caches
  // the string and drops the definition, releasing that chain.
  function labelOf(arrow) {
    if (!arrow) return '?';
    if (arrow.label != null) return arrow.label;
    const def = arrow.labelDef;
    let label;
    if (!def) label = '#' + arrow.id;
    else if (def.kind === 'compose') label = '[' + labelOf(def.left) + labelOf(def.right) + ']';
    else if (def.kind === 'reverse') label = labelOf(def.of) + "*";
    else label = blockLabels(def.block, def.side)[def.idx] ?? ('#' + arrow.id);
    arrow.label = label;
    arrow.labelDef = undefined;
    return label;
  }
  // All the new arrows on one side of a diagonalization block at once: the
  // matrix inverse is taken once per side, and only if some label on that
  // side is ever asked for.
  function blockLabels(block, side) {
    const key = side === 'A' ? 'labelsA' : 'labelsB';
    if (block[key]) return block[key];
    const ids = side === 'A' ? block.A : block.B;
    const combos = side === 'A' ? block.rowCombo : block.colCombo;
    const mat = combos.map(combo => ids.map(id => combo.get(id) || fzero));
    const inv = invertMatrix(mat);
    const names = ids.map(id => labelOf(block.oldArrows.get(id)));
    block[key] = combos.map((_, k) => comboLabel(new Map(names.map((nm, r) => [nm, inv[r][k]]))));
    return block[key];
  }

  // Diagonalize the quadratic (length-2) part of a potential so every arrow
  // appears in at most one 2-cycle term. When two candidate 2-cycles at a
  // vertex pair share an arrow, no relabeling of the *existing* arrows can
  // do that — it takes an actual change of basis among the parallel arrows.
  // For a fixed unordered vertex pair {i,j} with arrows A={i->j}, B={j->i},
  // the quadratic part restricted to this pair is a tensor
  // T = sum M[p][q]*(A[p],B[q]). Simultaneous row/column elimination on M
  // gives invertible matrices recorded as rowCombo/colCombo (each new
  // row/column expressed in the ORIGINAL A/B arrows) with rowCombo . M .
  // colCombo^T diagonal. Substituting each old arrow via
  //   A[r] |-> sum_k rowCombo[k][A[r]] * newA_k      (no matrix inverse needed)
  //   B[c] |-> sum_l colCombo[l][B[c]] * newB_l
  // exactly rewrites T as a clean diagonal sum — this is the standard proof
  // that any bilinear form has a normal form (a block of nonzero pivots,
  // zero elsewhere) under independent invertible changes of basis on each
  // side. Mutates `arrows` in place (via idBox, a {value} id counter).
  function diagonalizeQuadraticPart(arrows, current, maxLen, idBox, truncated) {
    // Index the quadratic part itself rather than every pair of parallel
    // arrows. Only an arrow that actually appears in some length-2 term can
    // be moved by the elimination below: an arrow whose row (or column) of
    // the pairing matrix is zero is never chosen as a pivot and never gets
    // a nonzero elimination factor, so it comes out of the process exactly
    // as it went in. Restricting the block to the pairing's support keeps
    // the cost tied to the rank of the pairing instead of to the number of
    // parallel arrows, which after a few mutations runs into the thousands
    // — and it is the same computation: a matrix that is the support block
    // plus zero rows and columns diagonalizes as the support block does.
    const byPair = new Map(); // "lo,hi" -> {lo, hi, rows:Set, cols:Set, entries:Map}
    for (const t of current.values()) {
      if (t.word.length !== 2) continue;
      const a0 = arrows.get(t.word[0]), a1 = arrows.get(t.word[1]);
      if (!a0 || !a1) continue;
      if (a0.source === a0.target || a1.source === a1.target) continue;
      if (a0.target !== a1.source || a1.target !== a0.source) continue; // not a 2-cycle
      const lo = Math.min(a0.source, a0.target), hi = Math.max(a0.source, a0.target);
      const key = lo + ',' + hi;
      let g = byPair.get(key);
      if (!g) { g = { lo, hi, rows: new Set(), cols: new Set(), entries: new Map() }; byPair.set(key, g); }
      // the arrow running lo->hi indexes the rows, the one running hi->lo the columns
      const row = a0.source === lo ? t.word[0] : t.word[1];
      const col = a0.source === lo ? t.word[1] : t.word[0];
      g.rows.add(row); g.cols.add(col);
      g.entries.set(row + ',' + col, t.coeff);
    }

    // Substitutions from every block are collected and applied to the
    // potential in ONE pass at the end. Blocks touch disjoint sets of
    // arrows, so this is the same rewrite as substituting block by block,
    // minus a full traversal of the potential per block.
    const substitutions = new Map();

    for (const g of byPair.values()) {
      const A = [...g.rows].sort((x, y) => x - y);
      const B = [...g.cols].sort((x, y) => x - y);
      if (A.length === 0 || B.length === 0) continue;

      const M = A.map(r => B.map(c => g.entries.get(r + ',' + c) || fzero));
      const rowNz = M.map(row => row.filter(x => !fisZero(x)).length);
      const colNz = B.map((_, q) => A.filter((_, p) => !fisZero(M[p][q])).length);
      const alreadyReduced = rowNz.every(c => c <= 1) && colNz.every(c => c <= 1) &&
        M.every(row => row.every(x => fisZero(x) || feq(x, fone)));
      if (alreadyReduced) continue; // already clean AND every surviving pairing is exactly 1

      let rowCombo = A.map(id => new Map([[id, fone]]));
      let colCombo = B.map(id => new Map([[id, fone]]));
      const usedRows = new Set(), usedCols = new Set();
      for (;;) {
        let pr = -1, pc = -1;
        findPivot:
        for (let r = 0; r < A.length; r++) {
          if (usedRows.has(r)) continue;
          for (let c = 0; c < B.length; c++) {
            if (usedCols.has(c)) continue;
            if (!fisZero(M[r][c])) { pr = r; pc = c; break findPivot; }
          }
        }
        if (pr === -1) break;
        usedRows.add(pr); usedCols.add(pc);
        const pivotVal = M[pr][pc];
        // Normalize the pivot to exactly 1 by rescaling the A-side row
        // only. Rows (A) and columns (B) come from independent arrow
        // families here — a bilinear pairing between two different bases,
        // not a quadratic form on one space — so no square root is
        // needed. This is what makes the result a *reduced* matrix (every
        // surviving entry 0 or 1), which the splitting below assumes.
        const invPivot = finv(pivotVal);
        for (let c = 0; c < B.length; c++) M[pr][c] = fmul(M[pr][c], invPivot);
        rowCombo[pr] = comboScale(rowCombo[pr], invPivot);
        for (let r = 0; r < A.length; r++) {
          if (r === pr) continue;
          const factor = M[r][pc]; // pivot is now 1, so this *is* the elimination factor
          if (fisZero(factor)) continue;
          for (let c = 0; c < B.length; c++) M[r][c] = fsub(M[r][c], fmul(factor, M[pr][c]));
          rowCombo[r] = comboSub(rowCombo[r], comboScale(rowCombo[pr], factor));
        }
        for (let c = 0; c < B.length; c++) {
          if (c === pc) continue;
          const factor = M[pr][c]; // pivot is now 1
          if (fisZero(factor)) continue;
          for (let r = 0; r < A.length; r++) M[r][c] = fsub(M[r][c], fmul(factor, M[r][pc]));
          colCombo[c] = comboSub(colCombo[c], comboScale(colCombo[pc], factor));
        }
      }

      // rowCombo/colCombo (used directly, no inverse) are exactly what the
      // substitution needs. A new arrow's own label — its definition in
      // terms of the OLD arrows — is a different quantity: column k of
      // Rinv=invert(rowCombo) for the A side, column l of Qinv=invert(
      // colCombo) for the B side. That inversion is display work only, so
      // the block records what it needs and labelOf() runs it on demand.
      //
      // A row the elimination never touched still carries its original
      // basis vector, and a fresh arrow for it would be the old arrow
      // under a new name: an identical copy, plus a substitution entry,
      // plus a label, for nothing. Those keep their existing arrow, so
      // only genuinely recombined arrows are replaced.
      const block = { A, B, rowCombo, colCombo, oldArrows: new Map() };
      for (const id of A) block.oldArrows.set(id, arrows.get(id));
      for (const id of B) block.oldArrows.set(id, arrows.get(id));
      const isIdentity = (combo, id) => combo.size === 1 && combo.has(id) && feq(combo.get(id), fone);
      const newA = rowCombo.map((combo, k) => {
        if (isIdentity(combo, A[k])) return A[k];
        const id = idBox.value++;
        arrows.set(id, { id, label: null, labelDef: { block, side: 'A', idx: k }, source: g.lo, target: g.hi });
        return id;
      });
      const newB = colCombo.map((combo, l) => {
        if (isIdentity(combo, B[l])) return B[l];
        const id = idBox.value++;
        arrows.set(id, { id, label: null, labelDef: { block, side: 'B', idx: l }, source: g.hi, target: g.lo });
        return id;
      });

      const addSubstitution = (oldId, combos, news) => {
        const parts = [];
        combos.forEach((combo, k) => { const c = combo.get(oldId); if (c && !fisZero(c)) parts.push({ path: [news[k]], coeff: c }); });
        // An arrow that maps to itself with coefficient 1 needs no rewriting.
        if (parts.length === 1 && parts[0].path[0] === oldId && feq(parts[0].coeff, fone)) return;
        substitutions.set(oldId, parts);
      };
      A.forEach((oldId) => addSubstitution(oldId, rowCombo, newA));
      B.forEach((oldId) => addSubstitution(oldId, colCombo, newB));

      // Only arrows that were actually replaced disappear; the ones reused
      // above are still in the quiver (and are their own new basis vector).
      const kept = new Set([...newA, ...newB]);
      for (const oldId of A) if (!kept.has(oldId)) arrows.delete(oldId);
      for (const oldId of B) if (!kept.has(oldId)) arrows.delete(oldId);
    }

    // Capped at maxLen, not above it: substituted paths are never shorter
    // than the arrow they replace, so a word already past the cap can only
    // grow and can never contribute to the final potential. Carrying such
    // words further was work spent on terms guaranteed to be discarded.
    if (substitutions.size > 0) current = applySubstitution(current, substitutions, maxLen, truncated);
    return current;
  }

  // `onProgress`, when given, is called with a short human-readable stage
  // name at each point below where the work changes character. It exists so
  // a caller running this off the main thread (see the worker in PART 6)
  // can say what it is doing during a mutation that takes minutes; when it
  // is absent this function behaves exactly as before.
  function mutateQP(quiver, potential, k, maxLen = 8, onProgress) {
    const report = onProgress || (() => {});
    const warnings = [];
    // Shared across the whole function: every length-cap-driven drop below
    // (potTruncate's own cap, diagonalizeQuadraticPart's substitution, each
    // round of the pair-splitting loop) sets this one flag, checked once
    // before returning, so a single warning covers all of them regardless
    // of which stage actually did the dropping.
    const truncated = { value: false };
    // One pass over the arrows sorts them into the three roles the mutation
    // needs and collects k's neighbours on each side, instead of four
    // separate traversals.
    const incoming = [], outgoing = [], untouched = [];
    const sourcesToK = new Set(), targetsFromK = new Set();
    for (const a of quiver.arrows.values()) {
      // DWZ mutation is defined for loop-free quivers, not merely loop-free
      // at k. A loop elsewhere passes through the premutation untouched, but
      // the reduction then meets a "2-cycle" built out of loops, which is
      // neither a genuine 2-cycle between two vertices nor something the
      // change of basis in diagonalizeQuadraticPart can move: depending on
      // the potential it either trips the overlap guard below (reported as
      // an internal error, which it is not) or quietly deletes the loops as
      // a trivial summand. Reject it here instead, where the offending
      // vertex can be named.
      if (a.source === a.target) {
        if (a.source === k) throw new Error('Cannot mutate at a vertex with a loop.');
        const lv = quiver.vertices.get(a.source);
        throw new Error(`Cannot mutate: the quiver has a loop at vertex ${lv ? lv.label : a.source}. QP mutation needs a loop-free quiver.`);
      }
      if (a.target === k) { incoming.push(a); sourcesToK.add(a.source); }
      else if (a.source === k) { outgoing.push(a); targetsFromK.add(a.target); }
      else untouched.push(a);
    }
    // DWZ mutation mu_k is only defined when k is not incident to a 2-cycle:
    // under the premutation such a pair collapses to a loop at the far
    // vertex, and the reduction step cannot get rid of it. A 2-cycle that
    // does NOT touch k is fine — the reduction below removes it, and this
    // agrees with mutating the reduced potential (mu-tilde respects
    // right-equivalence). Two arrows incident to a loop-free k form a
    // 2-cycle exactly when some vertex is both a source of an arrow into k
    // and the target of one out of k, so intersecting those two sets
    // decides it without comparing every pair.
    for (const j of targetsFromK) {
      if (sourcesToK.has(j)) {
        throw new Error('Cannot mutate at a vertex incident to a 2-cycle.');
      }
    }

    report('Composing arrows through the mutation vertex');
    let nextId = quiver.nextArrowId;
    const newArrows = new Map();
    const compositeOf = new Map();
    for (const beta of incoming) {
      for (const alpha of outgoing) {
        const id = nextId++;
        newArrows.set(id, { id, label: null, labelDef: { kind: 'compose', left: beta, right: alpha }, source: beta.source, target: alpha.target });
        compositeOf.set(beta.id + '_' + alpha.id, id);
      }
    }
    const reversedOf = new Map();
    for (const a of [...incoming, ...outgoing]) {
      const id = nextId++;
      newArrows.set(id, { id, label: null, labelDef: { kind: 'reverse', of: a }, source: a.target, target: a.source });
      reversedOf.set(a.id, id);
    }
    for (const a of untouched) newArrows.set(a.id, { ...a });

    const arrowById = quiver.arrows;
    function bracketWord(word) {
      const n = word.length;
      let r = 0, found = false;
      for (let i = 0; i < n; i++) {
        const prev = arrowById.get(word[(i - 1 + n) % n]);
        const cur = arrowById.get(word[i]);
        if (!(prev.target === k && cur.source === k)) { r = i; found = true; break; }
      }
      if (!found) { warnings.push('Encountered a term that only weaves through the mutation vertex; skipped.'); return null; }
      const rotated = word.slice(r).concat(word.slice(0, r));
      const result = [];
      let i = 0;
      while (i < rotated.length) {
        const a = rotated[i];
        if (i + 1 < rotated.length) {
          const b = rotated[i + 1];
          const aArrow = arrowById.get(a), bArrow = arrowById.get(b);
          if (aArrow.target === k && bArrow.source === k) {
            const cid = compositeOf.get(a + '_' + b);
            if (cid === undefined) { warnings.push('Internal: missing composite arrow.'); return null; }
            result.push(cid); i += 2; continue;
          }
        }
        result.push(a); i += 1;
      }
      if (result.length < 2) return null;
      return result;
    }

    report('Rewriting ' + potential.size + ' potential term' + (potential.size != 1 ? 's' : ''));
    const bracketed = new Map();
    for (const { word, coeff } of potential.values()) { const bw = bracketWord(word); if (bw) potAdd(bracketed, bw, coeff); }
    const deltaW = new Map();
    for (const beta of incoming) for (const alpha of outgoing) {
      const cid = compositeOf.get(beta.id + '_' + alpha.id);
      potAdd(deltaW, [cid, reversedOf.get(alpha.id), reversedOf.get(beta.id)], fone);
    }
    let tildeW = new Map();
    for (const t of bracketed.values()) potAdd(tildeW, t.word, t.coeff);
    for (const t of deltaW.values()) potAdd(tildeW, t.word, t.coeff);
    tildeW = potTruncate(tildeW, maxLen, truncated);

    let arrows = newArrows;
    const idBox = { value: nextId };
    report('Diagonalizing the quadratic part');
    let current = diagonalizeQuadraticPart(arrows, tildeW, maxLen, idBox, truncated);
    nextId = idBox.value;

    const removedIds = new Set();
    let stoppedOnConflict = false;
    const twoCycles = [...current.values()].filter(t => t.word.length === 2);
    if (twoCycles.length > 0) {
      const use = new Map();
      for (const t of twoCycles) for (const id of t.word) use.set(id, (use.get(id) || 0) + 1);
      const conflict = [...use.values()].some(c => c > 1);
      if (conflict) {
        // Shouldn't happen after diagonalizeQuadraticPart — kept as a guard.
        warnings.push('Internal: the quadratic part still has overlapping 2-cycles after diagonalization; stopping early as a precaution.');
        stoppedOnConflict = true;
      } else {
        // Splitting Theorem (DWZ Lemmas 4.7-4.8): current =
        // Sum_k(gamma_k delta_k) + R, a clean sum of 2-cycles each with
        // coefficient exactly 1 (diagonalizeQuadraticPart already put it
        // in this "reduced" form). Split R into gamma_k*u_k + v_k*delta_k
        // + S' for EVERY pair k at once via splitByPriority (a genuine
        // partition of R's terms, so no double counting even for a term
        // touching more than one pair). If every u_k, v_k is empty,
        // current is already an honest direct sum and every pair can be
        // dropped. Otherwise apply the SINGLE unitriangular automorphism
        // phi(gamma_k) = gamma_k - v_k, phi(delta_k) = delta_k - u_k for
        // every k simultaneously (fixing every other arrow) to the whole
        // potential — this is DWZ's Lemma 4.8 exactly, not a
        // pair-by-pair composition. Expanding
        // (gamma_k-v_k)(delta_k-u_k) = gamma_k delta_k - gamma_k u_k -
        // v_k delta_k + v_k u_k shows this cancels every pair's linear
        // coupling in one round and leaves a new error v_k*u_k of
        // strictly higher length (u_k, v_k both have length >= 2, since R
        // starts at length 3), so iterating drives every u_k, v_k to
        // exactly 0 -- Lemma 4.7's limiting process. Since this engine
        // truncates at maxLen anyway, "the limit" here just means
        // iterating until convergence or until a round no longer changes
        // anything visible at length <= maxLen; the round cap below is a
        // generous bound in case neither trips first.
        const pairs = twoCycles.map(t => ({ gamma: t.word[0], delta: t.word[1] }));
        for (const t of twoCycles) {
          if (!feq(t.coeff, fone)) warnings.push('Internal: a 2-cycle coefficient was not normalized to 1 before splitting.');
        }
        const priorityOf = new Map(), roleOf = new Map();
        pairs.forEach((p, idx) => {
          priorityOf.set(p.gamma, 2 * idx); roleOf.set(p.gamma, { kind: 'gamma', idx });
          priorityOf.set(p.delta, 2 * idx + 1); roleOf.set(p.delta, { kind: 'delta', idx });
        });
        const MAX_SPLIT_ROUNDS = maxLen + 6;
        let round = 0;
        for (;;) {
          report('Splitting ' + pairs.length + ' two-cycle pair' + (pairs.length != 1 ? 's' : '') + ', round ' + (round + 1));
          const { u, v } = splitByPriority(current, pairs, priorityOf, roleOf);
          const converged = pairs.every((_, idx) => u[idx].size === 0 && v[idx].size === 0);
          if (converged) break;
          if (round >= MAX_SPLIT_ROUNDS) { truncated.value = true; break; }
          const substitutions = new Map();
          pairs.forEach((p, idx) => {
            substitutions.set(p.gamma, [{ path: [p.gamma], coeff: fone }, ...[...v[idx].values()].map(({ path, coeff }) => ({ path, coeff: fneg(coeff) }))]);
            substitutions.set(p.delta, [{ path: [p.delta], coeff: fone }, ...[...u[idx].values()].map(({ path, coeff }) => ({ path, coeff: fneg(coeff) }))]);
          });
          const next = potTruncate(applySubstitution(current, substitutions, maxLen, truncated), maxLen, truncated);
          if (potEqual(next, current)) { current = next; break; } // no further change visible at this length cap
          current = next;
          round++;
        }
        for (const { gamma, delta } of pairs) {
          current.delete(keyOf(canonicalWord([gamma, delta])));
          arrows.delete(gamma); arrows.delete(delta);
          removedIds.add(gamma); removedIds.add(delta);
        }
      }
    }
    report('Finishing up');
    current = potTruncate(current, maxLen, truncated);

    let strayFound = false;
    for (const [key, t] of [...current]) { if (t.word.some(id => removedIds.has(id))) { current.delete(key); strayFound = true; } }
    // One check covers every length-cap drop in this function: potTruncate
    // (tildeW's own cap and the final one above), diagonalizeQuadraticPart's
    // substitution, and each round of the pair-splitting loop's own
    // substitution — none of those leave a literal gamma/delta id behind
    // for `strayFound` to catch on its own (the arrow is fully replaced by
    // unrelated ids, or the drop happens before any arrow is even deleted),
    // so `truncated` is the only reliable signal for most of them. It's
    // also set directly if the splitting loop hits its round cap without
    // converging.
    if (truncated.value || strayFound) warnings.push(`At least one cycle of length > ${maxLen} (= max cycle length in the settings)  in the potential was deleted.`);

    // Check the QUIVER's actual arrow structure, not just the potential:
    // diagonalizeQuadraticPart can leave a rank-deficient block with an
    // arrow i->j and an arrow j->i both surviving, pairing coefficient
    // forced to exactly zero — a real 2-cycle even though no length-2
    // potential term names it. That's the genuine degeneracy witness;
    // scanning `current` for length-2 terms alone would miss it.
    // Counted from the multiplicities of each directed vertex pair — the
    // number of 2-cycles between i and j is (arrows i->j) * (arrows j->i),
    // summed over unordered pairs. Same number as comparing every pair of
    // arrows, without the quadratic scan (which, on a quiver that has just
    // grown to tens of thousands of arrows, dominated the whole mutation).
    const dirCount = new Map();
    for (const a of arrows.values()) {
      if (a.source === a.target) continue;
      const key = a.source + ',' + a.target;
      dirCount.set(key, (dirCount.get(key) || 0) + 1);
    }
    let residual2Cycles = 0;
    for (const [key, n] of dirCount) {
      const comma = key.indexOf(',');
      const src = +key.slice(0, comma), tgt = +key.slice(comma + 1);
      if (src >= tgt) continue; // count each unordered pair once
      const back = dirCount.get(tgt + ',' + src);
      if (back) residual2Cycles += n * back;
    }
    if (residual2Cycles > 0) warnings.push(`Resulting quiver still has ${residual2Cycles} two-cycle` + (residual2Cycles != 1 ? 's' : '') + ' (a pair of arrows i↔j survives with no way to cancel it) — the potential is degenerate.');

    const newQuiver = { vertices: quiver.vertices, arrows, nextVertexId: quiver.nextVertexId, nextArrowId: nextId };
    // Dedupe as a safety net — every message above is pushed from exactly
    // one place, but keeping this cheap dedupe means a future added warning
    // path can't accidentally double up a banner.
    return { quiver: newQuiver, potential: current, warnings: [...new Set(warnings)] };
  }

  return {
    F, fadd, fsub, fmul, fdiv, fneg, finv, fisZero, feq, fone, fzero, fToString, fParse,
    RationalField, makePrimeField, getField, setField, isPrime,
    makeQuiver, addVertex, addArrow, defaultArrowLabel,
    canonicalWord, potAdd, potTruncate, potEqual, splitByPriority, applySubstitution, mutateQP,
    labelOf,
  };
}
const QP = QPEngine();

/* ======================================================================
   PART 2 — application state, presets, serialization
   ====================================================================== */
function freshState() {
  return {
    quiver: QP.makeQuiver(),
    potential: new Map(),
    maxLen: 8,
    mode: 'select',
    selection: null,          // {type:'vertex'|'arrow', id}
    arrowDraftSource: null,   // vertex id while placing an arrow
    termDraft: [],            // array of arrow ids
    dragVertex: null,
    highlightedTermKey: null, // canonical key of a potential term clicked in the side list, or null
  };
}
// Clearing the highlight is cheap and idempotent, so it's called liberally
// from every place that changes the quiver/potential/mode/selection —
// simpler and more robust than trying to enumerate exactly which actions
// would leave a stale arrow-id reference.
function clearTermHighlight() {
  if (state.highlightedTermKey === null) return; // no-op: avoid redundant list re-renders
  state.highlightedTermKey = null;
  renderTerms(); // keep the side-list's highlighted row in sync; canvas is handled by each caller's own render()/renderAll()
}
let state = freshState();
let history = [];
let historyIndex = -1;
let mouse = { x: 0, y: 0 };
// Purely cosmetic UI state (not part of the math, so not in `state`/history):
// which member is currently shown by each bundled-arrow's ‹ › steppers.
// Keyed by directed "source>target" id pair, value = index into that
// bundle's arrows (sorted by id). Read through bundleActiveIndex(), which
// clamps/wraps, so stale entries after edits never go out of range.
let bundleUI = new Map();
// The little name box overlaid on each bundle, keyed the same way. A real
// DOM element (not canvas text) so a name longer than the box can be
// scrolled into view instead of being cut down to whatever fits. Reused
// across renders (not recreated) so an in-progress scroll isn't reset by
// the render() it can trigger — see updateBundleNameOverlay().
let bundleNameEls = new Map();
// The custom scrollbar thumb dragged to scroll that name box, keyed the
// same way — {track, thumb} elements. Not the browser's native scrollbar:
// on a box this small, a native custom-styled (::-webkit-scrollbar) thumb
// had no usable drag range (it rendered spanning the full track). This one
// is drawn and sized by hand, with an enforced minimum width.
let bundleThumbEls = new Map();

// A potential term's word is only meaningful if it is an actual closed,
// composable path in the quiver: consecutive arrows must join up
// (target of one = source of the next), all the way around the cycle.
// The interactive term-builder enforces this as you click, but presets
// and imported JSON bypass that UI, so they're checked here too.
function isValidCyclicWord(quiver, word) {
  if (!word || word.length < 2) return false;
  for (let i = 0; i < word.length; i++) {
    const cur = quiver.arrows.get(word[i]);
    const next = quiver.arrows.get(word[(i + 1) % word.length]);
    if (!cur || !next || cur.target !== next.source) return false;
  }
  return true;
}

// An arrow created by a mutation may still carry `labelDef` instead of a
// name (see labelOf) — a pointer into a chain of older arrow objects, and
// for a diagonalization arrow into that block's whole coefficient matrix.
// structuredClone follows all of it, so a lazy label drags its entire
// naming chain into every history entry. Settle them first, so what gets
// cloned is a plain string either way:
//   * up to LABEL_FORCE_LIMIT arrows, resolve the real names (measured at
//     ~54 ms for 1400 arrows, so this stays comfortably interactive);
//   * past it, give the name up. Composed names at that size ([[ab]c*] and
//     worse, already 34 characters after four mutations) are unreadable,
//     the bundle view collapses those arrows anyway, and '#id' is what
//     labelOf falls back to for an unnamed arrow regardless.
// This runs on the live quiver, not on the copy, which is the point: it
// also releases the chain the live state was holding.
// Two separate ways a name gets too expensive to keep, and the second is
// the one that actually bites. A composite's name is '[' + left + right +
// ']', so a name DOUBLES in length with every mutation that touches it —
// measured on the 15-arrow X_7 preset, the longest arrow name runs 78
// characters after 10 mutations, 1,902 after 30, and 1,744,546 after 70,
// at which point one history entry costs 14 MB. Arrow COUNT never notices:
// the quiver still has 15 arrows. So cap the name itself, not just the
// number of them. Capping also cuts the growth off at the root, since the
// next generation composes names from the short ones this pass leaves.
const LABEL_FORCE_LIMIT = 5000;   // arrows: past this, don't even build names
const LABEL_MAX_CHARS = 2000;     // per name: past this, nobody can read it anyway
let labelCapNoticed = false;
function settleArrowLabels() {
  const build = state.quiver.arrows.size <= LABEL_FORCE_LIMIT;
  let capped = 0;
  for (const a of state.quiver.arrows.values()) {
    if (a.label == null) {
      if (!build) { a.label = '#' + a.id; a.labelDef = undefined; continue; }
      QP.labelOf(a);
    }
    // '#id' is exactly what labelOf falls back to for an arrow with no name,
    // so a capped arrow is indistinguishable from a never-named one — better
    // than a truncated prefix, which two different arrows could share.
    if (a.label.length > LABEL_MAX_CHARS) { a.label = '#' + a.id; capped++; }
  }
  if (capped && !labelCapNoticed) {
    labelCapNoticed = true;
    addMessage('Some arrow names had grown too long to keep and are now shown as ids. Use Relabel for clean names — the quiver and potential are unaffected.', 'warn');
  }
}

// History is capped by retained SIZE, not just by entry count: 60 entries is
// nothing for a 12-arrow quiver and fatal for a 100,000-arrow one, which a
// few mutations of a mutation-infinite quiver reaches (3 -> 12 -> 24 -> 108
// -> 1401 -> 114384). The newest entry is never evicted: a single snapshot
// larger than the whole budget still has to be reachable.
//
// snapWeight estimates BYTES rather than counting abstract units, because
// the two things a snapshot holds are on wildly different scales: measured
// against structuredClone, roughly 100 bytes per structural item (arrow,
// vertex, arrow of a potential word) and 2 per UTF-16 character of an arrow
// name. Leaving names out of the count was the whole reason an earlier
// version of this cap could be sailed straight past — see settleArrowLabels.
// The estimate runs high (it read ~24 MB for a snapshot that measured 14),
// which is the safe direction for a budget.
const HISTORY_MAX_ENTRIES = 60;
const HISTORY_BUDGET_BYTES = 32e6;
function snapWeight(snap) {
  let bytes = 100 * (snap.quiver.arrows.size + snap.quiver.vertices.size);
  for (const t of snap.potential.values()) bytes += 100 * t.word.length;
  for (const a of snap.quiver.arrows.values()) bytes += 2 * (a.label ? a.label.length : 0);
  return bytes;
}

function snapshot(label) {
  settleArrowLabels();
  const snap = structuredClone({ quiver: state.quiver, potential: state.potential, maxLen: state.maxLen });
  history = history.slice(0, historyIndex + 1);
  history.push({ label, snap, weight: snapWeight(snap) });
  let total = 0;
  for (const h of history) total += h.weight;
  while (history.length > 1 && (history.length > HISTORY_MAX_ENTRIES || total > HISTORY_BUDGET_BYTES)) {
    total -= history[0].weight;
    history.shift();
  }
  historyIndex = history.length - 1;
  renderHistory();
}
function restoreSnapshot(i) {
  if (i < 0 || i >= history.length) return;
  const { snap } = history[i];
  const cloned = structuredClone(snap);
  state.quiver = cloned.quiver;
  state.potential = cloned.potential;
  state.maxLen = cloned.maxLen;
  historyIndex = i;
  state.selection = null; state.termDraft = []; state.arrowDraftSource = null; state.highlightedTermKey = null;
  syncMaxLenUI();
  renderAll();
}
function pushHistoryIfChanged(label) { snapshot(label); }

function loadPreset(name) {
  const Q = QP.makeQuiver();
  let W = new Map();
  const one = QP.fone;
  if (name === '3cycle') {
    const v1 = QP.addVertex(Q, '1', 260, 140), v2 = QP.addVertex(Q, '2', 460, 260), v3 = QP.addVertex(Q, '3', 260, 380);
    const a = QP.addArrow(Q, v1, v2, 'a'), b = QP.addArrow(Q, v2, v3, 'b'), c = QP.addArrow(Q, v3, v1, 'c');
    QP.potAdd(W, [a, b, c], one);
  } else if (name === 'x7') {
    const v0 = QP.addVertex(Q, '0', 420, 300);
    const verts = {};
    const ang = { 1: -100, 2: -55, 3: 20, 4: 65, 5: 145, 6: 190 };
    for (let i = 1; i <= 6; i++) {
      const r = 210, a = (ang[i]) * Math.PI / 180;
      verts[i] = QP.addVertex(Q, String(i), 420 + r * Math.cos(a), 300 + r * Math.sin(a));
    }
    const arms = [[1, 2], [3, 4], [5, 6]];
    const alpha = [], beta = [], gamma = [], delta = [];
    for (let i = 0; i < 3; i++) {
      const [p, q] = arms[i];
      alpha[i] = QP.addArrow(Q, v0, verts[p], `a${i + 1}`);
      beta[i] = QP.addArrow(Q, verts[p], verts[q], `b${i + 1}`);
      delta[i] = QP.addArrow(Q, verts[p], verts[q], `d${i + 1}`);
      gamma[i] = QP.addArrow(Q, verts[q], v0, `g${i + 1}`);
    }
    for (let i = 0; i < 3; i++) QP.potAdd(W, [alpha[i], beta[i], gamma[i]], one);
    const D = i => [alpha[i], delta[i], gamma[i]];
    QP.potAdd(W, [...D(0), ...D(1)], one);
    QP.potAdd(W, [...D(1), ...D(2)], one);
    QP.potAdd(W, [...D(2), ...D(0)], one);
  } else if (name === 'pentagon') {
    // Triangulated pentagon quiver (fan triangulation from vertex 1): boundary
    // 1->2->3->4->5->1 plus diagonals 3->1 and 1->4, giving 3 triangles whose
    // boundaries are each an honest closed 3-cycle: (1,2,3), (3,4,1), (1,4,5).
    // Note a3 runs 4->3 (not 3->4) so triangle (3,4,1)'s cycle closes up.
    const pos = [[420, 140], [560, 260], [510, 430], [330, 430], [280, 260]];
    const vs = pos.map((p, i) => QP.addVertex(Q, String(i + 1), p[0], p[1]));
    const e = (i, j, label) => QP.addArrow(Q, vs[i], vs[j], label);
    const a1 = e(0, 1, 'a1'); // 1->2
    const a2 = e(1, 2, 'a2'); // 2->3
    const a3 = e(3, 2, 'a3'); // 4->3
    const a4 = e(3, 4, 'a4'); // 4->5
    const a5 = e(4, 0, 'a5'); // 5->1
    const d1 = e(2, 0, 'd1'); // 3->1  (diagonal)
    const d2 = e(0, 3, 'd2'); // 1->4  (diagonal)
    QP.potAdd(W, [a1, a2, d1], one);  // triangle 1-2-3
    QP.potAdd(W, [d1, d2, a3], one);  // triangle 3-1-4 (3->1->4->3)
    QP.potAdd(W, [d2, a4, a5], one);  // triangle 1-4-5
  } else if (name === 'markov') {
    // Markov quiver: 3 vertices, 2 arrows between every pair, all oriented
    // the same way around the cycle 1->2->3->1. Labardini-Fragoso's
    // potential (from the once-punctured torus) is the sum of the "inside"
    // triangle (a1 b1 c1), the "outside" triangle (a2 b2 c2), and the
    // length-6 cycle that alternates between the two arrows on each edge
    // (a1 b2 c1 a2 b1 c2).
    const r = 160, cx = 420, cy = 300;
    const v1 = QP.addVertex(Q, '1', cx, cy - r);
    const v2 = QP.addVertex(Q, '2', cx + r * Math.cos(Math.PI / 6), cy + r * Math.sin(Math.PI / 6));
    const v3 = QP.addVertex(Q, '3', cx - r * Math.cos(Math.PI / 6), cy + r * Math.sin(Math.PI / 6));
    const a1 = QP.addArrow(Q, v1, v2, 'a1'), a2 = QP.addArrow(Q, v1, v2, 'a2');
    const b1 = QP.addArrow(Q, v2, v3, 'b1'), b2 = QP.addArrow(Q, v2, v3, 'b2');
    const c1 = QP.addArrow(Q, v3, v1, 'c1'), c2 = QP.addArrow(Q, v3, v1, 'c2');
    QP.potAdd(W, [a1, b1, c1], one);              // inside triangle
    QP.potAdd(W, [a2, b2, c2], one);               // outside triangle
    QP.potAdd(W, [a1, b2, c1, a2, b1, c2], one);   // alternating hexagon
  }
  const badTerms = [...W.values()].filter(t => !isValidCyclicWord(Q, t.word));
  for (const t of badTerms) W.delete(keyForTerm(t));
  state.quiver = Q; state.potential = W; state.selection = null; state.termDraft = []; state.arrowDraftSource = null; state.highlightedTermKey = null;
  history = []; historyIndex = -1;
  snapshot('Preset: ' + (name || 'empty'));
  if (badTerms.length) addMessage(`Discarded ${badTerms.length} malformed potential term` + (badTerms.length != 1 ? 's' : '') + ' from this preset (internal bug — please report).', 'warn');
  // The Markov triangle's lowest vertices would otherwise sit under the
  // bottom-left hint box, so pull it up above the canvas's vertical middle.
  fitView(name === 'markov' ? 0.4 : 0.5);
  renderAll();
}

function serializeState() {
  const Q = state.quiver;
  const field = QP.getField();
  return JSON.stringify({
    field: field.kind === 'Fp' ? { kind: 'Fp', p: field.p.toString() } : { kind: 'Q' },
    vertices: [...Q.vertices.values()].map(v => ({ id: v.id, label: v.label, x: v.x, y: v.y })),
    arrows: [...Q.arrows.values()].map(a => ({ id: a.id, label: QP.labelOf(a), source: a.source, target: a.target })),
    nextVertexId: Q.nextVertexId, nextArrowId: Q.nextArrowId,
    potential: [...state.potential.values()].map(t => ({ word: t.word, coeff: [t.coeff.n.toString(), t.coeff.d.toString()] })),
    maxLen: state.maxLen,
  }, null, 1);
}
function deserializeState(text) {
  const obj = JSON.parse(text);
  if (!obj || typeof obj !== 'object') throw new Error('not a QP file');
  if (!Array.isArray(obj.vertices) || !Array.isArray(obj.arrows) || !Array.isArray(obj.potential)) {
    throw new Error('missing vertices, arrows or potential');
  }
  // Switch the active field to match the file *before* reconstructing
  // coefficients, so QP.F(...) below interprets the stored {n,d} pairs
  // correctly. Files from before this feature existed have no `field` key
  // — treat those as Q, which is what they always were.
  let fieldWarning = '';
  try {
    if (obj.field && obj.field.kind === 'Fp') QP.setField(QP.makePrimeField(BigInt(obj.field.p)));
    else QP.setField(QP.RationalField);
  } catch (e) {
    fieldWarning = `Could not use the imported field (${e.message}); kept the current one.`;
  }
  // Nothing in the file is taken on trust: it is ordinary untrusted input,
  // and every field below is either validated or rebuilt from scratch.
  const Q = QP.makeQuiver();
  const isId = (n) => Number.isSafeInteger(n) && n >= 0;
  let badEntries = 0;
  for (const v of obj.vertices) {
    if (!v || !isId(v.id) || Q.vertices.has(v.id)) { badEntries++; continue; }
    Q.vertices.set(v.id, {
      id: v.id,
      label: String(v.label ?? v.id),          // labelOf/escapeHtml assume a string
      x: Number.isFinite(v.x) ? v.x : 0,
      y: Number.isFinite(v.y) ? v.y : 0,
    });
  }
  for (const a of obj.arrows) {
    // An arrow whose endpoints are not in the file is not a quiver arrow;
    // keeping it would break every source/target lookup downstream.
    if (!a || !isId(a.id) || Q.arrows.has(a.id) ||
        !Q.vertices.has(a.source) || !Q.vertices.has(a.target)) { badEntries++; continue; }
    Q.arrows.set(a.id, { id: a.id, label: String(a.label ?? ('#' + a.id)), source: a.source, target: a.target });
  }
  // Never trust the file's own counters: a stale or hostile value hands the
  // next added vertex/arrow an id that is already in use, which silently
  // rewrites an existing one instead of creating anything.
  let maxV = -1; for (const id of Q.vertices.keys()) if (id > maxV) maxV = id;
  let maxA = -1; for (const id of Q.arrows.keys()) if (id > maxA) maxA = id;
  Q.nextVertexId = Math.max(isId(obj.nextVertexId) ? obj.nextVertexId : 0, maxV + 1);
  Q.nextArrowId = Math.max(isId(obj.nextArrowId) ? obj.nextArrowId : 0, maxA + 1);
  const W = new Map();
  let skipped = 0;
  for (const t of obj.potential) {
    if (!t || !isValidCyclicWord(Q, t.word)) { skipped++; continue; }
    try { QP.potAdd(W, t.word, QP.F(BigInt(t.coeff[0]), BigInt(t.coeff[1]))); }
    catch (e) { skipped++; }
  }
  state.quiver = Q; state.potential = W;
  // Clamped to the slider's own range, so state.maxLen can never drift from
  // the value the Settings panel shows.
  state.maxLen = Math.min(16, Math.max(4, Math.round(Number(obj.maxLen)) || 8));
  state.selection = null; state.termDraft = []; state.arrowDraftSource = null; state.highlightedTermKey = null;
  history = []; historyIndex = -1;
  snapshot('Imported');
  syncMaxLenUI();
  syncFieldUI();
  fitView();
  renderAll();
  if (badEntries) addMessage(`Skipped ${badEntries} vertex/arrow entr${badEntries != 1 ? 'ies' : 'y'} with a bad id or missing endpoints.`, 'warn');
  if (skipped) addMessage(`Skipped ${skipped} potential term` + (skipped != 1 ? 's' : '') + ` that weren't closed, composable cycles, or valid in this field.`, 'warn');
  if (fieldWarning) addMessage(fieldWarning, 'warn');
}

/* ======================================================================
   PART 3 — canvas rendering
   ====================================================================== */
const canvas = document.getElementById('cv');
const ctx = canvas.getContext('2d');
const wrap = document.getElementById('canvasWrap');
let view = { panX: 0, panY: 0 }; // simple, content is placed in absolute coords already

function cssVar(name) { return getComputedStyle(document.documentElement).getPropertyValue(name).trim(); }

function resizeCanvas() {
  const rect = wrap.getBoundingClientRect();
  const dpr = window.devicePixelRatio || 1;
  canvas.width = Math.max(1, Math.round(rect.width * dpr));
  canvas.height = Math.max(1, Math.round(rect.height * dpr));
  canvas.style.width = rect.width + 'px';
  canvas.style.height = rect.height + 'px';
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  render();
}
new ResizeObserver(resizeCanvas).observe(wrap);
window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', () => render());

const VR = 22; // vertex radius

function arrowGroupKey(a) { return a.source < a.target ? a.source + '_' + a.target : a.target + '_' + a.source; }
function directedKey(a) { return a.source + '>' + a.target; }

// More than this many arrows sharing a direction between the same two
// vertices are drawn as a single bundled curve (Keller's applet writes just
// a count on the arrow; here the bundle also keeps every name reachable —
// step between members with the chevrons, scroll a long one into view with
// the name strip — see bundleBoxLayout/drawBundleBox).
const ARROW_BUNDLE_THRESHOLD = 5;

// Returns { geo, bundleGeo }:
//  - geo: Map<arrowId, {curve}> — arrows drawn as their own curve.
//  - bundleGeo: Map<directedKey, {curve, arrows}> — groups of more than
//    ARROW_BUNDLE_THRESHOLD same-direction arrows, collapsed into one curve.
// Both singles and bundles sharing an unordered vertex pair are fanned out
// together (same curve-offset scheme as before bundling existed) so they
// never overlap on screen.
// Both the arrow geometry and the structural issues below depend only on
// the ARROW SET — not on where the vertices sit, not on labels, not on the
// potential. This is the shared constant-time test for "that set changed":
// mutation, undo/redo, import, presets and Clear all replace the quiver
// object wholesale, while adding or deleting arrows in place necessarily
// moves arrows.size or nextArrowId. (Nothing in this app changes an
// existing arrow's endpoints. If that ever changes, that code must clear
// both caches below by hand — the stamp will not notice on its own.)
function quiverCacheHit(cache) {
  const Q = state.quiver;
  return !!cache && cache.quiver === Q && cache.size === Q.arrows.size && cache.nextArrowId === Q.nextArrowId;
}
function quiverCacheStamp(value) {
  const Q = state.quiver;
  return { quiver: Q, size: Q.arrows.size, nextArrowId: Q.nextArrowId, value };
}
let geometryCache = null;   // { quiver, size, nextArrowId, value: {geo, bundleGeo} }
let structCache = null;     // { quiver, size, nextArrowId, value: {loopIds, twoCycleIds, flaggedVertices} }

// Curve offsets for every arrow, and the bundles that several parallel
// arrows collapse into. Cached because render(), both hit tests and the
// dblclick handler each ask for it — a chevron click alone rebuilt it three
// times, and at 40,000 arrows that is 30 ms a rebuild. Vertex positions are
// deliberately not part of the stamp: this returns curve offsets, and where
// a curve actually lands is arrowPoints' job, so dragging a vertex needs no
// recomputation here.
function computeArrowGeometry() {
  if (quiverCacheHit(geometryCache)) return geometryCache.value;
  const value = computeArrowGeometryUncached();
  geometryCache = quiverCacheStamp(value);
  return value;
}
function computeArrowGeometryUncached() {
  const directed = new Map();
  for (const a of state.quiver.arrows.values()) {
    if (a.source === a.target) continue;
    const dk = directedKey(a);
    if (!directed.has(dk)) directed.set(dk, []);
    directed.get(dk).push(a);
  }
  const itemsByPair = new Map();
  for (const [dk, arrows] of directed) {
    arrows.sort((x, y) => x.id - y.id);
    const pairKey = arrowGroupKey(arrows[0]);
    if (!itemsByPair.has(pairKey)) itemsByPair.set(pairKey, []);
    if (arrows.length > ARROW_BUNDLE_THRESHOLD) itemsByPair.get(pairKey).push({ bundle: dk, arrows });
    else for (const a of arrows) itemsByPair.get(pairKey).push({ single: a });
  }
  const geo = new Map(), bundleGeo = new Map();
  for (const items of itemsByPair.values()) {
    const n = items.length;
    items.forEach((item, idx) => {
      const curve = idx - (n - 1) / 2;
      if (item.single) geo.set(item.single.id, { curve });
      else bundleGeo.set(item.bundle, { curve, arrows: item.arrows });
    });
  }
  return { geo, bundleGeo };
}
// Reads bundleUI (clamped/wrapped to the bundle's current member count) so
// stale indices left over after arrows are added/removed/mutated never
// throw — they just settle back into range.
function bundleActiveIndex(dKey, n) {
  const v = bundleUI.get(dKey) ?? 0;
  return ((v % n) + n) % n;
}
function stepBundle(dKey, dir, n) {
  bundleUI.set(dKey, bundleActiveIndex(dKey, n) + dir);
}
// Fixed small size regardless of label length (per the request: a compact
// box, not one that grows with the name). Two chevrons step between
// different member arrows; the name strip between them is a real DOM
// element (see updateBundleNameOverlay) with `overflow-x: auto` so a name
// longer than that strip can be scrolled into view rather than cut down to
// whatever fits.
function bundleBoxLayout(arrows, curve) {
  const p = arrowPoints(arrows[0], curve);
  if (!p) return null;
  const mid = quadPoint(p, 0.5);
  const w = 74, h = 34, chevW = 13;
  const x = mid.x - w / 2, y = mid.y - h / 2;
  const chevY = y + 20; // vertical center of the chevron/name row
  const textW = w - chevW * 2 - 4;
  const name = { left: x + chevW + 2, top: y + 13, width: textW, height: 14 };
  // A dedicated scrollbar-like track+thumb (see updateBundleNameOverlay),
  // not the browser's native one — a custom-styled native scrollbar on a
  // box this small rendered a thumb with no usable drag range. Own thumb
  // means an enforced minimum size that's actually grabbable.
  const thumbTrack = { left: name.left, top: y + 28, width: textW, height: 5 };
  return { mid, x, y, w, h, chevW, chevY, name, thumbTrack };
}
// Hit-test the bundle label boxes. Returns null if (x,y) hits no box;
// otherwise {dKey, dir, n} where dir is -1/+1 on a chevron (step to the
// previous/next member) or 0 elsewhere in the box (the count line, or —
// when a click reaches the canvas at all — the name strip; see
// updateBundleNameOverlay, whose DOM element normally catches those first
// and forwards them here with the same coordinates).
function hitBundleNav(x, y) {
  const { bundleGeo } = computeArrowGeometry();
  // Boxes belonging to different vertex pairs can still overlap in a dense
  // drawing, so pick the one whose centre is nearest the click and, on a
  // tie, the one drawn last — that is the box on top, and the box on top is
  // the one the user is aiming at. Returning the first match instead meant
  // clicks landed on whatever was underneath.
  let best = null, bestD = Infinity;
  for (const [dKey, bundle] of bundleGeo) {
    const box = bundleBoxLayout(bundle.arrows, bundle.curve);
    if (!box) continue;
    if (x < box.x || x > box.x + box.w || y < box.y || y > box.y + box.h) continue;
    const d = Math.hypot(x - (box.x + box.w / 2), y - (box.y + box.h / 2));
    if (d <= bestD) { bestD = d; best = { dKey, box, n: bundle.arrows.length }; }
  }
  if (!best) return null;
  const { dKey, box, n } = best;
  if (x < box.x + box.chevW) return { dKey, dir: -1, n };
  if (x > box.x + box.w - box.chevW) return { dKey, dir: 1, n };
  return { dKey, dir: 0, n };
}

function arrowPoints(a, curveOffset) {
  const Q = state.quiver;
  const s = Q.vertices.get(a.source), t = Q.vertices.get(a.target);
  if (!s || !t) return null;
  const dx = t.x - s.x, dy = t.y - s.y;
  const len = Math.hypot(dx, dy) || 1;
  const ux = dx / len, uy = dy / len;
  // The perpendicular is taken from the pair's canonical orientation (low
  // vertex id to high), NOT from this arrow's own direction. Deriving it
  // from source->target flips it for the reverse arrow, which cancels
  // against that arrow's opposite curve offset: an i->j bundle and a j->i
  // bundle were handed offsets -0.5 and +0.5 and landed on exactly the
  // same arc, one label box hiding the other completely.
  let px = -uy, py = ux; // perpendicular
  if (a.source > a.target) { px = -px; py = -py; }
  const bend = curveOffset * 30;
  const mx = (s.x + t.x) / 2 + px * bend, my = (s.y + t.y) / 2 + py * bend;
  // start/end at circle edge, aimed toward the control point for a smooth join
  const sAngle = Math.atan2(my - s.y, mx - s.x);
  const tAngle = Math.atan2(my - t.y, mx - t.x);
  const sx = s.x + Math.cos(sAngle) * VR, sy = s.y + Math.sin(sAngle) * VR;
  const tx = t.x + Math.cos(tAngle) * VR, ty = t.y + Math.sin(tAngle) * VR;
  return { sx, sy, mx, my, tx, ty };
}
function quadPoint(p, t) {
  const x = (1 - t) * (1 - t) * p.sx + 2 * (1 - t) * t * p.mx + t * t * p.tx;
  const y = (1 - t) * (1 - t) * p.sy + 2 * (1 - t) * t * p.my + t * t * p.ty;
  return { x, y };
}

function drawArrowHead(x, y, angle, color) {
  const size = 8.5;
  ctx.save();
  ctx.translate(x, y); ctx.rotate(angle);
  ctx.beginPath();
  ctx.moveTo(0, 0);
  ctx.lineTo(-size * 1.7, size * 0.62);
  ctx.lineTo(-size * 1.7, -size * 0.62);
  ctx.closePath();
  ctx.fillStyle = color;
  ctx.fill();
  ctx.restore();
}

// A bundle's ‹ prev / next › stepper: dir -1 points left, +1 points right.
function drawChevron(x, y, dir, color) {
  const s = 4;
  ctx.beginPath();
  ctx.moveTo(x + dir * s, y);
  ctx.lineTo(x - dir * s, y - s);
  ctx.lineTo(x - dir * s, y + s);
  ctx.closePath();
  ctx.fillStyle = color;
  ctx.fill();
}

// Draws one bundle's collapsed curve, arrowhead, fixed-size label box
// (count + chevrons), and badge number. The name strip between the
// chevrons is left blank on the canvas — updateBundleNameOverlay() lays a
// real DOM element over it, scrollable via `overflow-x: auto`, so a name
// longer than the strip can be scrolled into view instead of chopped down
// to whatever fits. `color` reflects selection/highlight state exactly
// like a normal arrow's.
function drawBundleBox(arrows, curve, color, sans, bg, border, badgeIdx, link) {
  const box = bundleBoxLayout(arrows, curve);
  if (!box) return;

  ctx.fillStyle = bg;
  ctx.fillRect(box.x, box.y, box.w, box.h);
  ctx.strokeStyle = border; ctx.lineWidth = 1;
  ctx.strokeRect(box.x + 0.5, box.y + 0.5, box.w - 1, box.h - 1);

  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.font = '700 9.5px ' + sans;
  ctx.fillStyle = color;
  ctx.fillText(arrows.length + ' arrows', box.mid.x, box.y + 8);

  drawChevron(box.x + box.chevW / 2 + 2, box.chevY, -1, color);
  drawChevron(box.x + box.w - box.chevW / 2 - 2, box.chevY, 1, color);

  if (badgeIdx >= 0) {
    ctx.font = '700 10px ' + sans;
    ctx.fillStyle = link;
    ctx.fillText(String(badgeIdx + 1), box.mid.x, box.y - 6);
  }
}

// Forwards a DOM event's coordinates to the canvas as a synthetic mouse
// event, so the name overlay (which physically catches clicks meant for
// the box beneath it) can still drive normal select/term/erase/rename
// behavior — the exact same effect as if the click had landed on bare
// canvas over the bundle's box.
function forwardToCanvas(type, e) {
  canvas.dispatchEvent(new MouseEvent(type, { clientX: e.clientX, clientY: e.clientY, bubbles: true }));
}

// Keeps exactly one real, horizontally-scrollable DOM element per current
// bundle, showing the active member's full (untruncated) name and
// positioned over the name strip between its chevrons. Elements are reused
// across renders (not recreated) so a scroll in progress isn't reset by
// the very render() that repositioning can trigger; the element's own
// scrollLeft only resets when the *shown arrow* changes (stepped via the
// chevrons), not on every unrelated re-render.
function updateBundleNameOverlay(dKey, arrows, curve, color, seen) {
  const box = bundleBoxLayout(arrows, curve);
  if (!box) return;
  seen.add(dKey);
  let el = bundleNameEls.get(dKey);
  if (!el) {
    el = document.createElement('div');
    el.className = 'qp-bundle-name';
    el.title = 'Long name — drag the bar below to see the rest';
    // No native scrollbar here (overflow: hidden) — scrolling is driven
    // entirely by the custom thumb below, via el.scrollLeft. A click on
    // the text still needs forwarding, since the div physically sits on
    // top of the canvas and would otherwise swallow it.
    el.addEventListener('mousedown', (e) => forwardToCanvas('mousedown', e));
    el.addEventListener('click', (e) => forwardToCanvas('click', e));
    el.addEventListener('dblclick', (e) => forwardToCanvas('dblclick', e));
    wrap.appendChild(el);
    bundleNameEls.set(dKey, el);
  }
  // Rewrite the text when the NAME changes, not only when the bundle steps
  // to a different member: Relabel (and renaming a single arrow) gives the
  // same member a new name, which this box used to keep showing under its
  // old one. Writing textContent replaces the text node and so drops any
  // in-progress scroll, which is why it stays guarded — an unchanged name
  // must not be rewritten on every render.
  const idx = bundleActiveIndex(dKey, arrows.length);
  const label = QP.labelOf(arrows[idx]);
  if (el.dataset.idx !== String(idx) || el.textContent !== label) {
    el.dataset.idx = String(idx);
    el.textContent = label;
    el.scrollLeft = 0;
    bundleScroll.set(dKey, 0);
  }
  el.style.left = box.name.left + 'px';
  el.style.top = box.name.top + 'px';
  el.style.width = box.name.width + 'px';
  el.style.height = box.name.height + 'px';
  el.style.color = color;

  updateBundleThumb(dKey, el, box, color, label);
}
function pruneBundleNameOverlays(seen) {
  for (const [dKey, el] of bundleNameEls) if (!seen.has(dKey)) { el.remove(); bundleNameEls.delete(dKey); }
  for (const [dKey, t] of bundleThumbEls) if (!seen.has(dKey)) { t.track.remove(); bundleThumbEls.delete(dKey); }
}

// A dedicated, appropriately-sized scrollbar for `nameEl` (see
// bundleBoxLayout's `thumbTrack` for why not the native one). Hidden
// entirely when the name already fits — nothing to scroll, nothing to
// drag. Dragging only ever starts on the thumb itself, never the name
// text, so it can never race with clicking the name to select/erase/
// term/rename it.
const BUNDLE_THUMB_MIN_WIDTH = 12;
// The name strip's scroll offset, kept here rather than read back from the
// element: nameEl.scrollLeft / scrollWidth / clientWidth are all
// layout-dependent reads, and render() writes to those same elements just
// before, so each read forced a synchronous layout of the entire page. With
// a term list of tens of thousands of rows that cost hundreds of
// milliseconds — per frame of a drag, and per chevron click.
let bundleScroll = new Map(); // directedKey -> current scrollLeft, in px
// Width of a bundle label as the strip will render it, measured on the
// canvas in the same font the stylesheet gives .qp-bundle-name (10px,
// --qp-mono). A couple of sub-pixels either way only affects the size of a
// scroll thumb, and it costs no layout at all.
let bundleLabelFont = null;
function measureBundleLabel(text) {
  if (!bundleLabelFont) bundleLabelFont = '10px ' + cssVar('--qp-mono');
  const prev = ctx.font;
  ctx.font = bundleLabelFont;
  const w = ctx.measureText(text).width;
  ctx.font = prev;
  return w;
}
function updateBundleThumb(dKey, nameEl, box, color, label) {
  const trackW = box.thumbTrack.width;
  const maxScroll = Math.max(0, measureBundleLabel(label) - box.name.width);
  let t = bundleThumbEls.get(dKey);
  if (maxScroll <= 0) {
    if (t) t.track.style.display = 'none';
    bundleScroll.set(dKey, 0);
    nameEl.scrollLeft = 0;
    return;
  }
  if (!t) {
    const track = document.createElement('div');
    track.className = 'qp-bundle-thumb-track';
    const thumb = document.createElement('div');
    thumb.className = 'qp-bundle-thumb';
    // Both gestures below work from the numbers this function already
    // computed (t.trackW, t.thumbW, t.left, t.maxScroll) instead of
    // measuring the DOM, so dragging the thumb forces no layout either.
    const scrollTo = (left) => {
      const range = t.trackW - t.thumbW;
      const clamped = Math.min(range, Math.max(0, left));
      t.left = clamped;
      thumb.style.left = clamped + 'px';
      const s = range > 0 ? t.maxScroll * (clamped / range) : 0;
      bundleScroll.set(dKey, s);
      nameEl.scrollLeft = s;
    };
    thumb.addEventListener('mousedown', (e) => {
      e.preventDefault();
      const startX = e.clientX, startLeft = t.left;
      const onMove = (me) => scrollTo(startLeft + (me.clientX - startX));
      const onUp = () => { window.removeEventListener('mousemove', onMove); window.removeEventListener('mouseup', onUp); thumb.classList.remove('qp-dragging'); };
      thumb.classList.add('qp-dragging');
      window.addEventListener('mousemove', onMove);
      window.addEventListener('mouseup', onUp);
    });
    track.addEventListener('mousedown', (e) => {
      if (e.target === thumb) return; // handled by the thumb's own listener above
      // Clicking the bare track jumps the thumb there directly (a quick
      // "page" scroll), same as clicking a normal scrollbar's track.
      scrollTo(canvasCoords(e).x - t.trackLeft - t.thumbW / 2);
    });
    track.appendChild(thumb);
    wrap.appendChild(track);
    t = { track, thumb, trackW, thumbW: BUNDLE_THUMB_MIN_WIDTH, left: 0, maxScroll, trackLeft: box.thumbTrack.left };
    bundleThumbEls.set(dKey, t);
  }
  t.track.style.display = '';
  t.track.style.left = box.thumbTrack.left + 'px';
  t.track.style.top = box.thumbTrack.top + 'px';
  t.track.style.width = trackW + 'px';
  t.track.style.height = box.thumbTrack.height + 'px';
  const thumbW = Math.max(BUNDLE_THUMB_MIN_WIDTH, trackW * (box.name.width / (maxScroll + box.name.width)));
  t.thumb.style.width = thumbW + 'px';
  const range = trackW - thumbW;
  const scroll = Math.min(bundleScroll.get(dKey) || 0, maxScroll);
  const left = range > 0 ? range * (scroll / maxScroll) : 0;
  t.thumb.style.left = left + 'px';
  Object.assign(t, { trackW, thumbW, left, maxScroll, trackLeft: box.thumbTrack.left });
}

function render() {
  const rect = wrap.getBoundingClientRect();
  ctx.clearRect(0, 0, rect.width, rect.height);
  const fg = cssVar('--qp-fg'), link = cssVar('--qp-link'), linkSoft = cssVar('--qp-link-soft'),
        border = cssVar('--qp-border'), bg = cssVar('--qp-bg'), mutedBg = cssVar('--qp-muted-bg'),
        danger = cssVar('--qp-danger'), mono = cssVar('--qp-mono'), sans = cssVar('--qp-sans');

  const { geo, bundleGeo } = computeArrowGeometry();
  const termSet = new Set(state.termDraft);
  const { loopIds, twoCycleIds, flaggedVertices } = structuralIssues();
  const highlightedWord = state.highlightedTermKey ? (state.potential.get(state.highlightedTermKey)?.word ?? null) : null;

  // arrows
  for (const a of state.quiver.arrows.values()) {
    if (a.source !== a.target && !geo.has(a.id)) continue; // folded into a bundle, drawn below instead
    const isSel = state.selection && state.selection.type === 'arrow' && state.selection.id === a.id;
    const inTermIdx = state.termDraft.indexOf(a.id);
    const highlightIdx = highlightedWord ? highlightedWord.indexOf(a.id) : -1;
    const badgeIdx = inTermIdx >= 0 ? inTermIdx : highlightIdx;
    const flagged = loopIds.has(a.id) || twoCycleIds.has(a.id);
    let color = flagged ? danger : fg, width = flagged ? 2.2 : 1.4;
    if (isSel || badgeIdx >= 0) { color = link; width = 2.2; }

    if (a.source === a.target) {
      const v = state.quiver.vertices.get(a.source);
      if (!v) continue;
      ctx.beginPath();
      ctx.ellipse(v.x, v.y - VR - 16, 16, 16, 0, 0.35, Math.PI * 2 - 0.35);
      ctx.strokeStyle = color; ctx.lineWidth = width; ctx.stroke();
      drawArrowHead(v.x - 10, v.y - VR - 3, Math.PI * 0.72, color);
      continue;
    }
    const c = geo.get(a.id);
    const p = arrowPoints(a, c.curve);
    if (!p) continue;
    ctx.beginPath();
    ctx.moveTo(p.sx, p.sy);
    ctx.quadraticCurveTo(p.mx, p.my, p.tx, p.ty);
    ctx.strokeStyle = color; ctx.lineWidth = width; ctx.stroke();
    const endTan = { x: p.tx - quadPoint(p, 0.92).x, y: p.ty - quadPoint(p, 0.92).y };
    drawArrowHead(p.tx, p.ty, Math.atan2(endTan.y, endTan.x), color);

    // label
    const mid = quadPoint(p, 0.5);
    ctx.font = '11.5px ' + mono;
    const label = QP.labelOf(a);
    const tw = ctx.measureText(label).width;
    ctx.fillStyle = bg;
    ctx.fillRect(mid.x - tw / 2 - 3, mid.y - 8, tw + 6, 15);
    ctx.fillStyle = color;
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText(label, mid.x, mid.y);

    if (badgeIdx >= 0) {
      ctx.font = '700 10px ' + sans;
      ctx.fillStyle = link;
      ctx.fillText(String(badgeIdx + 1), mid.x, mid.y - 14);
    }
  }

  // bundled arrows: more than ARROW_BUNDLE_THRESHOLD same-direction arrows
  // between two vertices, collapsed into one thicker curve with a small
  // fixed-size label box (count + ‹ › chevrons; the name strip between
  // them is a scrollable DOM overlay — see updateBundleNameOverlay below).
  const seenBundleNames = new Set();
  for (const bundle of bundleGeo.values()) {
    const arrows = bundle.arrows;
    const dKey = directedKey(arrows[0]);
    const isSelMember = state.selection && state.selection.type === 'arrow' && arrows.some(m => m.id === state.selection.id);
    let badgeIdx = -1;
    for (const m of arrows) {
      const i1 = state.termDraft.indexOf(m.id);
      if (i1 >= 0) badgeIdx = i1;
      const i2 = highlightedWord ? highlightedWord.indexOf(m.id) : -1;
      if (i2 >= 0) badgeIdx = i2;
    }
    const flagged = arrows.some(m => twoCycleIds.has(m.id));
    let color = flagged ? danger : fg, width = 2.0; // a bit thicker than a normal single arrow
    if (isSelMember || badgeIdx >= 0) { color = link; width = 2.6; }
    else if (flagged) { width = 2.6; }

    const p = arrowPoints(arrows[0], bundle.curve);
    if (!p) continue;
    ctx.beginPath();
    ctx.moveTo(p.sx, p.sy);
    ctx.quadraticCurveTo(p.mx, p.my, p.tx, p.ty);
    ctx.strokeStyle = color; ctx.lineWidth = width; ctx.stroke();
    const endTan = { x: p.tx - quadPoint(p, 0.92).x, y: p.ty - quadPoint(p, 0.92).y };
    drawArrowHead(p.tx, p.ty, Math.atan2(endTan.y, endTan.x), color);

    drawBundleBox(arrows, bundle.curve, color, sans, bg, border, badgeIdx, link);
    updateBundleNameOverlay(dKey, arrows, bundle.curve, color, seenBundleNames);
  }
  pruneBundleNameOverlays(seenBundleNames);

  // pending arrow ghost
  if (state.mode === 'arrow' && state.arrowDraftSource != null) {
    const s = state.quiver.vertices.get(state.arrowDraftSource);
    if (s) {
      ctx.save();
      ctx.setLineDash([4, 4]);
      ctx.strokeStyle = link; ctx.lineWidth = 1.2;
      ctx.beginPath(); ctx.moveTo(s.x, s.y); ctx.lineTo(mouse.x, mouse.y); ctx.stroke();
      ctx.restore();
    }
  }

  // vertices
  for (const v of state.quiver.vertices.values()) {
    const isSel = state.selection && state.selection.type === 'vertex' && state.selection.id === v.id;
    const isArrowSrc = state.mode === 'arrow' && state.arrowDraftSource === v.id;
    const hasIssue = flaggedVertices.has(v.id);
    ctx.beginPath();
    ctx.arc(v.x, v.y, VR, 0, Math.PI * 2);
    ctx.fillStyle = isSel || isArrowSrc ? linkSoft : bg;
    ctx.fill();
    ctx.lineWidth = isSel || isArrowSrc ? 2.2 : (hasIssue ? 2.2 : 1.4);
    ctx.strokeStyle = isSel || isArrowSrc ? link : (hasIssue ? danger : fg);
    ctx.stroke();
    ctx.fillStyle = fg;
    ctx.font = '700 13px ' + sans;
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText(v.label, v.x, v.y);
  }
}

// vCenterFrac lets a preset pull its vertical center above the canvas
// midpoint (e.g. 0.42 instead of 0.5) — used by presets whose lowest
// vertices would otherwise sit under the bottom-left hint box.
function fitView(vCenterFrac = 0.5) {
  const vs = [...state.quiver.vertices.values()];
  if (!vs.length) return;
  const rect = wrap.getBoundingClientRect();
  const xs = vs.map(v => v.x), ys = vs.map(v => v.y);
  const minX = Math.min(...xs), maxX = Math.max(...xs), minY = Math.min(...ys), maxY = Math.max(...ys);
  const cw = maxX - minX, ch = maxY - minY;
  const targetCx = rect.width / 2, targetCy = rect.height * vCenterFrac;
  const curCx = (minX + maxX) / 2, curCy = (minY + maxY) / 2;
  const dx = targetCx - curCx, dy = targetCy - curCy;
  if (rect.width > 0 && (Math.abs(dx) > 1 || Math.abs(dy) > 1)) {
    for (const v of state.quiver.vertices.values()) { v.x += dx; v.y += dy; }
  }
}

/* ======================================================================
   PART 4 — interaction
   ====================================================================== */
function hitVertex(x, y) {
  for (const v of state.quiver.vertices.values()) if (Math.hypot(v.x - x, v.y - y) <= VR + 3) return v;
  return null;
}
// Clicking anywhere along a bundle's curve (not just its label box) picks
// out its currently-displayed member — every mode (select, term, erase,
// rename) that goes through hitArrow keeps working unchanged, just acting
// on whichever arrow the bundle's chevrons are currently showing.
function hitArrow(x, y) {
  const { geo, bundleGeo } = computeArrowGeometry();
  let best = null, bestD = 10;
  for (const a of state.quiver.arrows.values()) {
    if (a.source !== a.target) continue;
    const v = state.quiver.vertices.get(a.source);
    if (!v) continue;
    const d = Math.abs(Math.hypot(x - v.x, y - (v.y - VR - 16)) - 16);
    if (d < bestD) { bestD = d; best = a; }
  }
  for (const [id, c] of geo) {
    const a = state.quiver.arrows.get(id);
    if (!a) continue;
    const p = arrowPoints(a, c.curve);
    if (!p) continue;
    for (let t = 0; t <= 1; t += 0.04) {
      const pt = quadPoint(p, t);
      const d = Math.hypot(pt.x - x, pt.y - y);
      if (d < bestD) { bestD = d; best = a; }
    }
  }
  for (const [dKey, bundle] of bundleGeo) {
    const active = bundle.arrows[bundleActiveIndex(dKey, bundle.arrows.length)];
    // The count/chevron row can sit a bit off the curve itself (that's the
    // point of a box vs. a mid-curve label), so any click landing in the
    // box counts as a direct hit. Chevron clicks are intercepted earlier
    // (see hitBundleNav) before this ever runs; name-strip clicks land on
    // the DOM overlay and are forwarded here with the same coordinates —
    // see updateBundleNameOverlay/forwardToCanvas.
    const box = bundleBoxLayout(bundle.arrows, bundle.curve);
    if (box && x >= box.x && x <= box.x + box.w && y >= box.y && y <= box.y + box.h) { bestD = 0; best = active; continue; }
    const p = arrowPoints(bundle.arrows[0], bundle.curve);
    if (!p) continue;
    for (let t = 0; t <= 1; t += 0.04) {
      const pt = quadPoint(p, t);
      const d = Math.hypot(pt.x - x, pt.y - y);
      if (d < bestD) { bestD = d; best = active; }
    }
  }
  return best;
}
function canvasCoords(evt) {
  const rect = canvas.getBoundingClientRect();
  return { x: evt.clientX - rect.left, y: evt.clientY - rect.top };
}

function setMode(m) {
  state.mode = m;
  state.arrowDraftSource = null;
  // Select mode never edits the quiver/potential — moving vertices around
  // while a cycle is highlighted (e.g. to get a clearer look at it) is
  // exactly what it's for, so switching there (or back) leaves it lit.
  if (m !== 'select') clearTermHighlight();
  document.querySelectorAll('#modeSeg button').forEach(b => b.classList.toggle('qp-active', b.dataset.mode === m));
  updateHint();
  render();
}
function updateHint() {
  const hint = document.getElementById('hint');
  const map = {
    select: 'Drag vertices to move them. Click an arrow or vertex to inspect it. Double-click to rename.',
    vertex: 'Click empty canvas to place a new vertex.',
    arrow: state.arrowDraftSource == null ? 'Click a source vertex.' : 'Now click the target vertex (click empty space or press Esc to cancel).',
    term: 'Click arrows in order to build a cyclic potential term. It must close up. Click the last one again to undo a step.',
    mutate: 'Click a vertex to mutate the quiver with potential there.',
    erase: 'Click a vertex or arrow to delete it.',
  };
  hint.innerHTML = map[state.mode] || '';
}

function addMessage(text, kind) {
  const banner = document.getElementById('banner');
  const div = document.createElement('div');
  div.className = 'qp-msg' + (kind === 'warn' ? ' qp-warn' : '');
  // Built as DOM rather than written as innerHTML: `text` routinely carries
  // arrow and vertex labels, which come from imported JSON and so are
  // untrusted. textContent cannot be talked into parsing markup, whereas an
  // escape call here is one forgetful edit away from being dropped again.
  const body = document.createElement('span');
  body.textContent = text;
  const x = document.createElement('span');
  x.className = 'qp-x';
  x.textContent = '✕';
  x.onclick = () => div.remove();
  div.append(body, x);
  banner.appendChild(div);
  if (!kind || kind === 'ok') setTimeout(() => div.remove(), 6000);
}

/* ---- in-page modal: window.confirm/prompt are typically blocked inside
   a sandboxed artifact iframe (no allow-modals), so Clear and rename used
   to silently do nothing. This replaces both with real DOM UI. ---- */
function showModal({ title, message, showInput, defaultValue, okLabel, onOk }) {
  const overlay = document.getElementById('modalOverlay');
  const input = document.getElementById('modalInput');
  const okBtn = document.getElementById('modalOk');
  const cancelBtn = document.getElementById('modalCancel');
  document.getElementById('modalTitle').textContent = title;
  const msgEl = document.getElementById('modalMsg');
  msgEl.textContent = message || '';
  msgEl.style.display = message ? '' : 'none';
  input.style.display = showInput ? '' : 'none';
  if (showInput) input.value = defaultValue ?? '';
  okBtn.textContent = okLabel || 'OK';
  overlay.classList.add('qp-open');
  if (showInput) requestAnimationFrame(() => { input.focus(); input.select(); });

  function close() {
    overlay.classList.remove('qp-open');
    okBtn.removeEventListener('click', doOk);
    cancelBtn.removeEventListener('click', doCancel);
    input.removeEventListener('keydown', onKey);
    overlay.removeEventListener('mousedown', onOverlayClick);
  }
  function doOk() {
    const val = showInput ? input.value.trim() : undefined;
    if (showInput && val === '') { close(); return; }
    close();
    onOk(val);
  }
  function doCancel() { close(); }
  function onKey(e) { if (e.key === 'Enter') doOk(); else if (e.key === 'Escape') doCancel(); }
  function onOverlayClick(e) { if (e.target === overlay) doCancel(); }
  okBtn.addEventListener('click', doOk);
  cancelBtn.addEventListener('click', doCancel);
  input.addEventListener('keydown', onKey);
  overlay.addEventListener('mousedown', onOverlayClick);
}
function showConfirm(title, message, okLabel, onYes) {
  showModal({ title, message, showInput: false, okLabel, onOk: () => onYes() });
}
function showRename(title, defaultValue, onRenamed) {
  showModal({ title, showInput: true, defaultValue, okLabel: 'Rename', onOk: (val) => onRenamed(val) });
}

// Programmatic <a download> clicks are blocked in some sandboxed contexts
// (same family of restriction as window.confirm/prompt), so a plain
// "click to download" button can silently do nothing. This shows the JSON
// directly, selected and ready to copy, with Copy/Download as two
// independent ways to get it out — at least one of which always works.
function showExportModal(jsonText) {
  const overlay = document.getElementById('modalOverlay');
  const box = overlay.querySelector('.qp-modal-box');
  const input = document.getElementById('modalInput');
  const textarea = document.getElementById('modalTextarea');
  const msgEl = document.getElementById('modalMsg');
  const okBtn = document.getElementById('modalOk');
  const cancelBtn = document.getElementById('modalCancel');
  const extra = document.getElementById('modalExtraActions');
  const copyBtn = document.getElementById('modalCopy');
  const downloadBtn = document.getElementById('modalDownload');

  document.getElementById('modalTitle').textContent = 'Export';
  msgEl.textContent = 'Your quiver and potential as JSON — copy it, download it, or select all (Ctrl/Cmd+A) and copy manually.';
  msgEl.style.display = '';
  input.style.display = 'none';
  textarea.style.display = '';
  textarea.value = jsonText;
  box.classList.add('qp-wide');
  extra.style.display = 'flex';
  okBtn.style.display = 'none';
  cancelBtn.textContent = 'Close';
  overlay.classList.add('qp-open');
  requestAnimationFrame(() => { textarea.focus(); textarea.select(); });

  function close() {
    overlay.classList.remove('qp-open');
    box.classList.remove('qp-wide');
    textarea.style.display = 'none';
    extra.style.display = 'none';
    okBtn.style.display = '';
    cancelBtn.textContent = 'Cancel';
    cancelBtn.removeEventListener('click', close);
    copyBtn.removeEventListener('click', doCopy);
    downloadBtn.removeEventListener('click', doDownload);
    textarea.removeEventListener('keydown', onKey);
    overlay.removeEventListener('mousedown', onOverlayClick);
  }
  async function doCopy() {
    textarea.select();
    let ok = false;
    try { await navigator.clipboard.writeText(jsonText); ok = true; }
    catch (e) { try { ok = document.execCommand('copy'); } catch (e2) { ok = false; } }
    addMessage(ok ? 'Copied to clipboard.' : 'Could not copy automatically — select the text (Ctrl/Cmd+A) and copy it by hand (Ctrl/Cmd+C).', ok ? 'ok' : 'warn');
  }
  function doDownload() {
    try {
      const blob = new Blob([jsonText], { type: 'application/json' });
      const url = URL.createObjectURL(blob);
      const el = document.createElement('a'); el.href = url; el.download = 'quiver-with-potential.json';
      document.body.appendChild(el); el.click(); el.remove();
      URL.revokeObjectURL(url);
    } catch (e) {
      addMessage('Download isn’t available in this environment — use Copy to clipboard instead.', 'warn');
    }
  }
  function onKey(e) { if (e.key === 'Escape') close(); }
  function onOverlayClick(e) { if (e.target === overlay) close(); }
  cancelBtn.addEventListener('click', close);
  copyBtn.addEventListener('click', doCopy);
  downloadBtn.addEventListener('click', doDownload);
  textarea.addEventListener('keydown', onKey);
  overlay.addEventListener('mousedown', onOverlayClick);
}

/* ---- loops / 2-cycles: flagged live, not just right after a mutation ---- */
// Bucketed by directed vertex pair rather than compared arrow-by-arrow: an
// arrow i->j lies in a 2-cycle exactly when at least one arrow j->i exists,
// so a single pass that groups the arrows answers it for all of them at
// once. The old pairwise scan was quadratic, which at tens of thousands of
// arrows (a few mutations is enough) cost seconds — and render() runs this
// on every frame of a vertex drag.
//
// `flaggedVertices` is computed here too, for the same reason: the vertex
// loop in render() used to rescan every arrow once per vertex to decide
// whether to draw the vertex in red.
function getStructuralIssues(quiver) {
  const loopIds = new Set(), twoCycleIds = new Set(), flaggedVertices = new Set();
  const byDir = new Map(); // "source,target" -> [arrow ids]
  for (const a of quiver.arrows.values()) {
    if (a.source === a.target) { loopIds.add(a.id); flaggedVertices.add(a.source); continue; }
    const key = a.source + ',' + a.target;
    let bucket = byDir.get(key);
    if (!bucket) { bucket = []; byDir.set(key, bucket); }
    bucket.push(a.id);
  }
  for (const [key, ids] of byDir) {
    const comma = key.indexOf(',');
    const src = key.slice(0, comma), tgt = key.slice(comma + 1);
    if (!byDir.has(tgt + ',' + src)) continue;
    for (const id of ids) twoCycleIds.add(id);
    flaggedVertices.add(+src); flaggedVertices.add(+tgt);
  }
  return { loopIds, twoCycleIds, flaggedVertices };
}

// Which arrows are flagged depends only on each arrow's (source, target), so
// the answer survives everything else the app does: moving a vertex,
// renaming anything, adding or removing a potential term, switching the
// coefficient field. Recomputed only when the arrow set changes, on the
// shared stamp defined above.
function structuralIssues() {
  if (quiverCacheHit(structCache)) return structCache.value;
  const issues = getStructuralIssues(state.quiver);
  structCache = quiverCacheStamp(issues);
  // The banner is DOM work — an innerHTML write and a fresh handler — so it
  // is refreshed here, on an actual change, rather than once per frame.
  updateStructuralWarning(issues);
  return issues;
}

let structWarnDismissedKey = null;
function updateStructuralWarning(issues) {
  const { loopIds, twoCycleIds } = issues;
  const pairs = twoCycleIds.size / 2;
  const el = document.getElementById('structWarn');
  const row = document.getElementById('statIssueRow');
  const count = document.getElementById('statIssues');
  if (loopIds.size === 0 && pairs === 0) {
    structWarnDismissedKey = null;
    if (el) el.style.display = 'none';
    if (row) row.style.display = 'none';
    return;
  }
  const parts = [];
  if (loopIds.size) parts.push(loopIds.size + ' loop' + (loopIds.size != 1 ? 's' : ''));
  if (pairs) parts.push(pairs + ' two-cycle' + (pairs != 1 ? 's' : ''));
  // The two conditions are not the same rule and must not be stated as one:
  // a loop anywhere blocks mutation outright (mutateQP rejects it), while a
  // 2-cycle only matters at the vertex being mutated — one away from it is
  // reduced away by the splitting step.
  const rules = [];
  if (loopIds.size) rules.push('needs a loop-free quiver');
  if (pairs) rules.push('cannot be run at a vertex incident to a two-cycle');
  const why = 'QP mutation ' + rules.join(', and ') + '.';
  // Key identifies exactly which arrows are currently flagged, so dismissing
  // this set re-shows the banner as soon as the set of issues changes
  // (e.g. a new loop/2-cycle appears) rather than staying hidden forever.
  const key = [...loopIds].sort((a, b) => a - b).join(',') + '|' + [...twoCycleIds].sort((a, b) => a - b).join(',');
  if (el) {
    if (structWarnDismissedKey === key) {
      el.style.display = 'none';
    } else {
      el.style.display = 'flex';
      el.textContent = '';
      const body = document.createElement('span');
      body.textContent = parts.join(' and ') + ' present, shown in red — ' + why;
      const x = document.createElement('span');
      x.className = 'qp-x';
      x.textContent = '✕';
      x.onclick = () => { structWarnDismissedKey = key; el.style.display = 'none'; };
      el.append(body, x);
    }
  }
  if (row) row.style.display = '';
  if (count) count.textContent = parts.join(', ');
}

canvas.addEventListener('mousemove', (e) => {
  const p = canvasCoords(e); mouse = p;
  if (state.dragVertex != null) {
    const v = state.quiver.vertices.get(state.dragVertex);
    if (v) { v.x = p.x; v.y = p.y; render(); }
    return;
  }
  if (state.mode === 'arrow' && state.arrowDraftSource != null) render();
});

canvas.addEventListener('mousedown', (e) => {
  const p = canvasCoords(e);
  // Chevrons step to a different member on 'click' below; ignore them here
  // so mousedown doesn't also drag/select/deselect underneath the control.
  const nav = hitBundleNav(p.x, p.y);
  if (nav && nav.dir !== 0) return;
  if (state.mode !== 'select') clearTermHighlight();
  if (state.mode === 'select') {
    const v = hitVertex(p.x, p.y);
    if (v) { state.dragVertex = v.id; state.selection = { type: 'vertex', id: v.id }; renderInspector(); render(); return; }
    const a = hitArrow(p.x, p.y);
    if (a) { state.selection = { type: 'arrow', id: a.id }; renderInspector(); render(); return; }
    state.selection = null; renderInspector(); render();
  }
});
window.addEventListener('mouseup', () => {
  if (state.dragVertex != null) { state.dragVertex = null; snapshot('Move vertex'); }
});

canvas.addEventListener('click', (e) => {
  const p = canvasCoords(e);
  const nav = hitBundleNav(p.x, p.y);
  if (nav && nav.dir !== 0) {
    stepBundle(nav.dKey, nav.dir, nav.n);
    // The selection is pinned to one arrow id, so a bundle whose displayed
    // member is the selected one has to carry the selection along as it
    // steps. Without this the inspector keeps describing whichever member
    // was on display when it was picked — and since a click on the bundle
    // selects the member on display, only the first arrow of a bundle could
    // ever be inspected, renamed or deleted.
    const bundle = computeArrowGeometry().bundleGeo.get(nav.dKey);
    if (bundle && state.selection && state.selection.type === 'arrow' &&
        bundle.arrows.some(m => m.id === state.selection.id)) {
      const shown = bundle.arrows[bundleActiveIndex(nav.dKey, bundle.arrows.length)];
      state.selection = { type: 'arrow', id: shown.id };
      renderInspector();
    }
    render();
    return;
  }
  if (state.mode !== 'select') clearTermHighlight();
  if (state.mode === 'vertex') {
    const v = hitVertex(p.x, p.y);
    if (v) return;
    const id = QP.addVertex(state.quiver, String(state.quiver.nextVertexId + 1), p.x, p.y);
    snapshot('Add vertex ' + state.quiver.vertices.get(id).label);
    render(); renderStats();
  } else if (state.mode === 'arrow') {
    const v = hitVertex(p.x, p.y);
    if (state.arrowDraftSource == null) {
      if (v) { state.arrowDraftSource = v.id; updateHint(); render(); }
    } else {
      if (v) {
        if (v.id === state.arrowDraftSource) { addMessage('Loops are not supported (QP mutation requires loop-free quivers).', 'warn'); }
        else {
          const id = QP.addArrow(state.quiver, state.arrowDraftSource, v.id);
          snapshot('Add arrow ' + QP.labelOf(state.quiver.arrows.get(id)));
        }
      }
      state.arrowDraftSource = null; updateHint(); render(); renderStats();
    }
  } else if (state.mode === 'term') {
    const a = hitArrow(p.x, p.y);
    if (!a) return;
    const draft = state.termDraft;
    if (draft.length && draft[draft.length - 1] === a.id) { draft.pop(); render(); renderDraftBar(); return; }
    if (draft.length === 0) { draft.push(a.id); }
    else {
      const last = state.quiver.arrows.get(draft[draft.length - 1]);
      if (last.target !== a.source) { addMessage('That arrow does not continue the chain: need an arrow starting at vertex ' + (state.quiver.vertices.get(last.target)?.label ?? last.target) + '.', 'warn'); return; }
      draft.push(a.id);
    }
    render(); renderDraftBar();
  } else if (state.mode === 'mutate') {
    const v = hitVertex(p.x, p.y);
    if (!v) return;
    doMutate(v.id);
  } else if (state.mode === 'erase') {
    const v = hitVertex(p.x, p.y);
    if (v) {
      const label = v.label;
      for (const [id, a] of [...state.quiver.arrows]) if (a.source === v.id || a.target === v.id) state.quiver.arrows.delete(id);
      state.quiver.vertices.delete(v.id);
      pruneTermsReferencingMissingArrows();
      snapshot('Delete vertex ' + label);
      state.selection = null; renderInspector(); render(); renderStats(); renderTerms();
      return;
    }
    const a = hitArrow(p.x, p.y);
    if (a) {
      state.quiver.arrows.delete(a.id);
      pruneTermsReferencingMissingArrows();
      snapshot('Delete arrow ' + QP.labelOf(a));
      state.selection = null; renderInspector(); render(); renderStats(); renderTerms();
    }
  }
});

canvas.addEventListener('dblclick', (e) => {
  const p = canvasCoords(e);
  if (hitBundleNav(p.x, p.y)) return; // a stray dblclick on the box/chevrons/name shouldn't open a rename dialog
  clearTermHighlight();
  const v = hitVertex(p.x, p.y);
  if (v) { showRename('Rename vertex', v.label, (nv) => { v.label = nv; snapshot('Rename vertex'); render(); renderInspector(); }); return; }
  const a = hitArrow(p.x, p.y);
  if (a) { showRename('Rename arrow', QP.labelOf(a), (na) => { a.label = na; a.labelDef = undefined; snapshot('Rename arrow'); render(); renderInspector(); renderTerms(); }); }
});

window.addEventListener('keydown', (e) => {
  if (e.target.tagName === 'INPUT' || e.target.tagName === 'SELECT' || e.target.tagName === 'TEXTAREA') return;
  if (e.key === 'Escape') { state.arrowDraftSource = null; state.termDraft = []; clearTermHighlight(); updateHint(); render(); renderDraftBar(); return; }
  if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z') { e.preventDefault(); if (e.shiftKey) doRedo(); else doUndo(); return; }
  const map = { v: 'select', a: 'vertex', r: 'arrow', t: 'term', m: 'mutate', e: 'erase' };
  const k = e.key.toLowerCase();
  if (map[k]) { setMode(map[k]); }
});

function pruneTermsReferencingMissingArrows() {
  const ids = new Set(state.quiver.arrows.keys());
  for (const [key, t] of [...state.potential]) if (t.word.some(id => !ids.has(id))) state.potential.delete(key);
  state.termDraft = state.termDraft.filter(id => ids.has(id));
  if (state.highlightedTermKey !== null && !state.potential.has(state.highlightedTermKey)) state.highlightedTermKey = null;
}

// After a few mutations, arrow labels accumulate brackets and stars
// (e.g. a****[[ab]c*]) since each mutation composes/reverses the arrows
// it touches by name. Relabeling only touches the *display* labels —
// vertex and arrow ids, and every word in the potential (which is stored
// by id, not label), are untouched, so this is always safe and never
// changes the mathematics.
function relabelAll() {
  const vs = [...state.quiver.vertices.values()].sort((x, y) => x.id - y.id);
  vs.forEach((v, i) => { v.label = String(i + 1); });
  const as = [...state.quiver.arrows.values()].sort((x, y) => x.id - y.id);
  as.forEach((a, i) => { a.label = 'a' + (i + 1); a.labelDef = undefined; });
  state.highlightedTermKey = null;
  snapshot('Relabel');
  render(); renderInspector(); renderTerms(); renderDraftBar();
  addMessage('Relabeled: vertices 1…' + vs.length + ', arrows a1…a' + as.length + '.', 'ok');
}

function doUndo() { if (historyIndex > 0) restoreSnapshot(historyIndex - 1); }
function doRedo() { if (historyIndex < history.length - 1) restoreSnapshot(historyIndex + 1); }

/* ======================================================================
   PART 4b — running a mutation off the main thread

   Mutation is a pure function of (quiver, potential, k, maxLen), so it can
   run in a Web Worker with nothing shared but the message payload. That
   does not make it faster — the state has to be structured-cloned in both
   directions, which costs roughly a third of the round trip — so it is used
   only above WORKER_MIN_ARROWS, where a mutation takes long enough that a
   frozen tab is the real problem. Below that it runs inline, as before.

   That threshold is measured against the size of the quiver the mutation
   PRODUCES, not the one it is handed. Cost is driven by the premutation's
   composite arrows, one per (arrow into k, arrow out of k) pair, so the
   output can dwarf the input: a 3-vertex quiver carrying three parallel
   arrows on each edge grows 3 -> 12 -> 24 -> 108 -> 1401 -> 114384 arrows,
   and the 1401-arrow step — far below any input-side threshold — is the one
   that freezes the tab for seconds. predictedArrowCount() works the figure
   out in one pass, before any of that work is done.

   What it buys at that size: the page stays alive, the mutation can be
   cancelled (terminating the worker is the only way to stop it — there is
   no cooperative abort without SharedArrayBuffer), and a mutation that
   exhausts memory kills the worker instead of the tab.

   The worker is built from a Blob URL rather than a separate .js file so
   that it works when this page is opened straight off disk (file://),
   where a worker script fetched by relative URL would not load. If the
   Worker cannot be created at all — or fails once running — the mutation
   falls back to the main thread, which is slow but always correct.
   ====================================================================== */
const WORKER_MIN_ARROWS = 35000;

// Exactly the arrow count mutateQP() is about to build: one composite per
// (incoming, outgoing) pair, one reversal per arrow at k, and every arrow
// not touching k carried over. Counted without allocating any of them.
// This is the premutation's count, and the reduction only ever deletes
// arrows from it, so it also bounds the final quiver.
function predictedArrowCount(quiver, k) {
  let incoming = 0, outgoing = 0, untouched = 0;
  for (const a of quiver.arrows.values()) {
    if (a.target === k) incoming++;
    else if (a.source === k) outgoing++;
    else untouched++;
  }
  return incoming * outgoing + incoming + outgoing + untouched;
}

// Runs INSIDE the worker; never called here. It is stringified into the
// worker source alongside QPEngine, so it may only use what that source
// defines plus the worker's own globals.
function qpWorkerMain() {
  const QP = QPEngine();
  self.onmessage = (e) => {
    const { id, field, quiver, potential, k, maxLen } = e.data;
    try {
      QP.setField(field && field.kind === 'Fp' ? QP.makePrimeField(BigInt(field.p)) : QP.RationalField);
      const res = QP.mutateQP(quiver, potential, k, maxLen, (stage) => self.postMessage({ id, stage }));
      self.postMessage({ id, quiver: res.quiver, potential: res.potential, warnings: res.warnings });
    } catch (err) {
      self.postMessage({ id, error: (err && err.message) || String(err) });
    }
  };
}
function makeWorkerSource() {
  return QPEngine.toString() + '\n' + qpWorkerMain.toString() + '\nqpWorkerMain();\n';
}

let qpWorker = null;            // the live Worker, or null if not started
let qpWorkerUrl = null;         // Blob URL it is built from, reused across restarts
let qpWorkerUnavailable = false;// creation or startup failed; stop trying
let qpRequestId = 0;
let qpPending = null;           // { id, vertexId, label, progress } while a mutation is in flight

function getWorker() {
  if (qpWorker) return qpWorker;
  if (qpWorkerUnavailable || typeof Worker === 'undefined') return null;
  try {
    if (!qpWorkerUrl) qpWorkerUrl = URL.createObjectURL(new Blob([makeWorkerSource()], { type: 'text/javascript' }));
    const w = new Worker(qpWorkerUrl);
    w.onmessage = onWorkerMessage;
    // A Blob worker can be refused after construction (a strict CSP, say).
    // Treat that like never having had one: drop back to the main thread
    // and finish the mutation the user asked for.
    w.onerror = (ev) => {
      if (ev && typeof ev.preventDefault === 'function') ev.preventDefault();
      qpWorkerUnavailable = true;
      if (qpWorker) { qpWorker.terminate(); qpWorker = null; }
      const pending = qpPending;
      qpPending = null;
      closeMutationProgress();
      if (pending) {
        addMessage('Background mutation was not available here; running it on the page instead — it may freeze for a while.', 'warn');
        mutateInline(pending.vertexId);
      }
    };
    qpWorker = w;
    return w;
  } catch (e) {
    qpWorkerUnavailable = true;
    return null;
  }
}
function fieldDescriptor() {
  const f = QP.getField();
  return f.kind === 'Fp' ? { kind: 'Fp', p: f.p.toString() } : { kind: 'Q' };
}
function onWorkerMessage(e) {
  const msg = e.data;
  // Ignore anything that is not the answer to the request now outstanding:
  // a cancelled mutation's worker may still be draining messages.
  if (!qpPending || msg.id !== qpPending.id) return;
  if (msg.stage) { qpPending.progress(msg.stage); return; }
  const pending = qpPending;
  qpPending = null;
  closeMutationProgress();
  if (msg.error) { addMessage('Could not mutate: ' + msg.error, 'warn'); return; }
  applyMutation({ quiver: msg.quiver, potential: msg.potential, warnings: msg.warnings }, pending.label);
}
function cancelMutation() {
  if (!qpPending) return;
  qpPending = null;
  if (qpWorker) { qpWorker.terminate(); qpWorker = null; } // restarted on demand from the same Blob URL
  closeMutationProgress();
  addMessage('Mutation cancelled.', 'warn');
}

// A modal progress panel reusing the existing dialog, with Cancel as its
// only action — it also serves as the lock that keeps the quiver from being
// edited while a mutation is computed against it.
function showMutationProgress(vertexLabel, onCancel) {
  const overlay = document.getElementById('modalOverlay');
  const okBtn = document.getElementById('modalOk');
  const cancelBtn = document.getElementById('modalCancel');
  const msgEl = document.getElementById('modalMsg');
  document.getElementById('modalTitle').textContent = 'Mutating at vertex ' + vertexLabel + '…';
  msgEl.textContent = 'Starting…';
  msgEl.style.display = '';
  document.getElementById('modalInput').style.display = 'none';
  okBtn.style.display = 'none';
  cancelBtn.textContent = 'Cancel';
  overlay.classList.add('qp-open');
  const onKey = (e) => { if (e.key === 'Escape') onCancel(); };
  cancelBtn.onclick = onCancel;
  window.addEventListener('keydown', onKey, true);
  closeMutationProgress.cleanup = () => {
    window.removeEventListener('keydown', onKey, true);
    cancelBtn.onclick = null;
    cancelBtn.textContent = 'Cancel';
    okBtn.style.display = '';
    overlay.classList.remove('qp-open');
  };
  return (stage) => { msgEl.textContent = stage; };
}
function closeMutationProgress() {
  if (closeMutationProgress.cleanup) { closeMutationProgress.cleanup(); closeMutationProgress.cleanup = null; }
}

// Shared tail of both paths: adopt the result, record it, redraw.
function applyMutation(res, vertexLabel) {
  state.quiver = res.quiver; state.potential = res.potential;
  state.selection = null; state.termDraft = []; state.arrowDraftSource = null; state.highlightedTermKey = null;
  snapshot('Mutate at ' + vertexLabel);
  for (const w of res.warnings) addMessage(w, 'warn');
  renderAll();
}
function mutateInline(vertexId) {
  const v = state.quiver.vertices.get(vertexId);
  if (!v) return;
  try {
    applyMutation(QP.mutateQP(state.quiver, state.potential, vertexId, state.maxLen), v.label);
  } catch (err) {
    addMessage('Could not mutate: ' + err.message, 'warn');
  }
}

function doMutate(vertexId) {
  const v = state.quiver.vertices.get(vertexId);
  if (!v || qpPending) return; // one mutation at a time; the panel blocks the rest
  if (predictedArrowCount(state.quiver, vertexId) < WORKER_MIN_ARROWS) { mutateInline(vertexId); return; }
  const worker = getWorker();
  if (!worker) { mutateInline(vertexId); return; }
  const id = ++qpRequestId;
  const progress = showMutationProgress(v.label, cancelMutation);
  qpPending = { id, vertexId, label: v.label, progress };
  try {
    worker.postMessage({ id, field: fieldDescriptor(), quiver: state.quiver,
                         potential: state.potential, k: vertexId, maxLen: state.maxLen });
  } catch (err) {
    // The state could not be handed over (nothing in it should resist a
    // structured clone, but if that ever changes, still do the mutation).
    qpPending = null;
    closeMutationProgress();
    mutateInline(vertexId);
  }
}

/* ======================================================================
   PART 5 — panels
   ====================================================================== */
function renderStats() {
  document.getElementById('statV').textContent = state.quiver.vertices.size;
  document.getElementById('statA').textContent = state.quiver.arrows.size;
}
function wordHTML(word) {
  return word.map(id => {
    const a = state.quiver.arrows.get(id);
    return '<span>' + (a ? escapeHtml(QP.labelOf(a)) : '?') + '</span>';
  }).join('<span class="qp-sep">·</span>');
}
function escapeHtml(s) { return s.replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c])); }

function renderTerms() {
  const list = document.getElementById('termList');
  const empty = document.getElementById('termEmpty');
  const terms = [...state.potential.values()];
  document.getElementById('termCount').textContent = terms.length;
  empty.style.display = terms.length ? 'none' : '';
  list.innerHTML = '';
  for (const t of terms) {
    const key = keyForTerm(t);
    const row = document.createElement('div');
    row.className = 'qp-term' + (state.highlightedTermKey === key ? ' qp-highlighted' : '');
    const coeff = document.createElement('span'); coeff.className = 'qp-coeff'; coeff.textContent = QP.fToString(t.coeff);
    const word = document.createElement('span'); word.className = 'qp-word'; word.innerHTML = wordHTML(t.word);
    const rm = document.createElement('button'); rm.className = 'qp-rm'; rm.textContent = '✕';
    rm.onclick = (e) => { e.stopPropagation(); QP_removeTerm(t); };
    row.title = 'Click to highlight this cycle in the drawing';
    row.onclick = () => {
      state.highlightedTermKey = (state.highlightedTermKey === key) ? null : key;
      renderTerms();
      render();
    };
    row.append(coeff, word, rm);
    list.appendChild(row);
  }
}
function keyForTerm(t) { return t.word.join(','); }
function QP_removeTerm(t) {
  const key = keyForTerm(t);
  state.potential.delete(key);
  if (state.highlightedTermKey === key) state.highlightedTermKey = null;
  snapshot('Remove potential term');
  renderTerms();
  render();
}

function renderDraftBar() {
  const bar = document.getElementById('draftBar');
  if (state.mode !== 'term' || state.termDraft.length === 0) { bar.style.display = 'none'; return; }
  bar.style.display = 'flex';
  const closes = canCloseTerm();
  bar.innerHTML = wordHTML(state.termDraft) +
    (closes ? '<span class="qp-sep">→ closes ✓</span>' : '<span class="qp-ph"> · needs to return to start</span>');
  if (closes) {
    const coeffInput = document.createElement('input');
    coeffInput.type = 'text'; coeffInput.value = '1'; coeffInput.style.width = '54px';
    coeffInput.className = 'qp-input';
    coeffInput.id = 'coeffInput';
    const addBtn = document.createElement('button');
    addBtn.className = 'nav-button qp-small qp-active'; addBtn.textContent = 'Add term';
    addBtn.onclick = () => {
      try {
        const c = QP.fParse(coeffInput.value);
        QP.potAdd(state.potential, state.termDraft.slice(), c);
        state.termDraft = [];
        snapshot('Add potential term');
        renderTerms(); renderDraftBar(); render();
      } catch (err) { addMessage('Bad coefficient — use an integer or a/b.', 'warn'); }
    };
    const clearBtn = document.createElement('button');
    clearBtn.className = 'nav-button qp-small'; clearBtn.textContent = 'Cancel';
    clearBtn.onclick = () => { state.termDraft = []; renderDraftBar(); render(); };
    bar.append(' coeff ', coeffInput, addBtn, clearBtn);
  } else {
    const clearBtn = document.createElement('button');
    clearBtn.className = 'nav-button qp-small'; clearBtn.textContent = 'Cancel';
    clearBtn.onclick = () => { state.termDraft = []; renderDraftBar(); render(); };
    bar.append(clearBtn);
  }
}
function canCloseTerm() {
  if (state.termDraft.length < 2) return false;
  const first = state.quiver.arrows.get(state.termDraft[0]);
  const last = state.quiver.arrows.get(state.termDraft[state.termDraft.length - 1]);
  return first && last && last.target === first.source;
}

function renderInspector() {
  const card = document.getElementById('inspectorCard');
  const body = document.getElementById('inspectorBody');
  if (!state.selection) { card.style.display = 'none'; return; }
  card.style.display = '';
  if (state.selection.type === 'vertex') {
    const v = state.quiver.vertices.get(state.selection.id);
    if (!v) { card.style.display = 'none'; return; }
    const deg = [...state.quiver.arrows.values()].filter(a => a.source === v.id || a.target === v.id).length;
    body.innerHTML = `
      <div class="qp-inspector-row"><span class="qp-k">Type</span><span class="qp-v">vertex</span></div>
      <div class="qp-inspector-row"><span class="qp-k">Label</span><span class="qp-v">${escapeHtml(v.label)}</span></div>
      <div class="qp-inspector-row"><span class="qp-k">Incident arrows</span><span class="qp-v">${deg}</span></div>
      <div class="qp-row qp-inspector-actions" style="margin-top:8px">
        <button class="nav-button" id="renameV">Rename</button>
        <button class="nav-button qp-active" id="mutateHere">Mutate here</button>
      </div>`;
    document.getElementById('renameV').onclick = () => showRename('Rename vertex', v.label, (nv) => { v.label = nv; snapshot('Rename vertex'); render(); renderInspector(); });
    document.getElementById('mutateHere').onclick = () => doMutate(v.id);
  } else {
    const a = state.quiver.arrows.get(state.selection.id);
    if (!a) { card.style.display = 'none'; return; }
    const s = state.quiver.vertices.get(a.source), t = state.quiver.vertices.get(a.target);
    body.innerHTML = `
      <div class="qp-inspector-row"><span class="qp-k">Type</span><span class="qp-v">arrow</span></div>
      <div class="qp-inspector-row"><span class="qp-k">Label</span><span class="qp-v">${escapeHtml(QP.labelOf(a))}</span></div>
      <div class="qp-inspector-row"><span class="qp-k">Source → target</span><span class="qp-v">${escapeHtml(s?.label ?? '?')} → ${escapeHtml(t?.label ?? '?')}</span></div>
      <div class="qp-row qp-inspector-actions" style="margin-top:8px">
        <button class="nav-button" id="renameA">Rename</button>
        <button class="nav-button qp-danger" id="deleteA">Delete</button>
      </div>`;
    document.getElementById('renameA').onclick = () => showRename('Rename arrow', QP.labelOf(a), (na) => { a.label = na; a.labelDef = undefined; snapshot('Rename arrow'); render(); renderInspector(); renderTerms(); });
    document.getElementById('deleteA').onclick = () => { state.quiver.arrows.delete(a.id); pruneTermsReferencingMissingArrows(); snapshot('Delete arrow ' + QP.labelOf(a)); state.selection = null; renderInspector(); render(); renderStats(); renderTerms(); };
  }
}

function renderHistory() {
  document.getElementById('histCount').textContent = history.length;
  const list = document.getElementById('histList');
  list.innerHTML = '';
  history.forEach((h, i) => {
    const div = document.createElement('div');
    div.className = 'qp-h-item' + (i === historyIndex ? ' qp-current' : '');
    div.textContent = (i + 1) + '. ' + h.label;
    div.onclick = () => restoreSnapshot(i);
    list.appendChild(div);
  });
  list.scrollTop = list.scrollHeight;
  document.getElementById('undoBtn').disabled = historyIndex <= 0;
  document.getElementById('redoBtn').disabled = historyIndex >= history.length - 1;
}

function syncMaxLenUI() {
  document.getElementById('maxLenRange').value = state.maxLen;
  document.getElementById('maxLenVal').textContent = state.maxLen;
  document.getElementById('maxLenVal1').textContent = state.maxLen;
}

function toSubscript(number) {
    const subscripts = {
        "0": "₀",
        "1": "₁",
        "2": "₂",
        "3": "₃",
        "4": "₄",
        "5": "₅",
        "6": "₆",
        "7": "₇",
        "8": "₈",
        "9": "₉"
    };

    return String(number)
        .split("")
        .map(digit => subscripts[digit])
        .join("");
}

function syncFieldUI() {
  const field = QP.getField();
  const kindSel = document.getElementById('fieldKind');
  const pInput = document.getElementById('fieldP');
  const current = document.getElementById('fieldCurrent');
  if (field.kind === 'Fp') {
    kindSel.value = 'Fp';
    pInput.style.display = '';
    pInput.value = field.p.toString();
    current.textContent = 'Currently: 𝔽' + toSubscript(field.p);
  } else {
    kindSel.value = 'Q';
    pInput.style.display = 'none';
    current.textContent = 'Currently: ℚ';
  }
}

// Reinterprets every existing potential coefficient over `target` (its raw
// {n,d} is re-run through the new field's own make(), which is the correct
// way to move a value between fields — see the note on QP.F above). A term
// whose denominator isn't invertible in the new field (e.g. 1/2 moving into
// F_2) genuinely has no image there and gets dropped, with a count shown.
function applyFieldSwitch(target) {
  const oldTerms = [...state.potential.values()];
  QP.setField(target);
  const newPotential = new Map();
  let dropped = 0;
  for (const t of oldTerms) {
    try { QP.potAdd(newPotential, t.word, target.make(t.coeff.n, t.coeff.d)); }
    catch (e) { dropped++; }
  }
  state.potential = newPotential;
  state.selection = null; state.termDraft = []; state.arrowDraftSource = null; state.highlightedTermKey = null;
  history = []; historyIndex = -1;
  snapshot('Switch field to ' + (target.kind === 'Q' ? 'Q' : ('F_' + target.p)));
  syncFieldUI();
  renderAll();
  if (dropped) addMessage(`${dropped} potential term` + (dropped != 1 ? 's' : '') + ` dropped — their denominator wasn't invertible in the new field.`, 'warn');
  else addMessage('Switched coefficient field.', 'ok');
}

function renderAll() { render(); renderStats(); renderTerms(); renderDraftBar(); renderInspector(); renderHistory(); }

/* ======================================================================
   PART 6 — wiring
   ====================================================================== */
document.querySelectorAll('#modeSeg button').forEach(b => b.addEventListener('click', () => setMode(b.dataset.mode)));
document.getElementById('undoBtn').addEventListener('click', doUndo);
document.getElementById('redoBtn').addEventListener('click', doRedo);
document.getElementById('clearBtn').addEventListener('click', () => {
  showConfirm('Clear everything?', 'This removes every vertex, arrow, and potential term. It can be undone with Undo afterward.', 'Clear', () => {
    const maxLen = state.maxLen;
    state = freshState();
    state.maxLen = maxLen;
    snapshot('Clear');
    renderAll();
  });
});
document.getElementById('relabelBtn').addEventListener('click', relabelAll);
document.getElementById('presetSel').addEventListener('change', (e) => { if (e.target.value) { loadPreset(e.target.value); e.target.value = ''; } });
document.getElementById('maxLenRange').addEventListener('input', (e) => { state.maxLen = parseInt(e.target.value, 10); document.getElementById('maxLenVal').textContent = state.maxLen;
document.getElementById('maxLenVal1').textContent = state.maxLen;});
document.getElementById('maxLenRange').addEventListener('change', () => snapshot('Change length cap'));
document.getElementById('fieldKind').addEventListener('change', () => {
  document.getElementById('fieldP').style.display = document.getElementById('fieldKind').value === 'Fp' ? '' : 'none';
});
document.getElementById('fieldApplyBtn').addEventListener('click', () => {
  const kind = document.getElementById('fieldKind').value;
  const current = QP.getField();
  let target;
  if (kind === 'Q') {
    if (current.kind === 'Q') return;
    target = QP.RationalField;
  } else {
    let p;
    try { p = BigInt(document.getElementById('fieldP').value.trim()); } catch (e) { addMessage('Enter a whole number for p.', 'warn'); return; }
    if (!QP.isPrime(p)) { addMessage(p + ' is not prime — pick a prime p (2, 3, 5, 7, 11, …).', 'warn'); return; }
    if (current.kind === 'Fp' && current.p === p) return;
    try { target = QP.makePrimeField(p); } catch (e) { addMessage(e.message, 'warn'); return; }
  }
  const label = target.kind === 'Q' ? 'ℚ' : ('𝔽' + toSubscript(target.p));
  showConfirm(
    'Switch coefficient field?',
    `Every existing potential coefficient will be reinterpreted over ${label}. Terms whose denominator isn't invertible there will be dropped. This starts a new undo history.`,
    'Switch',
    () => applyFieldSwitch(target)
  );
});
document.getElementById('exportBtn').addEventListener('click', () => {
  showExportModal(serializeState());
});
document.getElementById('importBtn').addEventListener('click', () => document.getElementById('importFile').click());
document.getElementById('importFile').addEventListener('change', (e) => {
  const file = e.target.files[0]; if (!file) return;
  const reader = new FileReader();
  reader.onload = () => { try { deserializeState(reader.result); addMessage('Imported.', 'ok'); } catch (err) { addMessage('Import failed: ' + err.message, 'warn'); } };
  reader.readAsText(file);
  e.target.value = '';
});

/* ======================================================================
   PART 7 — boot
   ====================================================================== */
loadPreset('3cycle');
syncFieldUI();
// Browsers sometimes restore a form control's live value across a reload
// (independent of the HTML `value` attribute), so without this the max
// cycle length slider can visually stay wherever it was before the reload
// even though state.maxLen (set by loadPreset above) is correctly back to
// the default — sync it explicitly so the UI always matches state on boot.
syncMaxLenUI();
updateHint();
resizeCanvas();
