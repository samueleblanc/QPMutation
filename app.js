"use strict";
/* ======================================================================
   PART 1 — QP mutation engine (Derksen–Weyman–Zelevinsky mutation; the
   reduction step implements DWZ's Splitting Theorem via Lemmas 4.7-4.8,
   arXiv:0704.0649).
   ====================================================================== */
const QP = (function () {
  // ---------- Coefficient fields: exact rationals (Q), or a prime field F_p ----------
  // Every function below this point only ever touches coefficients through
  // fadd/fsub/fmul/fdiv/fneg/finv/fisZero/feq/fone/fzero/fToString/F. None
  // of it inspects {n,d} structurally, so setField() alone is enough to
  // make every computation — potentials, mutation, the linear-algebra
  // diagonalization — run over the new field with no other changes.
  function gcdBig(a, b) { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) { [a, b] = [b, a % b]; } return a; }

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
    function make(n, d = 1n) {
      n = BigInt(n); d = BigInt(d);
      if (d === 0n) throw new Error('division by zero');
      if (d < 0n) { n = -n; d = -d; }
      const g = gcdBig(n, d) || 1n;
      return { n: n / g, d: d / g };
    }
    return {
      kind: 'Q', label: 'Q',
      make,
      add: (x, y) => make(x.n * y.d + y.n * x.d, x.d * y.d),
      sub: (x, y) => make(x.n * y.d - y.n * x.d, x.d * y.d),
      mul: (x, y) => make(x.n * y.n, x.d * y.d),
      div: (x, y) => make(x.n * y.d, x.d * y.n),
      neg: (x) => make(-x.n, x.d),
      inv: (x) => make(x.d, x.n),
      isZero: (x) => x.n === 0n,
      eq: (x, y) => x.n === y.n && x.d === y.d,
      toString: (x) => (x.d === 1n ? x.n.toString() : `${x.n}/${x.d}`),
    };
  })();

  function makePrimeField(p) {
    p = BigInt(p);
    if (!isPrime(p)) throw new Error(`${p} is not prime`);
    const reduce = (n) => { n = BigInt(n) % p; return n < 0n ? n + p : n; };
    function make(n, d = 1n) {
      const dr = reduce(d);
      if (dr === 0n) throw new Error(`denominator is 0 mod ${p}`);
      return { n: reduce(BigInt(n) * modInverse(dr, p)), d: 1n };
    }
    return {
      kind: 'Fp', p, label: `F_${p}`,
      make,
      add: (x, y) => ({ n: reduce(x.n + y.n), d: 1n }),
      sub: (x, y) => ({ n: reduce(x.n - y.n), d: 1n }),
      mul: (x, y) => ({ n: reduce(x.n * y.n), d: 1n }),
      div: (x, y) => { if (y.n === 0n) throw new Error('division by zero'); return { n: reduce(x.n * modInverse(y.n, p)), d: 1n }; },
      neg: (x) => ({ n: reduce(-x.n), d: 1n }),
      inv: (x) => { if (x.n === 0n) throw new Error('division by zero'); return { n: modInverse(x.n, p), d: 1n }; },
      isZero: (x) => x.n === 0n,
      eq: (x, y) => x.n === y.n,
      toString: (x) => x.n.toString(),
    };
  }

  let CoeffField = RationalField;
  function getField() { return CoeffField; }
  function setField(field) { CoeffField = field; }

  function F(n, d = 1n) { return CoeffField.make(n, d); }
  const fadd = (x, y) => CoeffField.add(x, y);
  const fsub = (x, y) => CoeffField.sub(x, y);
  const fmul = (x, y) => CoeffField.mul(x, y);
  const fdiv = (x, y) => CoeffField.div(x, y);
  const fneg = (x) => CoeffField.neg(x);
  const finv = (x) => CoeffField.inv(x);
  const fisZero = (x) => CoeffField.isZero(x);
  const feq = (x, y) => CoeffField.eq(x, y);
  // 0 and 1 have the same {n,d} shape in every field this module supports,
  // so these stay valid across setField() calls with no redefinition.
  const fone = { n: 1n, d: 1n }, fzero = { n: 0n, d: 1n };
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
    // Pick one word in the equivalence class of words up to cyclical equivalence
    const n = word.length;
    let best = null;
    for (let i = 0; i < n; i++) {
      const rot = word.slice(i).concat(word.slice(0, i));
      if (best === null || lexLess(rot, best)) best = rot;
    }
    return best;
  }
  function lexLess(a, b) { for (let i = 0; i < a.length; i++) { if (a[i] !== b[i]) return a[i] < b[i]; } return false; }
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
  function cyclicDerivative(map, arrowId) {
    const out = new Map();
    for (const { word, coeff } of map.values()) {
      const n = word.length;
      for (let i = 0; i < n; i++) {
        if (word[i] !== arrowId) continue;
        const path = word.slice(i + 1).concat(word.slice(0, i));
        const key = keyOf(path);
        const existing = out.get(key);
        const nc = existing ? fadd(existing.coeff, coeff) : coeff;
        if (fisZero(nc)) out.delete(key); else out.set(key, { path, coeff: nc });
      }
    }
    return out;
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
    const out = new Map();
    const dropped = (arr) => { if (truncated && arr.length > maxLen) truncated.value = true; };
    for (const { word, coeff } of map.values()) {
      let partials = [{ arr: [], c: coeff }];
      for (const id of word) {
        const subs = substitutions.get(id);
        const nextPartials = [];
        for (const p of partials) {
          if (p.arr.length > maxLen) { dropped(p.arr); continue; }
          if (subs) {
            for (const { path, coeff: pc } of subs) {
              const arr = p.arr.concat(path);
              if (arr.length > maxLen) { dropped(arr); continue; }
              nextPartials.push({ arr, c: fmul(p.c, pc) });
            }
          } else {
            nextPartials.push({ arr: p.arr.concat([id]), c: p.c });
          }
        }
        partials = nextPartials;
      }
      for (const p of partials) {
        if (p.arr.length > maxLen) { dropped(p.arr); continue; }
        potAdd(out, p.arr, p.c);
      }
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
      const neg = c.n < 0n;
      const absC = neg ? fneg(c) : c;
      const coeffStr = feq(absC, fone) ? '' : fToString(absC) + '·';
      s += (idx === 0 ? (neg ? '-' : '') : (neg ? ' - ' : ' + ')) + coeffStr + label;
    });
    return s;
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
  function diagonalizeQuadraticPart(quiver, arrows, current, warnings, maxLen, idBox, truncated) {
    const byPair = new Map(); // "lo,hi" -> {lo, hi, toHi:[ids lo->hi], toLo:[ids hi->lo]}
    for (const a of arrows.values()) {
      if (a.source === a.target) continue;
      const [lo, hi] = a.source < a.target ? [a.source, a.target] : [a.target, a.source];
      const key = lo + ',' + hi;
      let g = byPair.get(key);
      if (!g) { g = { lo, hi, toHi: [], toLo: [] }; byPair.set(key, g); }
      (a.source === lo ? g.toHi : g.toLo).push(a.id);
    }

    for (const g of byPair.values()) {
      const A = g.toHi.slice().sort((x, y) => x - y);
      const B = g.toLo.slice().sort((x, y) => x - y);
      if (A.length === 0 || B.length === 0) continue;

      const M = A.map(() => B.map(() => fzero));
      for (let p = 0; p < A.length; p++) {
        for (let q = 0; q < B.length; q++) {
          const t = current.get(keyOf(canonicalWord([A[p], B[q]])));
          if (t) M[p][q] = t.coeff;
        }
      }
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

      // Fresh arrows for the WHOLE block. rowCombo/colCombo (used directly,
      // no inverse) are exactly what the substitution needs; each new
      // arrow's own label — its definition in terms of the OLD arrows — is
      // a different quantity: column k of Rinv=invert(rowCombo) for the A
      // side, column l of Qinv=invert(colCombo) for the B side.
      const oldLabel = id => arrows.get(id)?.label ?? ('#' + id);
      const Rmat = rowCombo.map(combo => A.map(id => combo.get(id) || fzero));
      const Qmat = colCombo.map(combo => B.map(id => combo.get(id) || fzero));
      const Rinv = invertMatrix(Rmat), Qinv = invertMatrix(Qmat);
      const newA = rowCombo.map((_, k) => {
        const id = idBox.value++;
        const defCombo = new Map(A.map((oldId, r) => [oldLabel(oldId), Rinv[r][k]]));
        arrows.set(id, { id, label: comboLabel(defCombo), source: g.lo, target: g.hi });
        return id;
      });
      const newB = colCombo.map((_, l) => {
        const id = idBox.value++;
        const defCombo = new Map(B.map((oldId, c) => [oldLabel(oldId), Qinv[c][l]]));
        arrows.set(id, { id, label: comboLabel(defCombo), source: g.hi, target: g.lo });
        return id;
      });

      const substitutions = new Map();
      A.forEach((oldId) => {
        const parts = [];
        rowCombo.forEach((combo, k) => { const c = combo.get(oldId); if (c && !fisZero(c)) parts.push({ path: [newA[k]], coeff: c }); });
        substitutions.set(oldId, parts);
      });
      B.forEach((oldId) => {
        const parts = [];
        colCombo.forEach((combo, k) => { const c = combo.get(oldId); if (c && !fisZero(c)) parts.push({ path: [newB[k]], coeff: c }); });
        substitutions.set(oldId, parts);
      });

      current = applySubstitution(current, substitutions, maxLen + 4, truncated);
      for (const oldId of A) arrows.delete(oldId);
      for (const oldId of B) arrows.delete(oldId);
    }
    return current;
  }

  function mutateQP(quiver, potential, k, maxLen = 8) {
    const warnings = [];
    // Shared across the whole function: every length-cap-driven drop below
    // (potTruncate's own cap, diagonalizeQuadraticPart's substitution, each
    // round of the pair-splitting loop) sets this one flag, checked once
    // before returning, so a single warning covers all of them regardless
    // of which stage actually did the dropping.
    const truncated = { value: false };
    for (const a of quiver.arrows.values()) {
      if (a.source === k && a.target === k) throw new Error('Cannot mutate at a vertex with a loop.');
    }
    // DWZ mutation mu_k is only defined when k is not incident to a 2-cycle:
    // under the premutation such a pair collapses to a loop at the far
    // vertex, and the reduction step cannot get rid of it. A 2-cycle that
    // does NOT touch k is fine — the reduction below removes it, and this
    // agrees with mutating the reduced potential (mu-tilde respects
    // right-equivalence).
    const incidentToK = [...quiver.arrows.values()].filter(a => a.source === k || a.target === k);
    for (let i = 0; i < incidentToK.length; i++) {
      for (let j = i + 1; j < incidentToK.length; j++) {
        const a = incidentToK[i], b = incidentToK[j];
        if (a.source === b.target && a.target === b.source) {
          throw new Error('Cannot mutate at a vertex incident to a 2-cycle — DWZ mutation is not defined there. Remove the 2-cycle first.');
        }
      }
    }
    const incoming = [...quiver.arrows.values()].filter(a => a.target === k && a.source !== k);
    const outgoing = [...quiver.arrows.values()].filter(a => a.source === k && a.target !== k);
    const untouched = [...quiver.arrows.values()].filter(a => a.source !== k && a.target !== k);

    let nextId = quiver.nextArrowId;
    const newArrows = new Map();
    const compositeOf = new Map();
    for (const beta of incoming) {
      for (const alpha of outgoing) {
        const id = nextId++;
        newArrows.set(id, { id, label: `[${beta.label}${alpha.label}]`, source: beta.source, target: alpha.target });
        compositeOf.set(beta.id + '_' + alpha.id, id);
      }
    }
    const reversedOf = new Map();
    for (const a of [...incoming, ...outgoing]) {
      const id = nextId++;
      newArrows.set(id, { id, label: a.label + "'", source: a.target, target: a.source });
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
    tildeW = potTruncate(tildeW, maxLen + 2, truncated);

    let arrows = newArrows;
    const idBox = { value: nextId };
    let current = diagonalizeQuadraticPart(quiver, arrows, tildeW, warnings, maxLen, idBox, truncated);
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
          const { u, v } = splitByPriority(current, pairs, priorityOf, roleOf);
          const converged = pairs.every((_, idx) => u[idx].size === 0 && v[idx].size === 0);
          if (converged) break;
          if (round >= MAX_SPLIT_ROUNDS) { truncated.value = true; break; }
          const substitutions = new Map();
          pairs.forEach((p, idx) => {
            substitutions.set(p.gamma, [{ path: [p.gamma], coeff: fone }, ...[...v[idx].values()].map(({ path, coeff }) => ({ path, coeff: fneg(coeff) }))]);
            substitutions.set(p.delta, [{ path: [p.delta], coeff: fone }, ...[...u[idx].values()].map(({ path, coeff }) => ({ path, coeff: fneg(coeff) }))]);
          });
          const next = potTruncate(applySubstitution(current, substitutions, maxLen + 4, truncated), maxLen, truncated);
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
    const survivingArrows = [...arrows.values()];
    let residual2Cycles = 0;
    for (let i = 0; i < survivingArrows.length; i++) {
      const a = survivingArrows[i];
      if (a.source === a.target) continue;
      for (let j = i + 1; j < survivingArrows.length; j++) {
        const b = survivingArrows[j];
        if (a.source === b.target && a.target === b.source) residual2Cycles++;
      }
    }
    if (residual2Cycles > 0) warnings.push(`Resulting quiver still has ${residual2Cycles} two-cycle(s) (a pair of arrows i↔j survives with no way to cancel it) — the potential is degenerate at this vertex.`);

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
    canonicalWord, potAdd, potTruncate, potEqual, cyclicDerivative, splitByPriority, applySubstitution, mutateQP,
  };
})();

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
    warnings: [],
    lastMutation: null,
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

function snapshot(label) {
  const snap = structuredClone({ quiver: state.quiver, potential: state.potential, maxLen: state.maxLen });
  history = history.slice(0, historyIndex + 1);
  history.push({ label, snap });
  if (history.length > 60) history.shift();
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
  if (name === 'empty3') {
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
  if (badTerms.length) addMessage(`Discarded ${badTerms.length} malformed potential term(s) from this preset (internal bug — please report).`, 'warn');
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
    arrows: [...Q.arrows.values()].map(a => ({ id: a.id, label: a.label, source: a.source, target: a.target })),
    nextVertexId: Q.nextVertexId, nextArrowId: Q.nextArrowId,
    potential: [...state.potential.values()].map(t => ({ word: t.word, coeff: [t.coeff.n.toString(), t.coeff.d.toString()] })),
    maxLen: state.maxLen,
  }, null, 1);
}
function deserializeState(text) {
  const obj = JSON.parse(text);
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
  const Q = QP.makeQuiver();
  for (const v of obj.vertices) Q.vertices.set(v.id, v);
  for (const a of obj.arrows) Q.arrows.set(a.id, a);
  Q.nextVertexId = obj.nextVertexId; Q.nextArrowId = obj.nextArrowId;
  const W = new Map();
  let skipped = 0;
  for (const t of obj.potential) {
    if (!isValidCyclicWord(Q, t.word)) { skipped++; continue; }
    try { QP.potAdd(W, t.word, QP.F(BigInt(t.coeff[0]), BigInt(t.coeff[1]))); }
    catch (e) { skipped++; }
  }
  state.quiver = Q; state.potential = W; state.maxLen = obj.maxLen || 8;
  state.selection = null; state.termDraft = []; state.arrowDraftSource = null; state.highlightedTermKey = null;
  history = []; historyIndex = -1;
  snapshot('Imported');
  syncMaxLenUI();
  syncFieldUI();
  fitView();
  renderAll();
  if (skipped) addMessage(`Skipped ${skipped} potential term(s) that weren't closed, composable cycles, or valid in this field.`, 'warn');
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
function computeArrowGeometry() {
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
  for (const [dKey, bundle] of bundleGeo) {
    const box = bundleBoxLayout(bundle.arrows, bundle.curve);
    if (!box) continue;
    if (x < box.x || x > box.x + box.w || y < box.y || y > box.y + box.h) continue;
    if (x < box.x + box.chevW) return { dKey, dir: -1, n: bundle.arrows.length };
    if (x > box.x + box.w - box.chevW) return { dKey, dir: 1, n: bundle.arrows.length };
    return { dKey, dir: 0, n: bundle.arrows.length };
  }
  return null;
}

function arrowPoints(a, curveOffset) {
  const Q = state.quiver;
  const s = Q.vertices.get(a.source), t = Q.vertices.get(a.target);
  if (!s || !t) return null;
  const dx = t.x - s.x, dy = t.y - s.y;
  const len = Math.hypot(dx, dy) || 1;
  const ux = dx / len, uy = dy / len;
  const px = -uy, py = ux; // perpendicular
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
  const idx = bundleActiveIndex(dKey, arrows.length);
  if (el.dataset.idx !== String(idx)) {
    el.dataset.idx = String(idx);
    el.textContent = arrows[idx].label;
    el.scrollLeft = 0;
  }
  el.style.left = box.name.left + 'px';
  el.style.top = box.name.top + 'px';
  el.style.width = box.name.width + 'px';
  el.style.height = box.name.height + 'px';
  el.style.color = color;

  updateBundleThumb(dKey, el, box, color);
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
function updateBundleThumb(dKey, nameEl, box, color) {
  const trackW = box.thumbTrack.width;
  const maxScroll = nameEl.scrollWidth - nameEl.clientWidth;
  let t = bundleThumbEls.get(dKey);
  if (maxScroll <= 0) {
    if (t) t.track.style.display = 'none';
    return;
  }
  if (!t) {
    const track = document.createElement('div');
    track.className = 'qp-bundle-thumb-track';
    const thumb = document.createElement('div');
    thumb.className = 'qp-bundle-thumb';
    thumb.addEventListener('mousedown', (e) => {
      e.preventDefault();
      const trackRect = track.getBoundingClientRect();
      const range = trackRect.width - thumb.offsetWidth;
      const startX = e.clientX, startLeft = thumb.offsetLeft;
      const onMove = (me) => {
        const left = Math.min(range, Math.max(0, startLeft + (me.clientX - startX)));
        thumb.style.left = left + 'px';
        const maxS = nameEl.scrollWidth - nameEl.clientWidth;
        nameEl.scrollLeft = range > 0 ? maxS * (left / range) : 0;
      };
      const onUp = () => { window.removeEventListener('mousemove', onMove); window.removeEventListener('mouseup', onUp); thumb.classList.remove('qp-dragging'); };
      thumb.classList.add('qp-dragging');
      window.addEventListener('mousemove', onMove);
      window.addEventListener('mouseup', onUp);
    });
    track.addEventListener('mousedown', (e) => {
      if (e.target === thumb) return; // handled by the thumb's own listener above
      // Clicking the bare track jumps the thumb there directly (a quick
      // "page" scroll), same as clicking a normal scrollbar's track.
      const trackRect = track.getBoundingClientRect();
      const range = trackRect.width - thumb.offsetWidth;
      const left = Math.min(range, Math.max(0, e.clientX - trackRect.left - thumb.offsetWidth / 2));
      thumb.style.left = left + 'px';
      const maxS = nameEl.scrollWidth - nameEl.clientWidth;
      nameEl.scrollLeft = range > 0 ? maxS * (left / range) : 0;
    });
    track.appendChild(thumb);
    wrap.appendChild(track);
    t = { track, thumb };
    bundleThumbEls.set(dKey, t);
  }
  t.track.style.display = '';
  t.track.style.left = box.thumbTrack.left + 'px';
  t.track.style.top = box.thumbTrack.top + 'px';
  t.track.style.width = trackW + 'px';
  t.track.style.height = box.thumbTrack.height + 'px';
  const thumbW = Math.max(BUNDLE_THUMB_MIN_WIDTH, trackW * (nameEl.clientWidth / nameEl.scrollWidth));
  t.thumb.style.width = thumbW + 'px';
  const range = trackW - thumbW;
  t.thumb.style.left = (range > 0 ? range * (nameEl.scrollLeft / maxScroll) : 0) + 'px';
}

function render() {
  const rect = wrap.getBoundingClientRect();
  ctx.clearRect(0, 0, rect.width, rect.height);
  const fg = cssVar('--qp-fg'), link = cssVar('--qp-link'), linkSoft = cssVar('--qp-link-soft'),
        border = cssVar('--qp-border'), bg = cssVar('--qp-bg'), mutedBg = cssVar('--qp-muted-bg'),
        danger = cssVar('--qp-danger'), mono = cssVar('--qp-mono'), sans = cssVar('--qp-sans');

  const { geo, bundleGeo } = computeArrowGeometry();
  const termSet = new Set(state.termDraft);
  const { loopIds, twoCycleIds } = updateStructuralWarning();
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
    const label = a.label;
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
    const hasIssue = [...state.quiver.arrows.values()].some(a =>
      (a.source === v.id || a.target === v.id) && (loopIds.has(a.id) || twoCycleIds.has(a.id)));
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
  div.innerHTML = '<span>' + text + '</span><span class="qp-x">✕</span>';
  div.querySelector('.qp-x').onclick = () => div.remove();
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
function getStructuralIssues(quiver) {
  const arrows = [...quiver.arrows.values()];
  const loopIds = new Set(arrows.filter(a => a.source === a.target).map(a => a.id));
  const twoCycleIds = new Set();
  for (let i = 0; i < arrows.length; i++) {
    const a = arrows[i];
    if (a.source === a.target) continue;
    for (let j = i + 1; j < arrows.length; j++) {
      const b = arrows[j];
      if (a.source === b.target && a.target === b.source) { twoCycleIds.add(a.id); twoCycleIds.add(b.id); }
    }
  }
  return { loopIds, twoCycleIds };
}
let structWarnDismissedKey = null;
function updateStructuralWarning() {
  const { loopIds, twoCycleIds } = getStructuralIssues(state.quiver);
  const pairs = twoCycleIds.size / 2;
  const el = document.getElementById('structWarn');
  const row = document.getElementById('statIssueRow');
  const count = document.getElementById('statIssues');
  if (loopIds.size === 0 && pairs === 0) {
    structWarnDismissedKey = null;
    if (el) el.style.display = 'none';
    if (row) row.style.display = 'none';
    return { loopIds, twoCycleIds };
  }
  const parts = [];
  if (loopIds.size) parts.push(loopIds.size + ' loop' + (loopIds.size > 1 ? 's' : ''));
  if (pairs) parts.push(pairs + ' two-cycle' + (pairs > 1 ? 's' : ''));
  // Key identifies exactly which arrows are currently flagged, so dismissing
  // this set re-shows the banner as soon as the set of issues changes
  // (e.g. a new loop/2-cycle appears) rather than staying hidden forever.
  const key = [...loopIds].sort((a, b) => a - b).join(',') + '|' + [...twoCycleIds].sort((a, b) => a - b).join(',');
  if (el) {
    if (structWarnDismissedKey === key) {
      el.style.display = 'none';
    } else {
      el.style.display = 'flex';
      el.innerHTML = '<span>' + parts.join(' and ') + ' present, shown in red — QP mutation needs a loop-free, 2-cycle-free quiver at the vertex you mutate.</span><span class="qp-x">✕</span>';
      el.querySelector('.qp-x').onclick = () => { structWarnDismissedKey = key; el.style.display = 'none'; };
    }
  }
  if (row) row.style.display = '';
  if (count) count.textContent = parts.join(', ');
  return { loopIds, twoCycleIds };
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
  if (nav && nav.dir !== 0) { stepBundle(nav.dKey, nav.dir, nav.n); render(); return; }
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
          snapshot('Add arrow ' + state.quiver.arrows.get(id).label);
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
      snapshot('Delete arrow ' + a.label);
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
  if (a) { showRename('Rename arrow', a.label, (na) => { a.label = na; snapshot('Rename arrow'); render(); renderInspector(); renderTerms(); }); }
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

// After a few mutations, arrow labels accumulate brackets and primes
// (e.g. a''''[[ab]c']) since each mutation composes/reverses the arrows
// it touches by name. Relabeling only touches the *display* labels —
// vertex and arrow ids, and every word in the potential (which is stored
// by id, not label), are untouched, so this is always safe and never
// changes the mathematics.
function relabelAll() {
  const vs = [...state.quiver.vertices.values()].sort((x, y) => x.id - y.id);
  vs.forEach((v, i) => { v.label = String(i + 1); });
  const as = [...state.quiver.arrows.values()].sort((x, y) => x.id - y.id);
  as.forEach((a, i) => { a.label = 'a' + (i + 1); });
  state.highlightedTermKey = null;
  snapshot('Relabel');
  render(); renderInspector(); renderTerms(); renderDraftBar();
  addMessage('Relabeled: vertices 1…' + vs.length + ', arrows a1…a' + as.length + '.', 'ok');
}

function doUndo() { if (historyIndex > 0) restoreSnapshot(historyIndex - 1); }
function doRedo() { if (historyIndex < history.length - 1) restoreSnapshot(historyIndex + 1); }

function doMutate(vertexId) {
  const v = state.quiver.vertices.get(vertexId);
  try {
    const res = QP.mutateQP(state.quiver, state.potential, vertexId, state.maxLen);
    state.quiver = res.quiver; state.potential = res.potential;
    state.selection = null; state.termDraft = []; state.arrowDraftSource = null; state.highlightedTermKey = null;
    snapshot('Mutate at ' + v.label);
    for (const w of res.warnings) addMessage(w, 'warn');
    renderAll();
  } catch (err) {
    addMessage('Could not mutate: ' + err.message, 'warn');
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
    return '<span>' + (a ? escapeHtml(a.label) : '?') + '</span>';
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
      <div class="qp-inspector-row"><span class="qp-k">Label</span><span class="qp-v">${escapeHtml(a.label)}</span></div>
      <div class="qp-inspector-row"><span class="qp-k">Source → target</span><span class="qp-v">${escapeHtml(s?.label ?? '?')} → ${escapeHtml(t?.label ?? '?')}</span></div>
      <div class="qp-row qp-inspector-actions" style="margin-top:8px">
        <button class="nav-button" id="renameA">Rename</button>
        <button class="nav-button qp-danger" id="deleteA">Delete</button>
      </div>`;
    document.getElementById('renameA').onclick = () => showRename('Rename arrow', a.label, (na) => { a.label = na; snapshot('Rename arrow'); render(); renderInspector(); renderTerms(); });
    document.getElementById('deleteA').onclick = () => { state.quiver.arrows.delete(a.id); pruneTermsReferencingMissingArrows(); snapshot('Delete arrow ' + a.label); state.selection = null; renderInspector(); render(); renderStats(); renderTerms(); };
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
  if (dropped) addMessage(`${dropped} potential term(s) dropped — their denominator wasn't invertible in the new field.`, 'warn');
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
loadPreset('empty3');
syncFieldUI();
// Browsers sometimes restore a form control's live value across a reload
// (independent of the HTML `value` attribute), so without this the max
// cycle length slider can visually stay wherever it was before the reload
// even though state.maxLen (set by loadPreset above) is correctly back to
// the default — sync it explicitly so the UI always matches state on boot.
syncMaxLenUI();
updateHint();
resizeCanvas();
