/* Interactive Formal Verification Lab
 *
 * Three small engines and the UI that drives them:
 *   1. DPLL with unit propagation, drawn as a search tree.
 *   2. Explicit-state CTL model checking. Kripke structures are generated
 *      from guarded-command models, and formulas are checked with the usual
 *      fixpoint labelling algorithm.
 *   3. Weakest-precondition VC generation for a tiny while-language. VCs are
 *      checked by trying every integer value in a small range.
 */
(function () {
  'use strict';

  // ==========================================
  // SHARED HELPERS
  // ==========================================
  const $ = (id) => document.getElementById(id);
  const SVG_NS = 'http://www.w3.org/2000/svg';

  function svgEl(tag, attrs, parent) {
    const el = document.createElementNS(SVG_NS, tag);
    for (const [k, v] of Object.entries(attrs || {})) el.setAttribute(k, v);
    if (parent) parent.appendChild(el);
    return el;
  }

  function escapeHtml(s) {
    return String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
  }

  function makeLogger(id) {
    return {
      clear() {
        const box = $(id);
        if (box) box.innerHTML = '';
      },
      log(msg, type = 'info') {
        const box = $(id);
        if (!box) return;
        const line = document.createElement('span');
        line.className = `log-${type}`;
        line.textContent = msg;
        box.appendChild(line);
        box.scrollTop = box.scrollHeight;
      }
    };
  }
  const NULL_LOGGER = { clear() {}, log() {} };

  function setBadge(el, text, classes) {
    el.className = 'badge ' + (classes[text] || 'badge-neutral');
    el.textContent = text;
  }

  // Keeps the label next to a speed slider in sync and reports changes.
  function bindSpeed(inputId, onChange) {
    const input = $(inputId);
    const label = input.parentElement.querySelector('.speed-label');
    const show = () => { label.textContent = `${input.value} ms per step`; };
    input.addEventListener('input', () => { show(); onChange(Number(input.value)); });
    show();
    return () => Number(input.value);
  }

  // Longest operators first, so "->" wins over "-", "<=" over "<", and so on.
  const OPERATORS = ['<->', '->', '=>', '==', '!=', '<=', '>=', '&&', '||',
    '⇔', '↔', '⇒', '→', '≠', '≤', '≥', '∧', '∨', '¬',
    '&', '|', '!', '~', '=', '<', '>', '(', ')', '[', ']', '+', '-', '*', '/'];
  const OP_ALIASES = {
    '=>': '->', '⇒': '->', '→': '->', '⇔': '<->', '↔': '<->', '==': '=', '≠': '!=',
    '≤': '<=', '≥': '>=', '∧': '&', '&&': '&', '∨': '|', '||': '|', '¬': '!', '~': '!'
  };

  function tokenize(src) {
    const toks = [];
    let i = 0;
    while (i < src.length) {
      const c = src[i];
      if (/\s/.test(c)) { i++; continue; }
      if (/[0-9]/.test(c)) {
        let j = i;
        while (j < src.length && /[0-9]/.test(src[j])) j++;
        toks.push({ t: 'num', v: Number(src.slice(i, j)), pos: i });
        i = j;
        continue;
      }
      if (/[A-Za-z_]/.test(c)) {
        let j = i;
        while (j < src.length && /[A-Za-z0-9_]/.test(src[j])) j++;
        toks.push({ t: 'id', v: src.slice(i, j), pos: i });
        i = j;
        continue;
      }
      const op = OPERATORS.find((o) => src.startsWith(o, i));
      if (!op) throw new Error(`Unexpected character "${c}" at position ${i + 1}`);
      toks.push({ t: 'op', v: OP_ALIASES[op] || op, pos: i });
      i += op.length;
    }
    toks.push({ t: 'eof', v: '', pos: src.length });
    return toks;
  }

  class TokenStream {
    constructor(src) { this.toks = tokenize(src); this.i = 0; }
    peek(offset = 0) { return this.toks[Math.min(this.i + offset, this.toks.length - 1)]; }
    next() { return this.toks[this.i++]; }
    isOp(v, offset = 0) { const t = this.peek(offset); return t.t === 'op' && t.v === v; }
    isId(v) { const t = this.peek(); return t.t === 'id' && t.v === v; }
    acceptOp(v) { if (this.isOp(v)) { this.i++; return true; } return false; }
    expectOp(v) { if (!this.acceptOp(v)) this.fail(`Expected "${v}"`); }
    fail(msg) {
      const t = this.peek();
      throw new Error(t.t === 'eof' ? `${msg}, but the input ended` : `${msg} at position ${t.pos + 1}`);
    }
    end() { if (this.peek().t !== 'eof') this.fail('Unexpected input'); }
  }

  // ==========================================
  // 1. DPLL SAT SOLVER
  // ==========================================
  const SAT_PRESETS = {
    'sat-simple': '(A | B) & (~A | C) & (~B | ~C)',
    'unsat-simple': '(A | B) & (~A | B) & (A | ~B) & (~A | ~B)',
    'chain': 'A & (~A | B) & (~B | C) & ~C',
    'php-3-2': '(P11 | P12) & (P21 | P22) & (P31 | P32) & (~P11 | ~P21) & (~P11 | ~P31) & (~P21 | ~P31) & (~P12 | ~P22) & (~P12 | ~P32) & (~P22 | ~P32)'
  };
  const SAT_MAX_VARS = 12;
  const SAT_MAX_NODES = 300;

  // CNF only: clauses joined by "&", literals joined by "|", negation with ~ ! ¬ or -.
  function parseCnf(src) {
    const ts = new TokenStream(src);
    const vars = [];
    const lit = () => {
      let pos = true;
      while (ts.acceptOp('!') || ts.acceptOp('-')) pos = !pos;
      const t = ts.next();
      if (t.t !== 'id' && t.t !== 'num') { ts.i--; ts.fail('Expected a variable name'); }
      const v = String(t.v);
      if (!vars.includes(v)) vars.push(v);
      return { v, pos };
    };
    const clause = () => {
      const lits = [];
      do {
        if (ts.acceptOp('(')) { lits.push(...clause()); ts.expectOp(')'); } else lits.push(lit());
      } while (ts.acceptOp('|'));
      return lits;
    };
    const clauses = [];
    do { clauses.push(clause()); } while (ts.acceptOp('&'));
    ts.end();
    return { vars, clauses };
  }

  class SatTooBig extends Error {}

  const sat = {
    vars: [], clauses: [], assign: new Map(),
    nodes: [], current: -1,
    iter: null, done: false, result: null,
    stats: { decisions: 0, propagations: 0, conflicts: 0 },
    focus: -1,
    timer: null
  };
  let satLog = NULL_LOGGER;
  const bit = (b) => (b ? 1 : 0);
  const litText = (l) => (l.pos ? '' : '¬') + l.v;
  const clauseText = (c) => `(${c.map(litText).join(' ∨ ')})`;

  function satLoad(vars, clauses) {
    stopSatAuto();
    Object.assign(sat, {
      vars, clauses, assign: new Map(), nodes: [], current: -1,
      iter: null, done: false, result: null, focus: -1, toldDone: false,
      stats: { decisions: 0, propagations: 0, conflicts: 0 }
    });
  }

  // One pass over the clauses: is everything satisfied, is something violated, or is a clause unit?
  function satEvaluate() {
    let allSat = true;
    let unit = null;
    for (let c = 0; c < sat.clauses.length; c++) {
      let satisfied = false;
      let open = 0;
      let openLit = null;
      for (const l of sat.clauses[c]) {
        const val = sat.assign.get(l.v);
        if (val === undefined) { open++; openLit = l; } else if (val === l.pos) { satisfied = true; break; }
      }
      if (satisfied) continue;
      allSat = false;
      if (open === 0) return { conflict: c };
      if (open === 1 && !unit) unit = { lit: openLit, clause: c };
    }
    return { allSat, unit };
  }

  function addSatNode(parent, label, kind) {
    const id = sat.nodes.length;
    sat.nodes.push({ id, parent, label, kind, status: 'open' });
    sat.current = id;
    if (sat.nodes.length > SAT_MAX_NODES) throw new SatTooBig();
    return id;
  }

  function markFailed(id) {
    const n = sat.nodes[id];
    if (n.status !== 'conflict') n.status = 'failed';
    sat.current = n.parent;
  }

  // Each `yield` is one visible step in the UI.
  function* dpll(nodeId) {
    const ev = satEvaluate();
    if (ev.conflict !== undefined) {
      sat.nodes[nodeId].status = 'conflict';
      sat.stats.conflicts++;
      sat.focus = ev.conflict;
      satLog.log(`Conflict: every literal in c${ev.conflict + 1} ${clauseText(sat.clauses[ev.conflict])} is false.`, 'danger');
      yield;
      return false;
    }
    if (ev.allSat) {
      sat.nodes[nodeId].status = 'sat';
      return true;
    }
    if (ev.unit) {
      const { lit, clause } = ev.unit;
      sat.assign.set(lit.v, lit.pos);
      sat.stats.propagations++;
      sat.focus = clause;
      const child = addSatNode(nodeId, `${lit.v}=${bit(lit.pos)}`, 'prop');
      satLog.log(`Unit propagation: c${clause + 1} ${clauseText(sat.clauses[clause])} forces ${lit.v} = ${bit(lit.pos)}.`, 'info');
      yield;
      if (yield* dpll(child)) return true;
      sat.assign.delete(lit.v);
      markFailed(child);
      return false;
    }
    const v = sat.vars.find((x) => !sat.assign.has(x));
    for (const val of [true, false]) {
      sat.assign.set(v, val);
      sat.stats.decisions++;
      sat.focus = -1;
      const child = addSatNode(nodeId, `${v}=${bit(val)}`, 'decision');
      satLog.log(`Decision: try ${v} = ${bit(val)}.`, 'step');
      yield;
      if (yield* dpll(child)) return true;
      sat.assign.delete(v);
      markFailed(child);
      sat.focus = -1;
      satLog.log(val ? `Backtrack: ${v} = 1 led to a conflict, so try ${v} = 0.` : `Backtrack: both values of ${v} fail here.`, 'warning');
      yield;
    }
    return false;
  }

  function* satRun() {
    const root = addSatNode(-1, 'start', 'root');
    satLog.log('Start the search with every variable unassigned.', 'step');
    yield;
    const ok = yield* dpll(root);
    sat.done = true;
    sat.result = ok ? 'SAT' : 'UNSAT';
    sat.focus = -1;
    if (ok) {
      for (let n = sat.current; n >= 0; n = sat.nodes[n].parent) sat.nodes[n].onPath = true;
      const model = sat.vars.map((v) => (sat.assign.has(v) ? `${v} = ${bit(sat.assign.get(v))}` : `${v} = any`));
      satLog.log(`Satisfiable. Every clause is true with ${model.join(', ')}.`, 'success');
    } else {
      satLog.log('Unsatisfiable. Every branch of the search ends in a conflict.', 'danger');
    }
  }

  // Advances the search by one step. Returns false once there is nothing left to do.
  function satAdvance() {
    if (sat.done) return false;
    if (!sat.iter) sat.iter = satRun();
    try {
      if (sat.iter.next().done) sat.done = true;
    } catch (e) {
      if (!(e instanceof SatTooBig)) throw e;
      sat.done = true;
      sat.result = 'TOO BIG';
      satLog.log(`Stopped after ${SAT_MAX_NODES} tree nodes. Try a formula with fewer variables.`, 'warning');
    }
    return !sat.done;
  }

  function satStep() {
    if (sat.done) {
      if (!sat.toldDone) satLog.log('The search is finished. Press Reset to run it again.', 'warning');
      sat.toldDone = true;
      return;
    }
    satAdvance();
    if (sat.done) stopSatAuto();
    renderSat();
  }

  function satSolve() {
    stopSatAuto();
    if (sat.done) {
      satLog.log('The search is finished. Press Reset to run it again.', 'warning');
      return;
    }
    while (satAdvance()) { /* run to completion */ }
    renderSat();
  }

  function toggleSatAuto() {
    if (sat.timer) { stopSatAuto(); return; }
    if (sat.done) satReset();
    $('btn-sat-run').textContent = 'Pause';
    sat.timer = setInterval(satStep, satSpeed());
  }

  function stopSatAuto() {
    if (sat.timer) clearInterval(sat.timer);
    sat.timer = null;
    const btn = typeof document !== 'undefined' && $('btn-sat-run');
    if (btn) btn.textContent = 'Auto run';
  }

  let satSpeed = () => 700;

  function satLoadSelected() {
    const key = $('sat-presets').value;
    const custom = key === 'custom';
    $('sat-custom-container').classList.toggle('hidden', !custom);
    const src = custom ? $('sat-custom-input').value : SAT_PRESETS[key];
    const err = $('sat-parse-error');
    err.textContent = '';
    let parsed = { vars: [], clauses: [] };
    if (src.trim()) {
      try {
        parsed = parseCnf(src);
        if (parsed.vars.length > SAT_MAX_VARS) throw new Error(`Please keep it to ${SAT_MAX_VARS} variables or fewer`);
      } catch (e) {
        err.textContent = e.message;
        parsed = { vars: [], clauses: [] };
      }
    }
    satLoad(parsed.vars, parsed.clauses);
    satLog.clear();
    if (parsed.clauses.length) {
      satLog.log(`Loaded ${parsed.clauses.length} clauses over ${parsed.vars.length} variables. Press Step to begin.`, 'info');
    } else {
      satLog.log('Type a formula in CNF to get started.', 'info');
    }
    renderSat();
  }

  function satReset() {
    satLoadSelected();
  }

  function layoutSatTree() {
    const kids = sat.nodes.map(() => []);
    sat.nodes.forEach((n) => { if (n.parent >= 0) kids[n.parent].push(n.id); });
    let leaf = 0;
    const place = (id, depth) => {
      const n = sat.nodes[id];
      n.y = 34 + depth * 56;
      if (!kids[id].length) { n.x = leaf++ * 64; return; }
      kids[id].forEach((k) => place(k, depth + 1));
      n.x = (sat.nodes[kids[id][0]].x + sat.nodes[kids[id][kids[id].length - 1]].x) / 2;
    };
    place(0, 0);
  }

  function drawSatTree() {
    const svg = $('sat-tree-svg');
    svg.innerHTML = '';
    if (!sat.nodes.length) {
      svg.setAttribute('viewBox', '0 0 500 260');
      svgEl('text', { x: 250, y: 130, 'text-anchor': 'middle', class: 'svg-placeholder' }, svg).textContent = 'Press Step or Solve to start the search.';
      return;
    }
    layoutSatTree();
    const xs = sat.nodes.map((n) => n.x);
    const minX = Math.min(...xs) - 50;
    const maxX = Math.max(...xs) + 50;
    const width = Math.max(maxX - minX, 380);
    const height = Math.max(Math.max(...sat.nodes.map((n) => n.y)) + 34, 240);
    svg.setAttribute('viewBox', `${(minX + maxX - width) / 2} 0 ${width} ${height}`);

    sat.nodes.forEach((n) => {
      if (n.parent < 0) return;
      const p = sat.nodes[n.parent];
      let cls = 'tree-link';
      if (n.status === 'failed' || n.status === 'conflict') cls += ' backtracked';
      else if (n.onPath) cls += ' sat-path';
      else cls += ' active';
      svgEl('line', { x1: p.x, y1: p.y, x2: n.x, y2: n.y, class: cls }, svg);
    });

    const KIND = { root: 'Start of the search', decision: 'Decision (a guess)', prop: 'Unit propagation (forced)' };
    sat.nodes.forEach((n) => {
      const g = svgEl('g', { class: `tree-node ${n.status}${n.id === sat.current && !sat.done ? ' current' : ''}` }, svg);
      if (n.kind === 'prop') {
        svgEl('rect', { x: -7, y: -7, width: 14, height: 14, transform: `translate(${n.x} ${n.y}) rotate(45)`, class: 'tree-node-shape' }, g);
      } else {
        svgEl('circle', { cx: n.x, cy: n.y, r: n.kind === 'root' ? 7 : 9, class: 'tree-node-shape' }, g);
      }
      svgEl('text', { x: n.x, y: n.y - 15, 'text-anchor': 'middle', class: 'tree-node-text' }, g).textContent = n.label;
      svgEl('title', {}, g).textContent = `${KIND[n.kind]}: ${n.label}`;
    });
  }

  function renderSat() {
    const status = sat.result || (sat.iter ? 'RUNNING' : 'IDLE');
    setBadge($('sat-status'), status, { SAT: 'badge-satisfied', UNSAT: 'badge-unsat', RUNNING: 'badge-active', 'TOO BIG': 'badge-warning' });

    const box = $('sat-formula-clauses');
    box.innerHTML = '';
    if (!sat.clauses.length) box.innerHTML = '<span class="placeholder-text">No clauses yet.</span>';
    sat.clauses.forEach((clause, ci) => {
      let satisfied = false;
      let open = 0;
      const parts = clause.map((l) => {
        const val = sat.assign.get(l.v);
        let cls = 'lit';
        if (val === undefined) open++;
        else if (val === l.pos) { cls += ' lit-true'; satisfied = true; } else cls += ' lit-false';
        return `<span class="${cls}">${escapeHtml(litText(l))}</span>`;
      });
      const el = document.createElement('div');
      el.className = 'clause-badge';
      if (satisfied) el.classList.add('satisfied');
      else if (open === 0) el.classList.add('violated');
      if (ci === sat.focus) el.classList.add('active');
      el.innerHTML = `<span class="clause-idx">c${ci + 1}</span>(${parts.join(' ∨ ')})`;
      box.appendChild(el);
    });

    const asg = $('sat-assignments');
    asg.innerHTML = '';
    if (!sat.vars.length) asg.innerHTML = '<span class="placeholder-text">No variables yet.</span>';
    sat.vars.forEach((v) => {
      const val = sat.assign.get(v);
      const b = document.createElement('span');
      b.className = `assignment-badge ${val === undefined ? 'val-unset' : `val-${val}`}`;
      b.textContent = `${v} = ${val === undefined ? '?' : bit(val)}`;
      asg.appendChild(b);
    });

    const s = sat.stats;
    $('sat-stats').innerHTML = [['Decisions', s.decisions], ['Propagations', s.propagations], ['Conflicts', s.conflicts]]
      .map(([k, v]) => `<div class="stat"><span class="stat-value">${v}</span><span class="stat-label">${k}</span></div>`).join('');

    drawSatTree();
  }

  // ==========================================
  // 2. CTL MODEL CHECKER
  // ==========================================

  // Guarded commands for two symmetric processes. `steps(i, j)` gives the
  // commands of process i, where j is the other process.
  function symmetric(steps) {
    return [0, 1].flatMap((i) => steps(i, 1 - i));
  }

  const MUTEX = { f: 'AG !(pc0 = CRIT & pc1 = CRIT)', desc: 'mutual exclusion' };

  const MC_SYSTEMS = {
    peterson: {
      blurb: 'Each process raises its flag, gives the turn to the other one, and waits while the other has its flag up and holds the turn. This is the real algorithm, so safety and liveness should both hold.',
      vars: ['pc0', 'pc1', 'flag0', 'flag1', 'turn'],
      init: { pc0: 'IDLE', pc1: 'IDLE', flag0: false, flag1: false, turn: 0 },
      actions: symmetric((i, j) => [
        { name: `P${i} request`, guard: (s) => s[`pc${i}`] === 'IDLE', update: (s) => ({ ...s, [`pc${i}`]: 'WAIT', [`flag${i}`]: true, turn: j }) },
        { name: `P${i} enter`, guard: (s) => s[`pc${i}`] === 'WAIT' && (!s[`flag${j}`] || s.turn === i), update: (s) => ({ ...s, [`pc${i}`]: 'CRIT' }) },
        { name: `P${i} exit`, guard: (s) => s[`pc${i}`] === 'CRIT', update: (s) => ({ ...s, [`pc${i}`]: 'IDLE', [`flag${i}`]: false }) }
      ]),
      caption: (s) => `${s.pc0[0]}${s.pc1[0]} t${s.turn}`,
      properties: [
        MUTEX,
        { f: 'AG (pc0 = WAIT -> AF pc0 = CRIT)', desc: 'P0 never starves' },
        { f: 'AG EF pc1 = CRIT', desc: 'P1 can always get in eventually' },
        { f: 'EF (pc0 = WAIT & pc1 = WAIT)', desc: 'both can be waiting at once' }
      ]
    },
    'flags-only': {
      blurb: 'Peterson without the turn variable: raise your flag, then wait until the other flag is down. Mutual exclusion still holds, but if both processes raise their flags at the same time, neither can ever move again.',
      vars: ['pc0', 'pc1', 'flag0', 'flag1'],
      init: { pc0: 'IDLE', pc1: 'IDLE', flag0: false, flag1: false },
      actions: symmetric((i, j) => [
        { name: `P${i} request`, guard: (s) => s[`pc${i}`] === 'IDLE', update: (s) => ({ ...s, [`pc${i}`]: 'WAIT', [`flag${i}`]: true }) },
        { name: `P${i} enter`, guard: (s) => s[`pc${i}`] === 'WAIT' && !s[`flag${j}`], update: (s) => ({ ...s, [`pc${i}`]: 'CRIT' }) },
        { name: `P${i} exit`, guard: (s) => s[`pc${i}`] === 'CRIT', update: (s) => ({ ...s, [`pc${i}`]: 'IDLE', [`flag${i}`]: false }) }
      ]),
      caption: (s) => `${s.pc0[0]}${s.pc1[0]}`,
      properties: [
        MUTEX,
        { f: 'AG (pc0 = WAIT -> AF pc0 = CRIT)', desc: 'P0 never starves' },
        { f: 'AG !deadlock', desc: 'no deadlocks' }
      ]
    },
    'naive-lock': {
      blurb: 'Each process waits until the other flag is down and only then raises its own. The gap between checking and setting lets both processes slip into the critical section together.',
      vars: ['pc0', 'pc1', 'flag0', 'flag1'],
      init: { pc0: 'IDLE', pc1: 'IDLE', flag0: false, flag1: false },
      actions: symmetric((i, j) => [
        { name: `P${i} sees flag${j} down`, guard: (s) => s[`pc${i}`] === 'IDLE' && !s[`flag${j}`], update: (s) => ({ ...s, [`pc${i}`]: 'READY' }) },
        { name: `P${i} raises flag and enters`, guard: (s) => s[`pc${i}`] === 'READY', update: (s) => ({ ...s, [`pc${i}`]: 'CRIT', [`flag${i}`]: true }) },
        { name: `P${i} exit`, guard: (s) => s[`pc${i}`] === 'CRIT', update: (s) => ({ ...s, [`pc${i}`]: 'IDLE', [`flag${i}`]: false }) }
      ]),
      caption: (s) => `${s.pc0[0]}${s.pc1[0]}`,
      properties: [
        MUTEX,
        { f: 'EF (pc0 = CRIT & pc1 = CRIT)', desc: 'the bad state is reachable' }
      ]
    },
    traffic: {
      blurb: 'A four-phase controller for a crossing. The north-south and east-west lights take turns, with a yellow phase in between.',
      vars: ['ns', 'ew'],
      init: { ns: 'GREEN', ew: 'RED' },
      actions: [
        { name: 'NS to yellow', guard: (s) => s.ns === 'GREEN', update: (s) => ({ ...s, ns: 'YELLOW' }) },
        { name: 'NS to red, EW to green', guard: (s) => s.ns === 'YELLOW', update: () => ({ ns: 'RED', ew: 'GREEN' }) },
        { name: 'EW to yellow', guard: (s) => s.ew === 'GREEN', update: (s) => ({ ...s, ew: 'YELLOW' }) },
        { name: 'EW to red, NS to green', guard: (s) => s.ew === 'YELLOW', update: () => ({ ns: 'GREEN', ew: 'RED' }) }
      ],
      caption: (s) => `${s.ns[0]}/${s.ew[0]}`,
      properties: [
        { f: 'AG !(ns = GREEN & ew = GREEN)', desc: 'never both green' },
        { f: 'AG (ns = GREEN -> AF ew = GREEN)', desc: 'east-west always gets a green' },
        { f: 'AG (ns = RED -> AX ns = GREEN)', desc: 'red goes straight to green (false)' }
      ]
    }
  };

  // Breadth-first exploration of the reachable states. States without any
  // enabled command get a self-loop so the transition relation stays total.
  function buildKripke(sys) {
    const key = (s) => sys.vars.map((v) => String(s[v])).join('|');
    const states = [];
    const index = new Map();
    const edges = [];
    const add = (vals, depth) => {
      const k = key(vals);
      if (index.has(k)) return index.get(k);
      const id = states.length;
      index.set(k, id);
      states.push({ id, name: `S${id}`, vals: { ...vals }, depth });
      return id;
    };
    add(sys.init, 0);
    for (let i = 0; i < states.length; i++) {
      const s = states[i];
      let enabled = 0;
      for (const act of sys.actions) {
        if (!act.guard(s.vals)) continue;
        enabled++;
        edges.push({ from: i, to: add(act.update(s.vals), s.depth + 1), label: act.name });
      }
      s.deadlock = enabled === 0;
      if (s.deadlock) edges.push({ from: i, to: i, label: 'deadlock: stays here forever', stutter: true });
    }
    states.forEach((s) => { s.vals.deadlock = s.deadlock; });
    const vars = [...sys.vars, 'deadlock'];
    const succ = states.map(() => []);
    edges.forEach((e) => { if (!succ[e.from].includes(e.to)) succ[e.from].push(e.to); });
    const domains = {};
    vars.forEach((v) => { domains[v] = new Set(states.map((s) => String(s.vals[v]))); });
    const bools = new Set(vars.filter((v) => typeof states[0].vals[v] === 'boolean'));
    return { states, edges, succ, vars, domains, bools };
  }

  const TEMPORAL = ['AX', 'EX', 'AF', 'EF', 'AG', 'EG'];

  function parseCtl(src, K) {
    const ts = new TokenStream(src);
    const iff = () => {
      let a = imp();
      while (ts.acceptOp('<->')) a = { k: 'iff', a, b: imp() };
      return a;
    };
    const imp = () => {
      const a = or();
      return ts.acceptOp('->') ? { k: 'imp', a, b: imp() } : a;
    };
    const or = () => {
      let a = and();
      while (ts.acceptOp('|')) a = { k: 'or', a, b: and() };
      return a;
    };
    const and = () => {
      let a = unary();
      while (ts.acceptOp('&')) a = { k: 'and', a, b: unary() };
      return a;
    };
    const unary = () => {
      if (ts.acceptOp('!')) return { k: 'not', a: unary() };
      const t = ts.peek();
      if (t.t === 'id' && TEMPORAL.includes(t.v)) {
        ts.next();
        return { k: t.v, a: unary() };
      }
      if (t.t === 'id' && (t.v === 'A' || t.v === 'E') && ts.isOp('[', 1)) {
        ts.next();
        ts.next();
        const a = iff();
        if (!ts.isId('U')) ts.fail('Expected "U"');
        ts.next();
        const b = iff();
        ts.expectOp(']');
        return { k: `${t.v}U`, a, b };
      }
      return atom();
    };
    const atom = () => {
      if (ts.acceptOp('(')) {
        const a = iff();
        ts.expectOp(')');
        return a;
      }
      const t = ts.next();
      if (t.t !== 'id') { ts.i--; ts.fail('Expected a proposition'); }
      if (t.v === 'true') return { k: 'true' };
      if (t.v === 'false') return { k: 'false' };
      if (!K.vars.includes(t.v)) throw new Error(`Unknown variable "${t.v}". This model has: ${K.vars.join(', ')}`);
      const isBool = K.bools.has(t.v);
      let op = '=';
      let val = 'true';
      if (ts.isOp('=') || ts.isOp('!=')) {
        op = ts.next().v;
        const neg = ts.acceptOp('-');
        const vt = ts.next();
        if (vt.t !== 'id' && vt.t !== 'num') { ts.i--; ts.fail('Expected a value'); }
        val = (neg ? '-' : '') + String(vt.v);
      } else if (!isBool) {
        throw new Error(`"${t.v}" is not a boolean. Compare it with a value, for example ${t.v} = ${[...K.domains[t.v]][0]}`);
      }
      if (isBool && val !== 'true' && val !== 'false') throw new Error(`${t.v} is a boolean, so compare it with true or false`);
      if (!isBool && !K.domains[t.v].has(val)) throw new Error(`${t.v} is never ${val}. Its values are: ${[...K.domains[t.v]].join(', ')}`);
      return { k: 'atom', v: t.v, op, val };
    };
    const f = iff();
    ts.end();
    return f;
  }

  const CTL_PREC = { iff: 1, imp: 2, or: 3, and: 4 };
  const CTL_SYM = { iff: ' ↔ ', imp: ' → ', or: ' ∨ ', and: ' ∧ ' };

  function ctlPrint(f, prec = 0) {
    switch (f.k) {
      case 'true':
      case 'false':
        return f.k;
      case 'atom':
        if (f.val === 'true' || f.val === 'false') return (f.op === '=') === (f.val === 'true') ? f.v : `¬${f.v}`;
        return `${f.v} ${f.op === '=' ? '=' : '≠'} ${f.val}`;
      case 'not': {
        const inner = ctlPrint(f.a, 5);
        return '¬' + (f.a.k === 'atom' && inner.includes(' ') ? `(${inner})` : inner);
      }
      case 'AU':
      case 'EU':
        return `${f.k[0]}[${ctlPrint(f.a)} U ${ctlPrint(f.b)}]`;
      case 'iff':
      case 'imp':
      case 'or':
      case 'and': {
        const p = CTL_PREC[f.k];
        const rightAssoc = f.k === 'imp';
        const s = ctlPrint(f.a, rightAssoc ? p + 1 : p) + CTL_SYM[f.k] + ctlPrint(f.b, rightAssoc ? p : p + 1);
        return p < prec ? `(${s})` : s;
      }
      default:
        return `${f.k} ${ctlPrint(f.a, 5)}`;
    }
  }

  // Labelling algorithm: returns, for every state, whether it satisfies f.
  // If `trace` is given, every subformula is appended with its result.
  function checkCtl(K, f, trace) {
    const n = K.states.length;
    const succ = K.succ;
    const fill = (b) => new Array(n).fill(b);
    const until = (a, b, quant) => {
      const z = b.slice();
      for (let changed = true; changed;) {
        changed = false;
        for (let i = 0; i < n; i++) {
          if (!z[i] && a[i] && succ[i][quant]((j) => z[j])) { z[i] = true; changed = true; }
        }
      }
      return z;
    };
    const globally = (a) => {
      const z = a.slice();
      for (let changed = true; changed;) {
        changed = false;
        for (let i = 0; i < n; i++) {
          if (z[i] && !succ[i].some((j) => z[j])) { z[i] = false; changed = true; }
        }
      }
      return z;
    };
    const rec = (g) => {
      let r;
      switch (g.k) {
        case 'true': r = fill(true); break;
        case 'false': r = fill(false); break;
        case 'atom': r = K.states.map((s) => (String(s.vals[g.v]) === g.val) === (g.op === '=')); break;
        case 'not': r = rec(g.a).map((x) => !x); break;
        case 'and': { const a = rec(g.a); const b = rec(g.b); r = a.map((x, i) => x && b[i]); break; }
        case 'or': { const a = rec(g.a); const b = rec(g.b); r = a.map((x, i) => x || b[i]); break; }
        case 'imp': { const a = rec(g.a); const b = rec(g.b); r = a.map((x, i) => !x || b[i]); break; }
        case 'iff': { const a = rec(g.a); const b = rec(g.b); r = a.map((x, i) => x === b[i]); break; }
        case 'EX': { const a = rec(g.a); r = succ.map((ss) => ss.some((j) => a[j])); break; }
        case 'AX': { const a = rec(g.a); r = succ.map((ss) => ss.every((j) => a[j])); break; }
        case 'EU': { const a = rec(g.a); const b = rec(g.b); r = until(a, b, 'some'); break; }
        case 'AU': { const a = rec(g.a); const b = rec(g.b); r = until(a, b, 'every'); break; }
        case 'EF': r = until(fill(true), rec(g.a), 'some'); break;
        case 'AF': r = until(fill(true), rec(g.a), 'every'); break;
        case 'EG': r = globally(rec(g.a)); break;
        case 'AG': r = until(fill(true), rec(g.a).map((x) => !x), 'some').map((x) => !x); break;
        default: throw new Error(`Unknown operator ${g.k}`);
      }
      if (trace) trace.push({ f: g, sat: r });
      return r;
    };
    return rec(f);
  }

  // Shortest path from `from` to a state where `target` holds, only leaving states where `through` holds.
  function bfsPath(K, from, target, through) {
    const prev = new Map([[from, -1]]);
    const queue = [from];
    while (queue.length) {
      const s = queue.shift();
      if (target(s)) {
        const path = [];
        for (let x = s; x !== -1; x = prev.get(x)) path.unshift(x);
        return path;
      }
      if (through && !through(s)) continue;
      for (const j of K.succ[s]) {
        if (!prev.has(j)) { prev.set(j, s); queue.push(j); }
      }
    }
    return null;
  }

  // Walks successors inside `inside` until a state repeats. Works for EG sets,
  // where every state has a successor in the set.
  function lasso(K, from, inside) {
    const path = [from];
    const seen = new Map([[from, 0]]);
    for (let s = from; ;) {
      const next = K.succ[s].find((j) => inside[j]);
      if (next === undefined) return { path, loop: -1 };
      path.push(next);
      if (seen.has(next)) return { path, loop: seen.get(next) };
      seen.set(next, path.length - 1);
      s = next;
    }
  }

  // Appends trace b to trace a, where b starts at the last state of a.
  function joinTraces(a, b) {
    const offset = a.path.length - 1;
    return { path: a.path.concat(b.path.slice(1)), loop: b.loop >= 0 ? b.loop + offset : a.loop };
  }

  // A path starting at s that shows why f is false there.
  function whyFails(K, f, s) {
    const here = { path: [s], loop: -1 };
    switch (f.k) {
      case 'AG': {
        const a = checkCtl(K, f.a);
        const p = bfsPath(K, s, (x) => !a[x]);
        return p ? joinTraces({ path: p, loop: -1 }, whyFails(K, f.a, p[p.length - 1])) : here;
      }
      case 'AF': {
        const z = checkCtl(K, { k: 'EG', a: { k: 'not', a: f.a } });
        return z[s] ? lasso(K, s, z) : here;
      }
      case 'AX': {
        const a = checkCtl(K, f.a);
        const j = K.succ[s].find((x) => !a[x]);
        return j === undefined ? here : joinTraces({ path: [s, j], loop: -1 }, whyFails(K, f.a, j));
      }
      case 'imp':
        return whyFails(K, f.b, s);
      case 'and':
        return whyFails(K, checkCtl(K, f.a)[s] ? f.b : f.a, s);
      case 'not':
        return whyHolds(K, f.a, s);
      default:
        return here;
    }
  }

  // A path starting at s that shows why f is true there.
  function whyHolds(K, f, s) {
    const here = { path: [s], loop: -1 };
    switch (f.k) {
      case 'EF':
      case 'EU': {
        const b = checkCtl(K, f.k === 'EF' ? f.a : f.b);
        const a = f.k === 'EU' ? checkCtl(K, f.a) : null;
        const p = bfsPath(K, s, (x) => b[x], a ? (x) => a[x] : null);
        return p ? joinTraces({ path: p, loop: -1 }, whyHolds(K, f.k === 'EF' ? f.a : f.b, p[p.length - 1])) : here;
      }
      case 'EG':
        return lasso(K, s, checkCtl(K, f));
      case 'EX': {
        const a = checkCtl(K, f.a);
        const j = K.succ[s].find((x) => a[x]);
        return j === undefined ? here : joinTraces({ path: [s, j], loop: -1 }, whyHolds(K, f.a, j));
      }
      case 'or':
        return whyHolds(K, checkCtl(K, f.a)[s] ? f.a : f.b, s);
      case 'not':
        return whyFails(K, f.a, s);
      default:
        return here;
    }
  }

  function verifyCtl(K, f) {
    const satSet = checkCtl(K, f);
    const holds = satSet[0];
    const ex = holds ? whyHolds(K, f, 0) : whyFails(K, f, 0);
    return { holds, sat: satSet, trace: ex.path.length > 1 ? { ...ex, kind: holds ? 'witness' : 'counterexample' } : null };
  }

  function layoutKripke(K) {
    const layers = [];
    K.states.forEach((s) => { (layers[s.depth] = layers[s.depth] || []).push(s.id); });
    const preds = K.states.map(() => []);
    K.edges.forEach((e) => { if (e.from !== e.to) preds[e.to].push(e.from); });
    const pos = [];
    layers.forEach((layer, d) => {
      if (d > 0) {
        const bary = (id) => {
          const ps = preds[id].filter((p) => K.states[p].depth === d - 1);
          return ps.length ? ps.reduce((acc, p) => acc + pos[p].x, 0) / ps.length : 0;
        };
        layer.sort((a, b) => bary(a) - bary(b));
      }
      layer.forEach((id, k) => { pos[id] = { x: (k - (layer.length - 1) / 2) * 125, y: d * 105 }; });
    });
    return pos;
  }

  const mc = {
    key: 'peterson', sys: null, K: null, pos: [],
    current: 0, highlight: null, trace: null, status: 'IDLE',
    steps: null, stepIdx: 0, formula: null, timer: null
  };
  let mcLog = NULL_LOGGER;
  let mcSpeed = () => 600;

  function stateValues(s) {
    return mc.sys.vars.map((v) => `${v}=${s.vals[v]}`).join(', ');
  }

  function mcLoadSystem() {
    mc.key = $('mc-system').value;
    mc.sys = MC_SYSTEMS[mc.key];
    mc.K = buildKripke(mc.sys);
    mc.pos = layoutKripke(mc.K);
    $('mc-blurb').textContent = mc.sys.blurb;
    const sel = $('mc-property');
    sel.innerHTML = '';
    mc.sys.properties.forEach((p, i) => {
      const opt = document.createElement('option');
      opt.value = String(i);
      opt.textContent = `${p.f}   (${p.desc})`;
      sel.appendChild(opt);
    });
    const custom = document.createElement('option');
    custom.value = 'custom';
    custom.textContent = 'Write your own formula...';
    sel.appendChild(custom);
    mcPropertyChanged();
    mcReset();
    const dead = mc.K.states.filter((s) => s.deadlock).map((s) => s.name);
    mcLog.log(`Built the model: ${mc.K.states.length} reachable states and ${mc.K.edges.filter((e) => !e.stutter).length} transitions.`, 'info');
    if (dead.length) mcLog.log(`Deadlock found in ${dead.join(', ')}. A self-loop was added so the model stays total.`, 'warning');
  }

  function mcPropertyChanged() {
    const custom = $('mc-property').value === 'custom';
    $('mc-custom').classList.toggle('hidden', !custom);
    $('mc-error').textContent = '';
    if (custom && !$('mc-custom').value) $('mc-custom').value = mc.sys.properties[0].f;
    mcClearResult();
    renderMc();
  }

  function mcFormula() {
    const sel = $('mc-property').value;
    const src = sel === 'custom' ? $('mc-custom').value : mc.sys.properties[Number(sel)].f;
    try {
      $('mc-error').textContent = '';
      return parseCtl(src, mc.K);
    } catch (e) {
      $('mc-error').textContent = e.message;
      return null;
    }
  }

  function mcClearResult() {
    mc.highlight = null;
    mc.trace = null;
    mc.steps = null;
    mc.status = 'IDLE';
    const v = $('mc-verdict');
    v.className = 'verdict-box hidden';
    v.innerHTML = '';
  }

  function mcReset() {
    stopMcSim();
    mc.current = 0;
    mcClearResult();
    mcLog.clear();
    renderMc();
  }

  function describeTrace(trace) {
    const names = trace.path.map((i) => mc.K.states[i].name);
    if (trace.loop < 0) return names.join(' → ');
    const prefix = names.slice(0, trace.loop);
    const cycle = names.slice(trace.loop);
    return `${prefix.length ? prefix.join(' → ') + ' → ' : ''}(${cycle.join(' → ')}) repeated forever`;
  }

  function edgeLabel(a, b) {
    return mc.K.edges.filter((e) => e.from === a && e.to === b).map((e) => e.label).join(' / ');
  }

  function mcShowVerdict(f) {
    const res = verifyCtl(mc.K, f);
    const n = mc.K.states.length;
    const count = res.sat.filter(Boolean).length;
    mc.highlight = res.sat;
    mc.trace = res.trace;
    mc.status = res.holds ? 'HOLDS' : 'FAILS';
    mc.steps = null;

    const formula = ctlPrint(f);
    const box = $('mc-verdict');
    box.className = `verdict-box ${res.holds ? 'verdict-ok' : 'verdict-bad'}`;
    let html = `<strong>${res.holds ? '✓ Holds' : '✗ Fails'}</strong> in the initial state S0. `
      + (count ? `The formula is true in ${count} of ${n} reachable states, shaded green in the graph.` : `The formula is false in all ${n} reachable states.`);
    if (res.trace) {
      html += `<div class="verdict-trace"><span>${res.holds ? 'Witness' : 'Counterexample'}:</span> ${escapeHtml(describeTrace(res.trace))}</div>`;
    }
    box.innerHTML = html;

    mcLog.log(`${formula}: ${res.holds ? 'holds' : 'fails'} in S0 (true in ${count}/${n} states).`, res.holds ? 'success' : 'danger');
    if (res.trace) {
      mcLog.log(`${res.holds ? 'Witness' : 'Counterexample'}, starting in S0:`, res.holds ? 'success' : 'danger');
      const p = res.trace.path;
      p.forEach((id, k) => {
        const s = mc.K.states[id];
        if (k > 0) mcLog.log(`  ${edgeLabel(p[k - 1], id)} → ${s.name}`, 'info');
        else mcLog.log(`  ${s.name}: ${stateValues(s)}`, 'info');
      });
      if (res.trace.loop >= 0) mcLog.log(`  ...and from here the run cycles back to ${mc.K.states[p[res.trace.loop]].name} forever.`, 'warning');
    }
    renderMc();
  }

  function mcVerify() {
    stopMcSim();
    const f = mcFormula();
    if (!f) return;
    mcShowVerdict(f);
  }

  function mcStep() {
    stopMcSim();
    if (!mc.steps) {
      const f = mcFormula();
      if (!f) return;
      const trace = [];
      checkCtl(mc.K, f, trace);
      const seen = new Set();
      mc.steps = trace.filter((t) => {
        const k = ctlPrint(t.f);
        if (seen.has(k)) return false;
        seen.add(k);
        return true;
      });
      mc.stepIdx = 0;
      mc.formula = f;
      mc.trace = null;
      $('mc-verdict').className = 'verdict-box hidden';
      mcLog.log(`Labelling states bottom-up, one subformula per step: ${ctlPrint(f)}`, 'step');
    }
    const st = mc.steps[mc.stepIdx++];
    const names = mc.K.states.filter((s) => st.sat[s.id]).map((s) => s.name);
    mc.highlight = st.sat;
    mc.status = 'CHECKING';
    mcLog.log(`Sat(${ctlPrint(st.f)}) = {${names.join(', ') || '∅'}}`, 'info');
    if (mc.stepIdx >= mc.steps.length) mcShowVerdict(mc.formula);
    else renderMc();
  }

  function mcMoveTo(id, how) {
    mc.current = id;
    mcLog.log(`${how} → ${mc.K.states[id].name} (${stateValues(mc.K.states[id])})`, 'step');
    renderMc();
  }

  function mcClickState(id) {
    if (mc.K.succ[mc.current].includes(id)) {
      stopMcSim();
      mcMoveTo(id, edgeLabel(mc.current, id));
    } else {
      mcLog.log(`${mc.K.states[id].name} is not one step away from ${mc.K.states[mc.current].name}. Pick a highlighted move instead.`, 'warning');
    }
  }

  function toggleMcSim() {
    if (mc.timer) { stopMcSim(); return; }
    $('btn-mc-simulate').textContent = 'Pause';
    mcLog.log(`Random walk from ${mc.K.states[mc.current].name}.`, 'step');
    mc.timer = setInterval(mcSimTick, mcSpeed());
  }

  function mcSimTick() {
    const out = mc.K.edges.filter((e) => e.from === mc.current);
    const e = out[Math.floor(Math.random() * out.length)];
    mcMoveTo(e.to, e.label);
  }

  function stopMcSim() {
    if (mc.timer) clearInterval(mc.timer);
    mc.timer = null;
    const btn = typeof document !== 'undefined' && $('btn-mc-simulate');
    if (btn) btn.textContent = 'Simulate';
  }

  function controlPoint(a, b, offset) {
    const dx = b.x - a.x;
    const dy = b.y - a.y;
    const len = Math.hypot(dx, dy) || 1;
    return { x: (a.x + b.x) / 2 - (dy / len) * offset, y: (a.y + b.y) / 2 + (dx / len) * offset };
  }

  // How many other states the curve a -> b (bent by `offset`) passes through.
  function curveHits(a, b, offset, others, r) {
    const c = controlPoint(a, b, offset);
    let hits = 0;
    others.forEach((p) => {
      for (let t = 0.05; t < 1; t += 0.05) {
        const u = 1 - t;
        const x = u * u * a.x + 2 * u * t * c.x + t * t * b.x;
        const y = u * u * a.y + 2 * u * t * c.y + t * t * b.y;
        if (Math.hypot(x - p.x, y - p.y) < r + 6) { hits++; return; }
      }
    });
    return hits;
  }

  function quadPath(a, b, offset, r) {
    const c = controlPoint(a, b, offset);
    const shift = (p, q, dist) => {
      const l = Math.hypot(q.x - p.x, q.y - p.y) || 1;
      return { x: p.x + ((q.x - p.x) / l) * dist, y: p.y + ((q.y - p.y) / l) * dist };
    };
    const s = shift(a, c, r);
    const e = shift(b, c, r + 2);
    return `M ${s.x.toFixed(1)} ${s.y.toFixed(1)} Q ${c.x.toFixed(1)} ${c.y.toFixed(1)} ${e.x.toFixed(1)} ${e.y.toFixed(1)}`;
  }

  function drawMc() {
    const svg = $('mc-graph-svg');
    svg.innerHTML = '';
    const { K, pos } = mc;
    const R = 20;
    const xs = pos.map((p) => p.x);
    const ys = pos.map((p) => p.y);
    const minX = Math.min(...xs) - 80;
    const minY = Math.min(...ys) - 70;
    const width = Math.max(Math.max(...xs) + 80 - minX, 360);
    const height = Math.max(...ys) + 60 - minY;
    svg.setAttribute('viewBox', `${minX} ${minY} ${width} ${height}`);

    const defs = svgEl('defs', {}, svg);
    ['muted', 'current', 'counterexample', 'witness'].forEach((name) => {
      const m = svgEl('marker', { id: `mc-arrow-${name}`, viewBox: '0 0 10 10', refX: 9, refY: 5, markerUnits: 'userSpaceOnUse', markerWidth: name === 'muted' ? 9 : 12, markerHeight: name === 'muted' ? 9 : 12, orient: 'auto-start-reverse' }, defs);
      svgEl('path', { d: 'M 0 0 L 10 5 L 0 10 z', class: `arrow-${name}` }, m);
    });

    const onPath = new Set(mc.trace ? mc.trace.path : []);
    const pathEdges = new Set();
    if (mc.trace) for (let i = 0; i + 1 < mc.trace.path.length; i++) pathEdges.add(`${mc.trace.path[i]}>${mc.trace.path[i + 1]}`);

    const pairs = new Map();
    K.edges.forEach((e) => {
      const k = `${e.from}>${e.to}`;
      if (!pairs.has(k)) pairs.set(k, { from: e.from, to: e.to, labels: [] });
      pairs.get(k).labels.push(e.label);
    });
    pairs.forEach((pe, k) => {
      const a = pos[pe.from];
      const b = pos[pe.to];
      let d;
      if (pe.from === pe.to) {
        d = `M ${a.x + 12} ${a.y - 16} C ${a.x + 42} ${a.y - 64}, ${a.x - 42} ${a.y - 64}, ${a.x - 13} ${a.y - 18}`;
      } else {
        const ds = K.states[pe.to].depth - K.states[pe.from].depth;
        const reverse = pairs.has(`${pe.to}>${pe.from}`);
        const base = ds === 1 ? (reverse ? 16 : 0) : 24 + 14 * Math.abs(ds);
        const others = pos.filter((p, i) => i !== pe.from && i !== pe.to);
        // Try bending the edge further, on either side, until it clears every other state.
        const candidates = ds === 1 && !reverse ? [0, 30, -30, 55, -55] : [base, -base, base * 1.7, -base * 1.7, base * 2.4, -base * 2.4];
        let offset = candidates[0];
        let best = Infinity;
        for (const o of candidates) {
          const h = curveHits(a, b, o, others, R);
          if (h < best) { best = h; offset = o; }
          if (h === 0) break;
        }
        d = quadPath(a, b, offset, R);
      }
      let cls = 'mc-edge-path';
      let marker = 'muted';
      if (pathEdges.has(k)) { cls += ` ${mc.trace.kind}`; marker = mc.trace.kind; } else if (pe.from === mc.current) { cls += ' current'; marker = 'current'; }
      const path = svgEl('path', { d, class: cls, 'marker-end': `url(#mc-arrow-${marker})` }, svg);
      svgEl('title', {}, path).textContent = `${K.states[pe.from].name} → ${K.states[pe.to].name}: ${pe.labels.join(', ')}`;
    });

    const nextStates = new Set(K.succ[mc.current]);
    K.states.forEach((s) => {
      const p = pos[s.id];
      const g = svgEl('g', { class: `mc-node${nextStates.has(s.id) && s.id !== mc.current ? ' next' : ''}` }, svg);
      const cls = ['mc-node-circle'];
      if (s.id === 0) cls.push('init');
      if (mc.highlight && mc.highlight[s.id]) cls.push('sat');
      if (s.deadlock) cls.push('deadlock');
      if (onPath.has(s.id)) cls.push(mc.trace.kind);
      if (s.id === mc.current) cls.push('current');
      svgEl('circle', { cx: p.x, cy: p.y, r: R, class: cls.join(' ') }, g);
      svgEl('text', { x: p.x, y: p.y + 4, class: 'mc-node-text' }, g).textContent = s.name;
      svgEl('text', { x: p.x, y: p.y + R + 14, class: 'mc-node-caption' }, g).textContent = mc.sys.caption(s.vals);
      svgEl('title', {}, g).textContent = `${s.name}: ${stateValues(s)}${s.deadlock ? ' (deadlock)' : ''}`;
      g.addEventListener('click', () => mcClickState(s.id));
    });

    // Fit the view to what was actually drawn, curves included. getBBox is
    // empty while the tab is hidden, so the node-based box above is the fallback.
    const bb = svg.getBBox();
    if (bb.width > 0) {
      const w = Math.max(bb.width + 40, 360);
      svg.setAttribute('viewBox', `${bb.x + bb.width / 2 - w / 2} ${bb.y - 20} ${w} ${bb.height + 40}`);
    }
  }

  function renderMc() {
    setBadge($('mc-status'), mc.status, { HOLDS: 'badge-satisfied', FAILS: 'badge-unsat', CHECKING: 'badge-active' });
    const s = mc.K.states[mc.current];
    $('mc-current-name').textContent = s.name;
    const vars = $('mc-state-vars');
    vars.innerHTML = '';
    [...mc.sys.vars, ...(s.deadlock ? ['deadlock'] : [])].forEach((v) => {
      const row = document.createElement('div');
      row.className = 'state-var-row';
      row.innerHTML = `<span>${escapeHtml(v)}</span><span class="state-val">${escapeHtml(s.vals[v])}</span>`;
      vars.appendChild(row);
    });
    const moves = $('mc-moves');
    moves.innerHTML = '';
    const out = mc.K.edges.filter((e) => e.from === mc.current && !e.stutter);
    if (!out.length) moves.innerHTML = '<span class="placeholder-text">No moves. This state is a deadlock.</span>';
    out.forEach((e) => {
      const b = document.createElement('button');
      b.type = 'button';
      b.className = 'move-btn';
      b.textContent = `${e.label} → ${mc.K.states[e.to].name}`;
      b.addEventListener('click', () => { stopMcSim(); mcMoveTo(e.to, e.label); });
      moves.appendChild(b);
    });
    drawMc();
  }

  // ==========================================
  // 3. HOARE LOGIC: WEAKEST PRECONDITIONS
  // ==========================================
  function parseExpr(src) {
    const ts = new TokenStream(src);
    const CMP = ['=', '!=', '<', '<=', '>', '>='];
    const imp = () => {
      const a = or();
      return ts.acceptOp('->') ? { k: 'imp', a, b: imp() } : a;
    };
    const or = () => {
      let a = and();
      while (ts.acceptOp('|')) a = { k: 'or', a, b: and() };
      return a;
    };
    const and = () => {
      let a = not();
      while (ts.acceptOp('&')) a = { k: 'and', a, b: not() };
      return a;
    };
    const not = () => (ts.acceptOp('!') ? { k: 'not', a: not() } : cmp());
    const cmp = () => {
      const a = sum();
      const t = ts.peek();
      if (t.t === 'op' && CMP.includes(t.v)) {
        ts.next();
        return { k: 'cmp', op: t.v, a, b: sum() };
      }
      return a;
    };
    const sum = () => {
      let a = prod();
      for (;;) {
        if (ts.acceptOp('+')) a = { k: 'bin', op: '+', a, b: prod() };
        else if (ts.acceptOp('-')) a = { k: 'bin', op: '-', a, b: prod() };
        else return a;
      }
    };
    const prod = () => {
      let a = neg();
      for (;;) {
        if (ts.acceptOp('*')) a = { k: 'bin', op: '*', a, b: neg() };
        else if (ts.acceptOp('/')) a = { k: 'bin', op: '/', a, b: neg() };
        else return a;
      }
    };
    const neg = () => (ts.acceptOp('-') ? { k: 'neg', a: neg() } : primary());
    const primary = () => {
      if (ts.acceptOp('(')) {
        const e = imp();
        ts.expectOp(')');
        return e;
      }
      const t = ts.next();
      if (t.t === 'num') return { k: 'num', v: t.v };
      if (t.t === 'id') return t.v === 'true' || t.v === 'false' ? { k: 'bool', v: t.v === 'true' } : { k: 'var', v: t.v };
      ts.i--;
      return ts.fail('Expected a number, a variable or "("');
    };
    const e = imp();
    ts.end();
    return e;
  }

  function typeOf(e) {
    const want = (x, t) => {
      if (typeOf(x) !== t) throw new Error(`"${printExpr(x)}" should be ${t === 'bool' ? 'a condition' : 'a number'}`);
    };
    switch (e.k) {
      case 'num':
      case 'var':
        return 'int';
      case 'bool':
        return 'bool';
      case 'neg':
        want(e.a, 'int');
        return 'int';
      case 'bin':
        want(e.a, 'int');
        want(e.b, 'int');
        return 'int';
      case 'cmp':
        if (e.op === '=' || e.op === '!=') want(e.b, typeOf(e.a));
        else { want(e.a, 'int'); want(e.b, 'int'); }
        return 'bool';
      case 'not':
        want(e.a, 'bool');
        return 'bool';
      default:
        want(e.a, 'bool');
        want(e.b, 'bool');
        return 'bool';
    }
  }

  function subst(e, x, r) {
    switch (e.k) {
      case 'var': return e.v === x ? r : e;
      case 'num':
      case 'bool': return e;
      case 'neg':
      case 'not': return { ...e, a: subst(e.a, x, r) };
      default: return { ...e, a: subst(e.a, x, r), b: subst(e.b, x, r) };
    }
  }

  function freeVars(e, out = new Set()) {
    if (e.k === 'var') out.add(e.v);
    if (e.a) freeVars(e.a, out);
    if (e.b) freeVars(e.b, out);
    return out;
  }

  function evalExpr(e, env) {
    switch (e.k) {
      case 'num':
      case 'bool': return e.v;
      case 'var': return env[e.v];
      case 'neg': return -evalExpr(e.a, env);
      case 'not': return !evalExpr(e.a, env);
      case 'and': return evalExpr(e.a, env) && evalExpr(e.b, env);
      case 'or': return evalExpr(e.a, env) || evalExpr(e.b, env);
      case 'imp': return !evalExpr(e.a, env) || evalExpr(e.b, env);
      case 'bin': {
        const a = evalExpr(e.a, env);
        const b = evalExpr(e.b, env);
        if (e.op === '+') return a + b;
        if (e.op === '-') return a - b;
        if (e.op === '*') return a * b;
        return b === 0 ? NaN : a / b;
      }
      case 'cmp': {
        const a = evalExpr(e.a, env);
        const b = evalExpr(e.b, env);
        if (Number.isNaN(a) || Number.isNaN(b)) return false;
        switch (e.op) {
          case '=': return typeof a === 'number' ? Math.abs(a - b) < 1e-9 : a === b;
          case '!=': return typeof a === 'number' ? Math.abs(a - b) >= 1e-9 : a !== b;
          case '<': return a < b;
          case '<=': return a <= b;
          case '>': return a > b;
          default: return a >= b;
        }
      }
      default: throw new Error(`Unknown expression ${e.k}`);
    }
  }

  const EXPR_PREC = { imp: 1, or: 2, and: 3, not: 4, cmp: 5 };
  const BIN_PREC = { '+': 6, '-': 6, '*': 7, '/': 7 };
  const EXPR_SYM = { imp: ' ⇒ ', or: ' ∨ ', and: ' ∧ ', '!=': ' ≠ ', '<=': ' ≤ ', '>=': ' ≥ ' };

  function printExpr(e, prec = 0) {
    let s;
    let p;
    switch (e.k) {
      case 'num':
      case 'bool':
      case 'var':
        return String(e.v);
      case 'neg':
        p = 8;
        s = '-' + printExpr(e.a, 9);
        break;
      case 'not':
        p = 4;
        s = '¬' + (['var', 'bool', 'not'].includes(e.a.k) ? printExpr(e.a) : `(${printExpr(e.a)})`);
        break;
      case 'cmp':
        p = 5;
        s = printExpr(e.a, 6) + (EXPR_SYM[e.op] || ` ${e.op} `) + printExpr(e.b, 6);
        break;
      case 'bin':
        p = BIN_PREC[e.op];
        s = printExpr(e.a, p) + ` ${e.op} ` + printExpr(e.b, p + 1);
        break;
      default: {
        p = EXPR_PREC[e.k];
        const rightAssoc = e.k === 'imp';
        s = printExpr(e.a, rightAssoc ? p + 1 : p) + EXPR_SYM[e.k] + printExpr(e.b, rightAssoc ? p : p + 1);
      }
    }
    return p < prec ? `(${s})` : s;
  }

  const Stmt = {
    assign: (x, e) => ({ k: 'assign', x, e: parseExpr(e) }),
    if: (c, t, f) => ({ k: 'if', cond: parseExpr(c), then: t, else: f }),
    while: (c, body) => ({ k: 'while', cond: parseExpr(c), body }),
    seq: (...list) => ({ k: 'seq', list })
  };

  const HL_PRESETS = {
    abs: {
      hint: 'One if-statement. Change the postcondition to y > 0 and see which branch breaks.',
      pre: 'true',
      post: 'y >= 0',
      prog: Stmt.if('x < 0', Stmt.assign('y', '-x'), Stmt.assign('y', 'x'))
    },
    swap: {
      hint: 'This swap forgets a temporary variable. Check the VC to get concrete values that break it.',
      pre: 'x = a & y = b',
      post: 'x = b & y = a',
      prog: Stmt.seq(Stmt.assign('x', 'y'), Stmt.assign('y', 'x'))
    },
    sum: {
      hint: 'Try deleting "& i <= N" from the invariant. The exit VC fails, and the counterexample shows why that part matters.',
      pre: 'N >= 0',
      inv: 's = i * (i + 1) / 2 & i <= N',
      post: 's = N * (N + 1) / 2',
      prog: Stmt.seq(Stmt.assign('i', '0'), Stmt.assign('s', '0'),
        Stmt.while('i < N', Stmt.seq(Stmt.assign('i', 'i + 1'), Stmt.assign('s', 's + i'))))
    },
    div: {
      hint: 'Division by repeated subtraction. Try dropping "& r >= 0" from the invariant.',
      pre: 'x >= 0 & y > 0',
      inv: 'x = q * y + r & r >= 0',
      post: 'x = q * y + r & 0 <= r & r < y',
      prog: Stmt.seq(Stmt.assign('q', '0'), Stmt.assign('r', 'x'),
        Stmt.while('y <= r', Stmt.seq(Stmt.assign('r', 'r - y'), Stmt.assign('q', 'q + 1'))))
    }
  };

  // Turns a statement tree into display lines and records each statement's line index.
  function renderProgram(stmt) {
    const lines = [];
    const emit = (text, indent, extra) => {
      lines.push({ text: '  '.repeat(indent) + text, ...extra });
      return lines.length - 1;
    };
    const walk = (st, ind) => {
      switch (st.k) {
        case 'seq':
          st.list.forEach((x) => walk(x, ind));
          break;
        case 'assign':
          st.line = emit(`${st.x} := ${printExpr(st.e)}`, ind);
          break;
        case 'if':
          st.line = emit(`if ${printExpr(st.cond)} then`, ind);
          walk(st.then, ind + 1);
          emit('else', ind);
          walk(st.else, ind + 1);
          emit('end', ind);
          break;
        case 'while':
          st.line = emit(`while ${printExpr(st.cond)} do`, ind);
          emit('', ind + 1, { assertion: 'inv' });
          walk(st.body, ind + 1);
          emit('end', ind);
          break;
      }
    };
    walk(stmt, 0);
    return lines;
  }

  // Computes wp backwards through the program and collects the verification conditions.
  function generateVcs(prog, spec) {
    const steps = [];
    const loopVcs = [];
    const wp = (st, Q) => {
      switch (st.k) {
        case 'seq':
          return st.list.reduceRight((q, x) => wp(x, q), Q);
        case 'assign': {
          const r = subst(Q, st.x, st.e);
          steps.push({ line: st.line, text: `wp(${st.x} := ${printExpr(st.e)}, ${printExpr(Q)}) = ${printExpr(r)}` });
          return r;
        }
        case 'if': {
          const t = wp(st.then, Q);
          const f = wp(st.else, Q);
          const r = { k: 'and', a: { k: 'imp', a: st.cond, b: t }, b: { k: 'imp', a: { k: 'not', a: st.cond }, b: f } };
          steps.push({ line: st.line, text: `wp(if ${printExpr(st.cond)} ...) = ${printExpr(r)}` });
          return r;
        }
        case 'while': {
          const inv = spec.inv;
          const body = wp(st.body, inv);
          loopVcs.push({
            name: 'Invariant is preserved',
            desc: 'If I and the loop condition hold, one pass through the body must leave I true.',
            f: { k: 'imp', a: { k: 'and', a: inv, b: st.cond }, b: body }
          });
          loopVcs.push({
            name: 'Exit gives the postcondition',
            desc: 'When the loop stops, I and the negated condition together must imply Q.',
            f: { k: 'imp', a: { k: 'and', a: inv, b: { k: 'not', a: st.cond } }, b: Q }
          });
          steps.push({ line: st.line, text: `wp(while ...) is just the invariant I: ${printExpr(inv)}. The loop also adds two VCs of its own.` });
          return inv;
        }
        default:
          throw new Error(`Unknown statement ${st.k}`);
      }
    };
    const top = wp(prog, spec.post);
    const main = spec.inv
      ? { name: 'Invariant holds on entry', desc: 'The precondition must make I true before the first iteration.', f: { k: 'imp', a: spec.pre, b: top } }
      : { name: 'Precondition implies wp', desc: 'P must imply the weakest precondition of the whole program.', f: { k: 'imp', a: spec.pre, b: top } };
    return { steps, vcs: [main, ...loopVcs] };
  }

  // Tries every combination of small integers, smallest magnitudes first.
  function checkVc(f) {
    const vars = [...freeVars(f)].sort();
    const bound = [20, 20, 20, 12, 7, 4, 3][vars.length] || 2;
    const values = [0];
    for (let k = 1; k <= bound; k++) values.push(k, -k);
    const idx = new Array(vars.length).fill(0);
    let tested = 0;
    for (;;) {
      const env = {};
      vars.forEach((v, k) => { env[v] = values[idx[k]]; });
      tested++;
      if (!evalExpr(f, env)) return { ok: false, cex: env, vars, bound, tested };
      let k = vars.length - 1;
      while (k >= 0 && ++idx[k] === values.length) { idx[k] = 0; k--; }
      if (k < 0) return { ok: true, vars, bound, tested };
    }
  }

  const hl = { key: 'abs', lines: [], plan: null, stepIdx: 0, results: null, activeLine: -1, status: 'IDLE', specText: null };
  let hlLog = NULL_LOGGER;

  function hlLoadPreset() {
    hl.key = $('hl-presets').value;
    const p = HL_PRESETS[hl.key];
    $('hl-pre').value = p.pre;
    $('hl-post').value = p.post;
    $('hl-inv').value = p.inv || '';
    $('hl-inv-group').classList.toggle('hidden', !p.inv);
    $('hl-hint').textContent = p.hint;
    hl.lines = renderProgram(p.prog);
    hlLog.clear();
    hlLog.log('Press "Check VCs" to verify, or "Step" to watch wp being computed line by line.', 'info');
    hlInvalidate();
  }

  function hlInvalidate() {
    hl.plan = null;
    hl.results = null;
    hl.stepIdx = 0;
    hl.activeLine = -1;
    hl.status = 'IDLE';
    $('hl-error').textContent = '';
    renderHl();
  }

  function hlReadSpec() {
    const p = HL_PRESETS[hl.key];
    const read = (id, what) => {
      const src = $(id).value.trim();
      if (!src) throw new Error(`The ${what.toLowerCase()} is empty`);
      let e;
      try {
        e = parseExpr(src);
      } catch (err) {
        throw new Error(`${what}: ${err.message}`);
      }
      if (typeOf(e) !== 'bool') throw new Error(`The ${what.toLowerCase()} should be a condition, not a number`);
      return e;
    };
    try {
      $('hl-error').textContent = '';
      return {
        pre: read('hl-pre', 'Precondition'),
        inv: p.inv ? read('hl-inv', 'Invariant') : null,
        post: read('hl-post', 'Postcondition')
      };
    } catch (e) {
      $('hl-error').textContent = e.message;
      return null;
    }
  }

  function hlPlan() {
    const spec = hlReadSpec();
    if (!spec) return false;
    hl.plan = generateVcs(HL_PRESETS[hl.key].prog, spec);
    hl.specText = { pre: printExpr(spec.pre), inv: spec.inv ? printExpr(spec.inv) : '', post: printExpr(spec.post) };
    hl.stepIdx = 0;
    return true;
  }

  function hlFinish() {
    hl.results = hl.plan.vcs.map((vc) => checkVc(vc.f));
    hl.activeLine = -1;
    const bad = hl.results.filter((r) => !r.ok).length;
    hl.status = bad ? 'FAILS' : 'HOLDS';
    if (bad) hlLog.log(`${bad} of ${hl.results.length} VCs fail. Look at the counterexample to see what goes wrong.`, 'danger');
    else hlLog.log(`All ${hl.results.length} VCs hold on the tested range, so the program meets its specification.`, 'success');
    renderHl();
  }

  function hlCheckAll() {
    if (!hlPlan()) return;
    hlLog.log('Computing weakest preconditions from Q backwards:', 'step');
    hl.plan.steps.forEach((st) => hlLog.log(st.text, 'info'));
    hlFinish();
  }

  function hlStep() {
    if (hl.results) {
      hlLog.log('Already checked. Edit a condition or press Reset to start again.', 'warning');
      return;
    }
    if (!hl.plan) {
      if (!hlPlan()) return;
      hlLog.log('Computing weakest preconditions from Q backwards, one statement per step.', 'step');
    }
    if (hl.stepIdx < hl.plan.steps.length) {
      const st = hl.plan.steps[hl.stepIdx++];
      hl.activeLine = st.line;
      hl.status = 'ANALYZING';
      hlLog.log(st.text, 'info');
      renderHl();
    } else {
      hlFinish();
    }
  }

  function renderHl() {
    setBadge($('hl-status'), hl.status, { HOLDS: 'badge-satisfied', FAILS: 'badge-unsat', ANALYZING: 'badge-active' });
    const pre = $('hl-pre').value.trim();
    const inv = $('hl-inv').value.trim();
    const post = $('hl-post').value.trim();

    const code = $('hl-code-display');
    code.innerHTML = '';
    const addLine = (num, text, cls) => {
      const div = document.createElement('div');
      div.className = `code-line ${cls || ''}`;
      div.innerHTML = `<span class="code-num">${num}</span><span class="code-text">${escapeHtml(text)}</span>`;
      code.appendChild(div);
    };
    addLine('', `{ P: ${pre} }`, 'assertion-line');
    let n = 0;
    hl.lines.forEach((ln, i) => {
      if (ln.assertion === 'inv') { addLine('', `${ln.text}{ I: ${inv} }`, 'assertion-line'); return; }
      n++;
      let cls = '';
      if (i === hl.activeLine) cls = 'active';
      else if (hl.status === 'HOLDS') cls = 'verified-ok';
      addLine(n, ln.text, cls);
    });
    addLine('', `{ Q: ${post} }`, 'assertion-line');

    const list = $('hl-vc-list');
    list.innerHTML = '';
    if (!hl.plan || (!hl.results && hl.stepIdx < hl.plan.steps.length)) {
      list.innerHTML = '<span class="placeholder-text">The VCs appear here once wp has been computed for the whole program.</span>';
      return;
    }
    hl.plan.vcs.forEach((vc, i) => {
      const r = hl.results && hl.results[i];
      const card = document.createElement('div');
      card.className = `vc-card-item${r ? (r.ok ? ' vc-ok' : ' vc-bad') : ''}`;
      const badge = !r ? '<span class="vc-status-badge vc-status-pending">NOT CHECKED</span>'
        : r.ok ? '<span class="vc-status-badge vc-status-verified">HOLDS</span>'
          : '<span class="vc-status-badge vc-status-failed">FAILS</span>';
      let detail = '';
      if (r && r.ok) {
        detail = r.vars.length
          ? `Checked all ${r.tested.toLocaleString()} combinations of ${r.vars.join(', ')} from -${r.bound} to ${r.bound}.`
          : 'No variables left, so this is just true.';
      } else if (r) {
        detail = `Counterexample: ${Object.entries(r.cex).map(([k, v]) => `${k} = ${v}`).join(', ')}`;
      }
      card.innerHTML = `<div class="vc-card-header"><span>VC${i + 1}: ${escapeHtml(vc.name)}</span>${badge}</div>`
        + `<div class="vc-card-body">${escapeHtml(printExpr(vc.f))}</div>`
        + `<div class="vc-card-footer">${escapeHtml(vc.desc)}</div>`
        + (detail ? `<div class="vc-card-detail${r.ok ? '' : ' cex'}">${escapeHtml(detail)}</div>` : '');
      list.appendChild(card);
    });
  }

  // ==========================================
  // INITIALISATION
  // ==========================================
  function initLab() {
    const root = $('fv-lab');
    if (!root || root.dataset.ready) return;
    root.dataset.ready = '1';

    const tabs = root.querySelectorAll('.fv-tab-btn');
    const showTab = (id) => {
      tabs.forEach((b) => {
        const on = b.dataset.tab === id;
        b.classList.toggle('active', on);
        b.setAttribute('aria-selected', on ? 'true' : 'false');
      });
      root.querySelectorAll('.fv-tab-content').forEach((c) => c.classList.toggle('active', c.id === id));
      // Redraw now that the panel is visible and can be measured
      if (id === 'model-checker' && mc.K) drawMc();
    };
    tabs.forEach((b) => b.addEventListener('click', () => {
      showTab(b.dataset.tab);
      history.replaceState(null, '', `#${b.dataset.tab}`);
    }));
    const showHashTab = () => {
      const id = location.hash.slice(1);
      if ([...tabs].some((b) => b.dataset.tab === id)) showTab(id);
    };
    window.addEventListener('hashchange', showHashTab);
    showHashTab();

    // SAT
    satLog = makeLogger('sat-logs');
    satSpeed = bindSpeed('sat-speed', (ms) => {
      if (sat.timer) { clearInterval(sat.timer); sat.timer = setInterval(satStep, ms); }
    });
    $('sat-presets').addEventListener('change', satLoadSelected);
    $('sat-custom-input').addEventListener('input', satLoadSelected);
    $('btn-sat-solve').addEventListener('click', satSolve);
    $('btn-sat-step').addEventListener('click', () => { stopSatAuto(); satStep(); });
    $('btn-sat-run').addEventListener('click', toggleSatAuto);
    $('btn-sat-reset').addEventListener('click', satReset);
    satLoadSelected();

    // Model checker
    mcLog = makeLogger('mc-logs');
    mcSpeed = bindSpeed('mc-speed', (ms) => {
      if (mc.timer) { clearInterval(mc.timer); mc.timer = setInterval(mcSimTick, ms); }
    });
    $('mc-system').addEventListener('change', mcLoadSystem);
    $('mc-property').addEventListener('change', mcPropertyChanged);
    $('mc-custom').addEventListener('input', () => { mcClearResult(); $('mc-error').textContent = ''; renderMc(); });
    $('mc-custom').addEventListener('keydown', (e) => { if (e.key === 'Enter') mcVerify(); });
    $('btn-mc-verify').addEventListener('click', mcVerify);
    $('btn-mc-step').addEventListener('click', mcStep);
    $('btn-mc-simulate').addEventListener('click', toggleMcSim);
    $('btn-mc-reset').addEventListener('click', mcReset);
    mcLoadSystem();

    // Hoare logic
    hlLog = makeLogger('hl-logs');
    $('hl-presets').addEventListener('change', hlLoadPreset);
    ['hl-pre', 'hl-inv', 'hl-post'].forEach((id) => {
      $(id).addEventListener('input', hlInvalidate);
      $(id).addEventListener('keydown', (e) => { if (e.key === 'Enter') hlCheckAll(); });
    });
    $('btn-hl-check').addEventListener('click', hlCheckAll);
    $('btn-hl-step').addEventListener('click', hlStep);
    $('btn-hl-reset').addEventListener('click', hlLoadPreset);
    hlLoadPreset();
  }

  if (typeof module !== 'undefined' && module.exports) {
    module.exports = {
      parseCnf, parseCtl, ctlPrint, buildKripke, checkCtl, verifyCtl, MC_SYSTEMS,
      parseExpr, printExpr, typeOf, generateVcs, checkVc, renderProgram, HL_PRESETS, SAT_PRESETS,
      sat, satLoad, satAdvance
    };
  } else if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', initLab);
  } else {
    initLab();
  }
})();
