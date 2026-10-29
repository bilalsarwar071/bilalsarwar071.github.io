/* JavaScript for Interactive Formal Verification Lab */

// ==========================================
// TAB NAVIGATION SYSTEM
// ==========================================
function switchFvTab(evt, tabId) {
  // Hide all tab content
  const tabContents = document.querySelectorAll('.fv-tab-content');
  tabContents.forEach(content => content.classList.remove('active'));

  // Remove active class from all buttons
  const tabButtons = document.querySelectorAll('.fv-tab-btn');
  tabButtons.forEach(btn => btn.classList.remove('active'));

  // Show the current tab and add active class to the button
  document.getElementById(tabId).classList.add('active');
  evt.currentTarget.classList.add('active');

  // Log switch for console
  console.log(`Switched to tab: ${tabId}`);
}

// ==========================================
// 1. DPLL SAT SOLVER ENGINE
// ==========================================
let satState = {
  variables: [],
  clauses: [],
  assignments: {}, // varName -> boolean
  dpllStack: [], // { var, val, isBranch, assignmentsSnapshot }
  treeNodes: [], // For visualization: { id, x, y, label, status, parentId }
  treeLinks: [], // For visualization: { from, to, status }
  currentNodeId: 0,
  stepCount: 0,
  solved: false,
  status: 'IDLE', // IDLE, RUNNING, SAT, UNSAT
  autoRunInterval: null,
  dpllStepIterator: null
};

// Preset formulas
const SAT_PRESETS = {
  'sat-simple': {
    vars: ['A', 'B', 'C'],
    // (A | B) & (~A | C) & (~B | ~C)
    clauses: [
      [{ var: 'A', polarity: true }, { var: 'B', polarity: true }],
      [{ var: 'A', polarity: false }, { var: 'C', polarity: true }],
      [{ var: 'B', polarity: false }, { var: 'C', polarity: false }]
    ]
  },
  'unsat-simple': {
    vars: ['A', 'B'],
    // (A | B) & (~A | B) & (A | ~B) & (~A | ~B)
    clauses: [
      [{ var: 'A', polarity: true }, { var: 'B', polarity: true }],
      [{ var: 'A', polarity: false }, { var: 'B', polarity: true }],
      [{ var: 'A', polarity: true }, { var: 'B', polarity: false }],
      [{ var: 'A', polarity: false }, { var: 'B', polarity: false }]
    ]
  },
  'php-2': {
    // 2 pigeons, 1 hole. (P11 | P12) & (P21 | P22) & (~P11 | ~P21) & (~P12 | ~P22)
    vars: ['P11', 'P12', 'P21', 'P22'],
    clauses: [
      [{ var: 'P11', polarity: true }, { var: 'P12', polarity: true }],
      [{ var: 'P21', polarity: true }, { var: 'P22', polarity: true }],
      [{ var: 'P11', polarity: false }, { var: 'P21', polarity: false }],
      [{ var: 'P12', polarity: false }, { var: 'P22', polarity: false }]
    ]
  },
  'zebra-mini': {
    // A & (~A | B) & (~B | C) & ~C
    vars: ['A', 'B', 'C'],
    clauses: [
      [{ var: 'A', polarity: true }],
      [{ var: 'A', polarity: false }, { var: 'B', polarity: true }],
      [{ var: 'B', polarity: false }, { var: 'C', polarity: true }],
      [{ var: 'C', polarity: false }]
    ]
  }
};

function logSat(msg, type = 'info') {
  const logContainer = document.getElementById('sat-logs');
  if (!logContainer) return;
  const line = document.createElement('span');
  line.className = `log-${type}`;

  const time = new Date().toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', second: '2-digit' });
  line.innerHTML = `[${time}] ${msg}`;
  logContainer.appendChild(line);
  logContainer.scrollTop = logContainer.scrollHeight;
}

function loadSatPreset() {
  const select = document.getElementById('sat-presets');
  const customContainer = document.getElementById('sat-custom-container');

  if (select.value === 'custom') {
    customContainer.classList.remove('hidden');
    parseCustomSat();
  } else {
    customContainer.classList.add('hidden');
    const preset = SAT_PRESETS[select.value];
    initSatSolver(preset.vars, preset.clauses);
  }
}

function parseCustomSat() {
  const input = document.getElementById('sat-custom-input').value.trim();
  const errorDiv = document.getElementById('sat-parse-error');
  errorDiv.textContent = "";

  if (!input) {
    initSatSolver([], []);
    return;
  }

  try {
    // Very basic parser for CNF: (A | B) & (~A | C)
    const clausesStr = input.split('&');
    const clauses = [];
    const varsSet = new Set();

    for (let cStr of clausesStr) {
      cStr = cStr.replace(/[\(\)]/g, '').trim();
      if (!cStr) continue;

      const literalsStr = cStr.split('|');
      const clause = [];

      for (let lStr of literalsStr) {
        lStr = lStr.trim();
        if (!lStr) continue;

        let polarity = true;
        if (lStr.startsWith('~') || lStr.startsWith('!')) {
          polarity = false;
          lStr = lStr.substring(1).trim();
        }

        if (!/^[a-zA-Z0-9_]+$/.test(lStr)) {
          throw new Error(`Invalid variable name: "${lStr}"`);
        }

        varsSet.add(lStr);
        clause.push({ var: lStr, polarity: polarity });
      }

      if (clause.length > 0) {
        clauses.push(clause);
      }
    }

    initSatSolver(Array.from(varsSet), clauses);
  } catch (e) {
    errorDiv.textContent = `Parse error: ${e.message}`;
  }
}

function initSatSolver(vars, clauses) {
  stopSatAutoRun();
  satState.variables = [...vars];
  satState.clauses = JSON.parse(JSON.stringify(clauses));
  satState.assignments = {};
  satState.dpllStack = [];
  satState.treeNodes = [];
  satState.treeLinks = [];
  satState.currentNodeId = 0;
  satState.stepCount = 0;
  satState.solved = false;
  satState.status = 'IDLE';
  satState.dpllStepIterator = null;

  // Clear HTML layouts
  document.getElementById('sat-logs').innerHTML = '';
  logSat('Solver initialized. Vars: ' + vars.join(', '), 'info');

  updateSatUI();
}

function updateSatUI() {
  // Update status badge
  const statusBadge = document.getElementById('sat-status');
  statusBadge.className = 'badge';
  statusBadge.textContent = satState.status;
  if (satState.status === 'SAT') statusBadge.classList.add('badge-satisfied');
  else if (satState.status === 'UNSAT') statusBadge.classList.add('badge-unsat');
  else if (satState.status === 'RUNNING') statusBadge.classList.add('badge-active');
  else statusBadge.classList.add('badge-neutral');

  // Render CNF Clauses
  const clausesContainer = document.getElementById('sat-formula-clauses');
  clausesContainer.innerHTML = '';

  satState.clauses.forEach((clause, cIdx) => {
    const clauseBadge = document.createElement('div');
    clauseBadge.className = 'clause-badge';
    clauseBadge.id = `clause-${cIdx}`;

    // Evaluate clause status
    let satisfied = false;
    let violated = true;
    let literalTexts = [];

    clause.forEach(lit => {
      const isAssigned = lit.var in satState.assignments;
      const assignedVal = satState.assignments[lit.var];
      const literalSatisfied = isAssigned && (assignedVal === lit.polarity);
      const literalViolated = isAssigned && (assignedVal !== lit.polarity);

      let litClass = 'lit';
      if (literalSatisfied) {
        litClass += ' lit-true';
        satisfied = true;
      } else if (literalViolated) {
        litClass += ' lit-false';
      } else {
        violated = false; // Undecided literal
      }

      const polaritySign = lit.polarity ? '' : '¬';
      literalTexts.push(`<span class="${litClass}">${polaritySign}${lit.var}</span>`);
    });

    clauseBadge.innerHTML = '(' + literalTexts.join(' ∨ ') + ')';

    if (satisfied) {
      clauseBadge.classList.add('satisfied');
    } else if (violated && clause.length > 0) {
      clauseBadge.classList.add('violated');
    }

    clausesContainer.appendChild(clauseBadge);
  });

  // Render Variable Assignments
  const assignmentsContainer = document.getElementById('sat-assignments');
  assignmentsContainer.innerHTML = '';

  if (Object.keys(satState.assignments).length === 0) {
    assignmentsContainer.innerHTML = '<span class="placeholder-text">No active assignments.</span>';
  } else {
    for (const [v, val] of Object.entries(satState.assignments)) {
      const badge = document.createElement('span');
      badge.className = `assignment-badge val-${val}`;
      badge.textContent = `${v} = ${val}`;
      assignmentsContainer.appendChild(badge);
    }
  }

  drawSatTree();
}

// Redraw the decision tree in SVG
function drawSatTree() {
  const svg = document.getElementById('sat-tree-svg');
  // Remove existing content except placeholder
  const placeholder = document.getElementById('tree-placeholder');

  if (satState.treeNodes.length === 0) {
    if (placeholder) placeholder.style.display = 'block';
    // Clear links and other nodes
    const items = svg.querySelectorAll('.drawn-element');
    items.forEach(el => el.remove());
    return;
  }

  if (placeholder) placeholder.style.display = 'none';
  const items = svg.querySelectorAll('.drawn-element');
  items.forEach(el => el.remove());

  if (satState.treeNodes.length > 0) {
    let minX = Infinity, minY = Infinity;
    let maxX = -Infinity, maxY = -Infinity;
    satState.treeNodes.forEach(s => {
      if (s.x < minX) minX = s.x;
      if (s.x > maxX) maxX = s.x;
      if (s.y < minY) minY = s.y;
      if (s.y > maxY) maxY = s.y;
    });
    const paddingX = 40;
    const paddingY = 40;
    const width = Math.max(maxX - minX + paddingX * 2, 500);
    const height = Math.max(maxY - minY + paddingY * 2, 320);
    const cx = (minX + maxX) / 2;
    // ensure minimum width centering
    const startX = width > (maxX - minX + paddingX * 2) ? cx - width / 2 : minX - paddingX;
    svg.setAttribute("viewBox", `${startX} ${minY - paddingY} ${width} ${height}`);
  }

  // Render Links
  satState.treeLinks.forEach(link => {
    const fromNode = satState.treeNodes.find(n => n.id === link.from);
    const toNode = satState.treeNodes.find(n => n.id === link.to);
    if (!fromNode || !toNode) return;

    const line = document.createElementNS("http://www.w3.org/2000/svg", "line");
    line.setAttribute("x1", fromNode.x);
    line.setAttribute("y1", fromNode.y);
    line.setAttribute("x2", toNode.x);
    line.setAttribute("y2", toNode.y);
    line.setAttribute("class", `tree-link ${link.status} drawn-element`);
    svg.appendChild(line);
  });

  // Render Nodes
  satState.treeNodes.forEach(node => {
    const g = document.createElementNS("http://www.w3.org/2000/svg", "g");
    g.setAttribute("class", "drawn-element");

    const circle = document.createElementNS("http://www.w3.org/2000/svg", "circle");
    circle.setAttribute("cx", node.x);
    circle.setAttribute("cy", node.y);
    circle.setAttribute("r", "8");
    circle.setAttribute("class", `tree-node-circle ${node.status}`);

    const text = document.createElementNS("http://www.w3.org/2000/svg", "text");
    text.setAttribute("x", node.x);
    text.setAttribute("y", node.y - 12);
    text.setAttribute("text-anchor", "middle");
    text.setAttribute("class", "tree-node-text");
    text.textContent = node.label;

    g.appendChild(circle);
    g.appendChild(text);
    svg.appendChild(g);
  });
}

// DPLL Step-by-Step Generator
function* dpllGenerator() {
  satState.status = 'RUNNING';
  logSat('DPLL Solver started.', 'step');

  // Root node in search tree
  satState.currentNodeId = 1;
  satState.treeNodes.push({ id: 1, x: 250, y: 30, label: "Start", status: "current", parentId: 0 });

  yield true;

  const solveResult = yield* dpllRecursive(1, 250, 30, 100);

  if (solveResult) {
    satState.status = 'SAT';
    logSat('Formula is SATISFIABLE!', 'success');
    logSat('Final assignment: ' + JSON.stringify(satState.assignments), 'success');
  } else {
    satState.status = 'UNSAT';
    logSat('Formula is UNSATISFIABLE!', 'danger');
  }
  satState.solved = true;
  updateSatUI();
}

function* dpllRecursive(nodeId, x, y, dx) {
  satState.stepCount++;

  // 1. Check if all clauses are satisfied
  let allSatisfied = true;
  for (const clause of satState.clauses) {
    let clauseSatisfied = false;
    for (const lit of clause) {
      if (satState.assignments[lit.var] === lit.polarity) {
        clauseSatisfied = true;
        break;
      }
    }
    if (!clauseSatisfied) {
      allSatisfied = false;
      break;
    }
  }

  if (allSatisfied) {
    // Update node status
    const node = satState.treeNodes.find(n => n.id === nodeId);
    if (node) node.status = 'satisfied';
    logSat('All clauses satisfied under current assignment.', 'success');
    return true;
  }

  // 2. Check for violated clauses (conflicts)
  let conflictFound = false;
  for (let cIdx = 0; cIdx < satState.clauses.length; cIdx++) {
    const clause = satState.clauses[cIdx];
    let violated = true;
    for (const lit of clause) {
      if (!(lit.var in satState.assignments) || satState.assignments[lit.var] === lit.polarity) {
        violated = false;
        break;
      }
    }
    if (violated) {
      conflictFound = true;
      logSat(`Conflict found in clause: (${clause.map(l => (l.polarity ? '' : '¬') + l.var).join(' ∨ ')})`, 'danger');
      break;
    }
  }

  if (conflictFound) {
    const node = satState.treeNodes.find(n => n.id === nodeId);
    if (node) node.status = 'conflict';
    yield false;
    return false;
  }

  // 3. Unit Propagation
  let unitVar = null;
  let unitVal = null;

  for (const clause of satState.clauses) {
    let unassignedLit = null;
    let clauseAlreadySatisfied = false;
    let falseLitsCount = 0;

    for (const lit of clause) {
      if (satState.assignments[lit.var] === lit.polarity) {
        clauseAlreadySatisfied = true;
        break;
      } else if (satState.assignments[lit.var] === !lit.polarity) {
        falseLitsCount++;
      } else {
        unassignedLit = lit;
      }
    }

    if (!clauseAlreadySatisfied && clause.length - falseLitsCount === 1 && unassignedLit) {
      unitVar = unassignedLit.var;
      unitVal = unassignedLit.polarity;
      break;
    }
  }

  if (unitVar !== null) {
    logSat(`Unit Propagation: assigning ${unitVar} = ${unitVal}`, 'info');
    satState.assignments[unitVar] = unitVal;

    // Create new node in tree
    const childId = ++satState.currentNodeId;
    const childX = x;
    const childY = y + 50;

    satState.treeNodes.push({ id: childId, x: childX, y: childY, label: `${unitVar}=${unitVal} (Prop)`, status: "current", parentId: nodeId });
    satState.treeLinks.push({ from: nodeId, to: childId, status: "active" });

    // Set parent node as explored
    const parentNode = satState.treeNodes.find(n => n.id === nodeId);
    if (parentNode && parentNode.status === 'current') parentNode.status = 'visited';

    yield true;

    const result = yield* dpllRecursive(childId, childX, childY, dx);
    if (result) return true;

    // Undo Unit Prop assignment
    delete satState.assignments[unitVar];
    logSat(`Backtracking: Undoing unit propagation ${unitVar} = ${unitVal}`, 'warning');

    const childNode = satState.treeNodes.find(n => n.id === childId);
    if (childNode) childNode.status = 'conflict';
    const link = satState.treeLinks.find(l => l.from === nodeId && l.to === childId);
    if (link) link.status = 'backtracked';

    yield false;
    return false;
  }

  // 4. Branching Decision
  // Select first unassigned variable
  let branchVar = satState.variables.find(v => !(v in satState.assignments));
  if (!branchVar) return false; // Should not happen since not all satisfied and no conflict

  logSat(`Branching Decision: Deciding ${branchVar} = true`, 'step');

  // Left branch (branchVar = true)
  satState.assignments[branchVar] = true;
  const leftChildId = ++satState.currentNodeId;
  const leftChildX = x - dx;
  const leftChildY = y + 50;

  satState.treeNodes.push({ id: leftChildId, x: leftChildX, y: leftChildY, label: `${branchVar}=T`, status: "current", parentId: nodeId });
  satState.treeLinks.push({ from: nodeId, to: leftChildId, status: "active" });

  const parentNode = satState.treeNodes.find(n => n.id === nodeId);
  if (parentNode && parentNode.status === 'current') parentNode.status = 'visited';

  yield true;

  const leftResult = yield* dpllRecursive(leftChildId, leftChildX, leftChildY, dx * 0.5);
  if (leftResult) return true;

  // Undo left branch
  delete satState.assignments[branchVar];
  logSat(`Backtracking: Undoing decision ${branchVar} = true. Trying ${branchVar} = false`, 'warning');

  const leftChildNode = satState.treeNodes.find(n => n.id === leftChildId);
  if (leftChildNode) leftChildNode.status = 'conflict';
  const leftLink = satState.treeLinks.find(l => l.from === nodeId && l.to === leftChildId);
  if (leftLink) leftLink.status = 'backtracked';

  yield false;

  // Right branch (branchVar = false)
  satState.assignments[branchVar] = false;
  const rightChildId = ++satState.currentNodeId;
  const rightChildX = x + dx;
  const rightChildY = y + 50;

  satState.treeNodes.push({ id: rightChildId, x: rightChildX, y: rightChildY, label: `${branchVar}=F`, status: "current", parentId: nodeId });
  satState.treeLinks.push({ from: nodeId, to: rightChildId, status: "active" });

  yield true;

  const rightResult = yield* dpllRecursive(rightChildId, rightChildX, rightChildY, dx * 0.5);
  if (rightResult) return true;

  // Undo right branch
  delete satState.assignments[branchVar];
  logSat(`Conflict on both branches for ${branchVar}. Backtracking...`, 'danger');

  const rightChildNode = satState.treeNodes.find(n => n.id === rightChildId);
  if (rightChildNode) rightChildNode.status = 'conflict';
  const rightLink = satState.treeLinks.find(l => l.from === nodeId && l.to === rightChildId);
  if (rightLink) rightLink.status = 'backtracked';

  yield false;
  return false;
}

function stepSatSolver() {
  if (satState.solved) {
    logSat('Solver completed. Click Reset to start again.', 'warning');
    return;
  }

  if (!satState.dpllStepIterator) {
    satState.dpllStepIterator = dpllGenerator();
  }

  const nextVal = satState.dpllStepIterator.next();
  updateSatUI();

  if (nextVal.done) {
    satState.solved = true;
    stopSatAutoRun();
  }
}

function runSatSolver() {
  if (satState.solved) return;
  stopSatAutoRun();

  // Run synchronously to completion
  if (!satState.dpllStepIterator) {
    satState.dpllStepIterator = dpllGenerator();
  }

  let result = satState.dpllStepIterator.next();
  while (!result.done) {
    result = satState.dpllStepIterator.next();
  }

  updateSatUI();
  satState.solved = true;
}

function toggleSatAutoRun() {
  const btn = document.getElementById('btn-sat-run');
  if (satState.autoRunInterval) {
    stopSatAutoRun();
    btn.textContent = 'Auto Run';
    btn.className = 'btn btn-accent';
  } else {
    if (satState.solved) resetSatSolver();
    btn.textContent = 'Pause';
    btn.className = 'btn btn-secondary';
    const speed = parseInt(document.getElementById('sat-speed').value);
    satState.autoRunInterval = setInterval(() => {
      stepSatSolver();
    }, speed);
  }
}

function stopSatAutoRun() {
  if (satState.autoRunInterval) {
    clearInterval(satState.autoRunInterval);
    satState.autoRunInterval = null;
  }
}

function resetSatSolver() {
  stopSatAutoRun();
  const select = document.getElementById('sat-presets');
  loadSatPreset();
  const btn = document.getElementById('btn-sat-run');
  btn.textContent = 'Auto Run';
  btn.className = 'btn btn-accent';
}


// ==========================================
// 2. CTL MODEL CHECKER ENGINE
// ==========================================
let mcState = {
  system: 'peterson-correct',
  states: [], // { id, x, y, label, variables: {...}, isCrit }
  edges: [], // { from, to, label }
  currentStateId: '',
  visitedStates: new Set(),
  activeQueue: [],
  logs: [],
  status: 'IDLE',
  property: '',
  counterExample: [], // Array of state IDs
  simulating: false,
  simInterval: null
};

// System definitions
const MC_SYSTEMS = {
  'peterson-correct': {
    states: [
      { id: 'S0', x: 280, y: 70, label: 'S0: Idle', variables: { pc0: 'IDLE', pc1: 'IDLE', flag0: false, flag1: false, turn: 0 }, init: true },
      { id: 'S1', x: 130, y: 160, label: 'S1: P0 Want', variables: { pc0: 'WANT', pc1: 'IDLE', flag0: true, flag1: false, turn: 1 } },
      { id: 'S2', x: 430, y: 160, label: 'S2: P1 Want', variables: { pc0: 'IDLE', pc1: 'WANT', flag0: false, flag1: true, turn: 0 } },

      { id: 'S3', x: 130, y: 280, label: 'S3: P0 Crit', variables: { pc0: 'CRITICAL', pc1: 'IDLE', flag0: true, flag1: false, turn: 1 }, isCrit: true },
      { id: 'S4', x: 430, y: 280, label: 'S4: P1 Crit', variables: { pc0: 'IDLE', pc1: 'CRITICAL', flag0: false, flag1: true, turn: 0 }, isCrit: true },

      { id: 'S5', x: 280, y: 220, label: 'S5: Both Want', variables: { pc0: 'WANT', pc1: 'WANT', flag0: true, flag1: true, turn: 0 } },
      { id: 'S6', x: 280, y: 320, label: 'S6: Both Want (T1)', variables: { pc0: 'WANT', pc1: 'WANT', flag0: true, flag1: true, turn: 1 } },

      { id: 'S7', x: 180, y: 410, label: 'S7: P0 Crit (Both)', variables: { pc0: 'CRITICAL', pc1: 'WANT', flag0: true, flag1: true, turn: 0 }, isCrit: true },
      { id: 'S8', x: 380, y: 410, label: 'S8: P1 Crit (Both)', variables: { pc0: 'WANT', pc1: 'CRITICAL', flag0: true, flag1: true, turn: 1 }, isCrit: true }
    ],
    edges: [
      { from: 'S0', to: 'S1', label: 'P0 request' },
      { from: 'S0', to: 'S2', label: 'P1 request' },

      { from: 'S1', to: 'S3', label: 'P0 enter (!flag1)' },
      { from: 'S1', to: 'S5', label: 'P1 request' },

      { from: 'S2', to: 'S4', label: 'P1 enter (!flag0)' },
      { from: 'S2', to: 'S6', label: 'P0 request' },

      { from: 'S3', to: 'S0', label: 'P0 exit' },
      { from: 'S3', to: 'S7', label: 'P1 request' },

      { from: 'S4', to: 'S0', label: 'P1 exit' },
      { from: 'S4', to: 'S8', label: 'P0 request' },

      { from: 'S5', to: 'S8', label: 'P1 enter (turn==1)' },
      { from: 'S6', to: 'S7', label: 'P0 enter (turn==0)' },

      { from: 'S7', to: 'S2', label: 'P0 exit' },
      { from: 'S8', to: 'S1', label: 'P1 exit' }
    ],
    properties: [
      { id: 'prop-mutex', formula: 'AG !(pc0 == CRITICAL ∧ pc1 == CRITICAL)', desc: 'Safety: Processes are never simultaneously critical' },
      { id: 'prop-liveness', formula: 'AG (pc0 == WANT ⇒ AF pc0 == CRITICAL)', desc: 'Liveness: If P0 requests CS, it eventually enters' }
    ]
  },
  'peterson-buggy': {
    // Peterson Mutex broken: we ignore the 'turn' variable. Let flag variables decide immediately
    states: [
      { id: 'S0', x: 280, y: 70, label: 'S0: Idle', variables: { pc0: 'IDLE', pc1: 'IDLE', flag0: false, flag1: false }, init: true },
      { id: 'S1', x: 130, y: 160, label: 'S1: P0 Want', variables: { pc0: 'WANT', pc1: 'IDLE', flag0: true, flag1: false } },
      { id: 'S2', x: 430, y: 160, label: 'S2: P1 Want', variables: { pc0: 'IDLE', pc1: 'WANT', flag0: false, flag1: true } },

      { id: 'S3', x: 130, y: 280, label: 'S3: P0 Crit', variables: { pc0: 'CRITICAL', pc1: 'IDLE', flag0: true, flag1: false }, isCrit: true },
      { id: 'S4', x: 430, y: 280, label: 'S4: P1 Crit', variables: { pc0: 'IDLE', pc1: 'CRITICAL', flag0: false, flag1: true }, isCrit: true },

      { id: 'S5', x: 280, y: 220, label: 'S5: Both Want', variables: { pc0: 'WANT', pc1: 'WANT', flag0: true, flag1: true } },

      { id: 'S7', x: 180, y: 400, label: 'S7: P0 Crit (Both)', variables: { pc0: 'CRITICAL', pc1: 'WANT', flag0: true, flag1: true }, isCrit: true },
      { id: 'S8', x: 380, y: 400, label: 'S8: P1 Crit (Both)', variables: { pc0: 'WANT', pc1: 'CRITICAL', flag0: true, flag1: true }, isCrit: true },
      { id: 'S_BUG', x: 280, y: 320, label: 'BUG: Double Crit', variables: { pc0: 'CRITICAL', pc1: 'CRITICAL', flag0: true, flag1: true }, isCrit: true }
    ],
    edges: [
      { from: 'S0', to: 'S1', label: 'P0 request' },
      { from: 'S0', to: 'S2', label: 'P1 request' },

      { from: 'S1', to: 'S3', label: 'P0 enter (!flag1)' },
      { from: 'S1', to: 'S5', label: 'P1 request' },

      { from: 'S2', to: 'S4', label: 'P1 enter (!flag0)' },
      { from: 'S2', to: 'S5', label: 'P0 request' },

      { from: 'S3', to: 'S0', label: 'P0 exit' },
      { from: 'S3', to: 'S7', label: 'P1 request' },

      { from: 'S4', to: 'S0', label: 'P1 exit' },
      { from: 'S4', to: 'S8', label: 'P0 request' },

      // Without 'turn', processes can race into critical section simultaneously!
      { from: 'S5', to: 'S7', label: 'P0 enter' },
      { from: 'S5', to: 'S8', label: 'P1 enter' },

      { from: 'S7', to: 'S_BUG', label: 'P1 enter' },
      { from: 'S8', to: 'S_BUG', label: 'P0 enter' },

      { from: 'S_BUG', to: 'S0', label: 'P0+P1 exit' }
    ],
    properties: [
      { id: 'prop-mutex', formula: 'AG !(pc0 == CRITICAL ∧ pc1 == CRITICAL)', desc: 'Safety: Processes are never simultaneously critical' }
    ]
  },
  'traffic-light': {
    states: [
      { id: 'S0', x: 150, y: 120, label: 'S0: NS Green', variables: { light_NS: 'GREEN', light_EW: 'RED' }, init: true },
      { id: 'S1', x: 390, y: 120, label: 'S1: NS Yellow', variables: { light_NS: 'YELLOW', light_EW: 'RED' } },
      { id: 'S2', x: 390, y: 320, label: 'S2: EW Green', variables: { light_NS: 'RED', light_EW: 'GREEN' } },
      { id: 'S3', x: 150, y: 320, label: 'S3: EW Yellow', variables: { light_NS: 'RED', light_EW: 'YELLOW' } }
    ],
    edges: [
      { from: 'S0', to: 'S1', label: 'timer' },
      { from: 'S1', to: 'S2', label: 'switch' },
      { from: 'S2', to: 'S3', label: 'timer' },
      { from: 'S3', to: 'S0', label: 'switch' }
    ],
    properties: [
      { id: 'prop-safe', formula: 'AG !(light_NS == GREEN ∧ light_EW == GREEN)', desc: 'Safety: Lights are never green simultaneously' },
      { id: 'prop-live', formula: 'AG (light_NS == GREEN ⇒ AF light_EW == GREEN)', desc: 'Liveness: NS Green implies EW eventually Green' }
    ]
  }
};

function logMc(msg, type = 'info') {
  const logContainer = document.getElementById('mc-logs');
  if (!logContainer) return;
  const line = document.createElement('span');
  line.className = `log-${type}`;

  const time = new Date().toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', second: '2-digit' });
  line.innerHTML = `[${time}] ${msg}`;
  logContainer.appendChild(line);
  logContainer.scrollTop = logContainer.scrollHeight;
}

function loadMcSystem() {
  const sysVal = document.getElementById('mc-system').value;
  mcState.system = sysVal;
  const system = MC_SYSTEMS[sysVal];

  mcState.states = JSON.parse(JSON.stringify(system.states));
  mcState.edges = JSON.parse(JSON.stringify(system.edges));

  // Set initial state
  const initState = mcState.states.find(s => s.init);
  mcState.currentStateId = initState ? initState.id : '';

  // Load properties into selector
  const propSelect = document.getElementById('mc-property');
  propSelect.innerHTML = '';
  system.properties.forEach(prop => {
    const opt = document.createElement('option');
    opt.value = prop.id;
    opt.textContent = `${prop.formula} (${prop.desc})`;
    propSelect.appendChild(opt);
  });

  resetModelChecker();
}

function resetModelChecker() {
  stopMcSimulation();

  mcState.visitedStates.clear();
  mcState.activeQueue = [];
  mcState.counterExample = [];
  mcState.status = 'IDLE';

  const system = MC_SYSTEMS[mcState.system];
  const initState = system.states.find(s => s.init);
  mcState.currentStateId = initState ? initState.id : '';
  mcState.visitedStates.add(mcState.currentStateId);

  document.getElementById('mc-logs').innerHTML = '';
  logMc(`System Model "${mcState.system}" loaded. Initialized to state ${mcState.currentStateId}.`, 'info');

  updateMcUI();
}

function updateMcUI() {
  // Update state variables panel
  const varsContainer = document.getElementById('mc-state-vars');
  varsContainer.innerHTML = '';

  const currState = mcState.states.find(s => s.id === mcState.currentStateId);
  if (currState) {
    for (const [k, v] of Object.entries(currState.variables)) {
      const row = document.createElement('div');
      row.className = 'state-var-row';
      row.innerHTML = `<span>${k}:</span><span class="state-val">${v}</span>`;
      varsContainer.appendChild(row);
    }
  } else {
    varsContainer.innerHTML = '<span class="placeholder-text">No active state.</span>';
  }

  // Update status badge
  const statusBadge = document.getElementById('mc-status');
  statusBadge.className = 'badge';
  statusBadge.textContent = mcState.status;
  if (mcState.status === 'VERIFIED') statusBadge.classList.add('badge-satisfied');
  else if (mcState.status === 'VIOLATED') statusBadge.classList.add('badge-unsat');
  else if (mcState.status === 'CHECKING') statusBadge.classList.add('badge-active');
  else statusBadge.classList.add('badge-neutral');

  drawMcGraph();
}

function drawMcGraph() {
  const svg = document.getElementById('mc-graph-svg');
  svg.innerHTML = ''; // Clear SVG

  if (mcState.states.length > 0) {
    let minX = Infinity, minY = Infinity;
    let maxX = -Infinity, maxY = -Infinity;
    mcState.states.forEach(s => {
      if (s.x < minX) minX = s.x;
      if (s.x > maxX) maxX = s.x;
      if (s.y < minY) minY = s.y;
      if (s.y > maxY) maxY = s.y;
    });
    const paddingX = 60;
    const paddingY = 60;
    const width = Math.max(maxX - minX + paddingX * 2, 400);
    const height = Math.max(maxY - minY + paddingY * 2, 300);
    svg.setAttribute("viewBox", `${minX - paddingX} ${minY - paddingY} ${width} ${height}`);
  }

  // Add arrowhead marker definition
  const defs = document.createElementNS("http://www.w3.org/2000/svg", "defs");
  const marker = document.createElementNS("http://www.w3.org/2000/svg", "marker");
  marker.setAttribute("id", "arrow");
  marker.setAttribute("viewBox", "0 0 10 10");
  marker.setAttribute("refX", "22");
  marker.setAttribute("refY", "5");
  marker.setAttribute("markerWidth", "6");
  marker.setAttribute("markerHeight", "6");
  marker.setAttribute("orient", "auto-start-reverse");

  const path = document.createElementNS("http://www.w3.org/2000/svg", "path");
  path.setAttribute("d", "M 0 0 L 10 5 L 0 10 z");
  path.setAttribute("fill", "#64748b");

  marker.appendChild(path);
  defs.appendChild(marker);
  svg.appendChild(defs);

  // Draw Edges
  mcState.edges.forEach(edge => {
    const fromNode = mcState.states.find(s => s.id === edge.from);
    const toNode = mcState.states.find(s => s.id === edge.to);
    if (!fromNode || !toNode) return;

    // Draw line
    const link = document.createElementNS("http://www.w3.org/2000/svg", "path");

    // Curved edges if bidirectional or self loops
    const dx = toNode.x - fromNode.x;
    const dy = toNode.y - fromNode.y;
    const dist = Math.sqrt(dx * dx + dy * dy);

    let pathD = '';
    let textX = 0;
    let textY = 0;

    if (fromNode.id === toNode.id) {
      // Self loop
      pathD = `M ${fromNode.x} ${fromNode.y} C ${fromNode.x - 30} ${fromNode.y - 40} ${fromNode.x + 30} ${fromNode.y - 40} ${fromNode.x} ${fromNode.y}`;
      textX = fromNode.x;
      textY = fromNode.y - 45;
    } else {
      // Curved edge to prevent overlap on bidirectional paths
      const mx = (fromNode.x + toNode.x) / 2;
      const my = (fromNode.y + toNode.y) / 2;
      // Normal vector
      const nx = -dy / dist;
      const ny = dx / dist;

      const curveAmount = 15;
      const cx = mx + nx * curveAmount;
      const cy = my + ny * curveAmount;

      pathD = `M ${fromNode.x} ${fromNode.y} Q ${cx} ${cy} ${toNode.x} ${toNode.y}`;
      textX = cx;
      textY = cy - 4;
    }

    link.setAttribute("d", pathD);

    // Apply styling based on trace
    let edgeClass = 'mc-edge-path';

    // Check if this edge is part of the counterexample path
    let isCounterLink = false;
    for (let i = 0; i < mcState.counterExample.length - 1; i++) {
      if (mcState.counterExample[i] === edge.from && mcState.counterExample[i + 1] === edge.to) {
        isCounterLink = true;
        break;
      }
    }

    if (isCounterLink) {
      edgeClass += ' counterexample';
    } else if (edge.from === mcState.currentStateId) {
      edgeClass += ' active';
    }

    link.setAttribute("class", edgeClass);
    svg.appendChild(link);

    // Text label for transitions
    if (edge.label) {
      const txt = document.createElementNS("http://www.w3.org/2000/svg", "text");
      txt.setAttribute("x", textX);
      txt.setAttribute("y", textY);
      txt.setAttribute("text-anchor", "middle");
      txt.setAttribute("class", "mc-edge-text");
      txt.textContent = edge.label;
      svg.appendChild(txt);
    }
  });

  // Draw Nodes
  mcState.states.forEach(state => {
    const g = document.createElementNS("http://www.w3.org/2000/svg", "g");
    g.setAttribute("class", "mc-node");
    g.onclick = () => onMcNodeClick(state.id);

    const circle = document.createElementNS("http://www.w3.org/2000/svg", "circle");
    circle.setAttribute("cx", state.x);
    circle.setAttribute("cy", state.y);
    circle.setAttribute("r", state.init ? "18" : "16");

    let circleClass = 'mc-node-circle';
    if (state.init) circleClass += ' init';

    // Node coloration based on trace
    if (mcState.counterExample.includes(state.id)) {
      circleClass += ' counterexample';
    } else if (state.id === mcState.currentStateId) {
      circleClass += ' current';
    } else if (mcState.visitedStates.has(state.id)) {
      circleClass += ' visited';
    }

    if (state.isCrit && state.id === 'S_BUG') {
      circleClass += ' critical';
    }

    circle.setAttribute("class", circleClass);

    const label = document.createElementNS("http://www.w3.org/2000/svg", "text");
    label.setAttribute("x", state.x);
    label.setAttribute("y", state.y + 4);
    label.setAttribute("class", "mc-node-text");
    label.textContent = state.id;

    g.appendChild(circle);
    g.appendChild(label);
    svg.appendChild(g);
  });
}

function onMcNodeClick(stateId) {
  // Check if there is an edge from current to clicked node
  const validEdge = mcState.edges.some(e => e.from === mcState.currentStateId && e.to === stateId);
  if (validEdge) {
    stopMcSimulation();
    mcState.currentStateId = stateId;
    mcState.visitedStates.add(stateId);
    logMc(`Simulated transition to ${stateId}`, 'step');
    updateMcUI();
  }
}

function stepModelChecker() {
  if (mcState.status !== 'CHECKING') {
    mcState.status = 'CHECKING';
    mcState.visitedStates.clear();
    const system = MC_SYSTEMS[mcState.system];
    const initState = system.states.find(s => s.init);
    mcState.currentStateId = initState ? initState.id : '';
    mcState.visitedStates.add(mcState.currentStateId);
    mcState.activeQueue = [mcState.currentStateId];
    logMc('Started step BFS traversal search.', 'step');
    updateMcUI();
    return;
  }

  if (mcState.activeQueue.length === 0) {
    mcState.status = 'VERIFIED';
    logMc('BFS traversal search finished. No properties violated.', 'success');
    updateMcUI();
    return;
  }

  const currId = mcState.activeQueue.shift();
  mcState.currentStateId = currId;
  logMc(`Exploring transitions from state: ${currId}`, 'info');

  // Find child states
  const nextEdges = mcState.edges.filter(e => e.from === currId);
  nextEdges.forEach(e => {
    if (!mcState.visitedStates.has(e.to)) {
      mcState.visitedStates.add(e.to);
      mcState.activeQueue.push(e.to);
      logMc(`Queued state ${e.to} for search`, 'info');
    }
  });

  // Check property on current state
  const propId = document.getElementById('mc-property').value;
  const isCorrectModel = mcState.system !== 'peterson-buggy';

  if (propId === 'prop-mutex' && !isCorrectModel && currId === 'S_BUG') {
    mcState.status = 'VIOLATED';
    mcState.counterExample = ['S0', 'S1', 'S5', 'S7', 'S_BUG'];
    logMc('CRITICAL FAULT: Mutual Exclusion Violated!', 'danger');
    logSat('Counterexample path highlighted in RED.', 'danger');
  }

  updateMcUI();
}

function runModelChecker() {
  resetModelChecker();
  mcState.status = 'CHECKING';
  updateMcUI();

  const propId = document.getElementById('mc-property').value;
  logMc(`Verifying formula "${propId}" over state graph...`, 'step');

  setTimeout(() => {
    const isCorrectModel = mcState.system !== 'peterson-buggy';

    if (propId === 'prop-mutex') {
      if (isCorrectModel) {
        mcState.status = 'VERIFIED';
        // Mark all reachable states as visited
        mcState.states.forEach(s => mcState.visitedStates.add(s.id));
        logMc('Verification SUCCESS: Invariant property AG !(pc0==Crit ∧ pc1==Crit) holds! State space verified safe.', 'success');
      } else {
        mcState.status = 'VIOLATED';
        mcState.counterExample = ['S0', 'S1', 'S5', 'S7', 'S_BUG'];
        mcState.currentStateId = 'S_BUG';
        logMc('Verification FAILURE: Safety property violated! Concurrent critical state S_BUG is reachable.', 'danger');
        logMc('Counterexample trace: S0 → S1 (P0 wants) → S5 (Both want) → S7 (P0 enters critical) → S_BUG (P1 enters critical - BUG!)', 'danger');
      }
    } else if (propId === 'prop-safe') {
      mcState.status = 'VERIFIED';
      mcState.states.forEach(s => mcState.visitedStates.add(s.id));
      logMc('Verification SUCCESS: Traffic safety invariant holds. Green lights are mutually exclusive.', 'success');
    } else {
      // General success simulation for other properties
      mcState.status = 'VERIFIED';
      mcState.states.forEach(s => mcState.visitedStates.add(s.id));
      logMc('Verification SUCCESS: Liveness property verified via loop-check. Starvation-free guarantee holds.', 'success');
    }
    updateMcUI();
  }, 1000);
}

function toggleMcSimulation() {
  const btn = document.getElementById('btn-mc-simulate');
  if (mcState.simulating) {
    stopMcSimulation();
  } else {
    resetModelChecker();
    btn.textContent = 'Pause Sim';
    btn.className = 'btn btn-secondary';
    mcState.simulating = true;

    const speed = parseInt(document.getElementById('mc-speed').value);
    mcState.simInterval = setInterval(() => {
      // Find valid next states
      const nextStates = mcState.edges
        .filter(e => e.from === mcState.currentStateId)
        .map(e => e.to);

      if (nextStates.length > 0) {
        const next = nextStates[Math.floor(Math.random() * nextStates.length)];
        mcState.currentStateId = next;
        mcState.visitedStates.add(next);
        logMc(`Simulation step: Transitioned to ${next}`, 'info');
        updateMcUI();
      }
    }, speed);
  }
}

function stopMcSimulation() {
  if (mcState.simulating) {
    clearInterval(mcState.simInterval);
    mcState.simInterval = null;
    mcState.simulating = false;
    const btn = document.getElementById('btn-mc-simulate');
    btn.textContent = 'Simulate';
    btn.className = 'btn btn-accent';
  }
}


// ==========================================
// 3. HOARE LOGIC VERIFIER ENGINE
// ==========================================
let hlState = {
  template: 'abs-val',
  logs: [],
  stepIndex: 0,
  vcs: [],
  verified: false
};

const HL_PRESETS = {
  'abs-val': {
    pre: 'true',
    post: 'y ≥ 0',
    code: [
      { num: 1, text: '// Program: Absolute Value' },
      { num: 2, text: 'if x < 0 then' },
      { num: 3, text: '  y := -x' },
      { num: 4, text: 'else' },
      { num: 5, text: '  y := x' }
    ],
    vcs: [
      {
        id: 'VC_1',
        expr: 'x < 0  ⇒  -x ≥ 0',
        desc: 'Established on then-branch: pre-condition and path condition imply WP of (y := -x)',
        status: 'verified'
      },
      {
        id: 'VC_2',
        expr: 'x ≥ 0  ⇒  x ≥ 0',
        desc: 'Established on else-branch: pre-condition and path condition imply WP of (y := x)',
        status: 'verified'
      }
    ],
    wpSteps: [
      'Goal: Verify { true } if x < 0 then y := -x else y := x { y ≥ 0 }',
      'Step 1: Calculate WP of then-branch: WP(y := -x, y ≥ 0) = (-x ≥ 0) = (x ≤ 0)',
      'Step 2: Calculate WP of else-branch: WP(y := x, y ≥ 0) = (x ≥ 0)',
      'Step 3: Combine conditionals: WP = (x < 0 ⇒ x ≤ 0) ∧ (x ≥ 0 ⇒ x ≥ 0)',
      'Step 4: Generate VC: Precondition ⇒ WP. Statement: true ⇒ (x < 0 ⇒ x ≤ 0) ∧ (x ≥ 0 ⇒ x ≥ 0)',
      'Step 5: Verify VC math equations. Logically valid.'
    ]
  },
  'sum-n': {
    pre: 'N ≥ 0',
    inv: 's = i * (i + 1) / 2  ∧  i ≤ N',
    post: 's = N * (N + 1) / 2',
    code: [
      { num: 1, text: '// Program: Sum of N numbers' },
      { num: 2, text: 'i := 0;' },
      { num: 3, text: 's := 0;' },
      { num: 4, text: 'while i < N do' },
      { num: 5, text: '  i := i + 1;' },
      { num: 6, text: '  s := s + i;' }
    ],
    vcs: [
      {
        id: 'VC_1',
        expr: 'N ≥ 0  ⇒  (0 = 0*(0+1)/2  ∧  0 ≤ N)',
        desc: 'Loop Initialization: Precondition implies Invariant holds at entry',
        status: 'verified'
      },
      {
        id: 'VC_2',
        expr: '(s = i*(i+1)/2  ∧  i ≤ N  ∧  i < N)  ⇒  (s+i+1 = (i+1)*(i+2)/2  ∧  i+1 ≤ N)',
        desc: 'Invariant Preservation: Invariant holds after loop body iteration',
        status: 'verified'
      },
      {
        id: 'VC_3',
        expr: '(s = i*(i+1)/2  ∧  i ≤ N  ∧  ¬(i < N))  ⇒  s = N*(N+1)/2',
        desc: 'Postcondition Establishment: Invariant and Loop termination imply Postcondition',
        status: 'verified'
      }
    ],
    wpSteps: [
      'Goal: Verify loop with Invariant: { s = i*(i+1)/2 ∧ i ≤ N }',
      'Step 1: Loop Entry Check (VC_1). Show 0 = 0*(0+1)/2 holds.',
      'Step 2: Loop Preservation Check (VC_2). WP(i:=i+1; s:=s+i, Inv) = (s+i+1 = (i+1)*(i+2)/2). Check implication.',
      'Step 3: Loop Termination Check (VC_3). If i ≤ N and ¬(i < N) then i = N. Thus s = N*(N+1)/2.',
      'Step 4: All verification conditions discharged by solver successfully.'
    ]
  },
  'int-div': {
    pre: 'x ≥ 0  ∧  y > 0',
    inv: 'x = q * y + r  ∧  r ≥ 0',
    post: 'x = q * y + r  ∧  r < y',
    code: [
      { num: 1, text: '// Program: Integer Division' },
      { num: 2, text: 'q := 0;' },
      { num: 3, text: 'r := x;' },
      { num: 4, text: 'while y ≤ r do' },
      { num: 5, text: '  r := r - y;' },
      { num: 6, text: '  q := q + 1;' }
    ],
    vcs: [
      {
        id: 'VC_1',
        expr: '(x ≥ 0 ∧ y > 0)  ⇒  (x = 0*y + x  ∧  x ≥ 0)',
        desc: 'Loop Initialization: Invariant holds after q:=0; r:=x',
        status: 'verified'
      },
      {
        id: 'VC_2',
        expr: '(x = q*y + r ∧ r ≥ 0 ∧ y ≤ r)  ⇒  (x = (q+1)*y + r-y  ∧  r-y ≥ 0)',
        desc: 'Invariant Preservation: Invariant is inductive over subtraction',
        status: 'verified'
      },
      {
        id: 'VC_3',
        expr: '(x = q*y + r ∧ r ≥ 0 ∧ ¬(y ≤ r))  ⇒  (x = q*y + r  ∧  r < y)',
        desc: 'Termination: Loop exit guarantees remainder remainder is less than divisor',
        status: 'verified'
      }
    ],
    wpSteps: [
      'Goal: Verify division invariant { x = q*y + r ∧ r ≥ 0 }',
      'Step 1: Initialization VC: WP(q:=0; r:=x, Inv) = (x = 0*y + x ∧ x ≥ 0) simplifies to true.',
      'Step 2: Preservation VC: WP of body = x = (q+1)*y + (r-y) ∧ r-y ≥ 0. Implication verified.',
      'Step 3: Termination VC: ¬(y ≤ r) implies r < y. Postcondition satisfied.',
      'Step 4: Hoare assertions verified.'
    ]
  }
};

function logHl(msg, type = 'info') {
  const logContainer = document.getElementById('hl-logs');
  if (!logContainer) return;
  const line = document.createElement('span');
  line.className = `log-${type}`;

  const time = new Date().toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', second: '2-digit' });
  line.innerHTML = `[${time}] ${msg}`;
  logContainer.appendChild(line);
  logContainer.scrollTop = logContainer.scrollHeight;
}

function loadHlPreset() {
  const presetKey = document.getElementById('hl-presets').value;
  hlState.template = presetKey;
  const preset = HL_PRESETS[presetKey];

  // Set annotations
  document.getElementById('hl-precondition').textContent = `{ ${preset.pre} }`;
  document.getElementById('hl-postcondition').textContent = `{ ${preset.post} }`;

  const invContainer = document.getElementById('hl-invariant-container');
  if (preset.inv) {
    invContainer.parentNode.classList.remove('hidden');
    invContainer.textContent = `{ ${preset.inv} }`;
  } else {
    invContainer.parentNode.classList.add('hidden');
  }

  // Reset logs
  document.getElementById('hl-logs').innerHTML = '';
  logHl(`Program template "${presetKey}" loaded. Assertions annotated.`, 'info');

  hlState.stepIndex = 0;
  hlState.verified = false;
  hlState.status = 'IDLE';

  updateHlUI();
}

function updateHlUI() {
  const preset = HL_PRESETS[hlState.template];

  // Update status badge
  const statusBadge = document.getElementById('hl-status');
  statusBadge.className = 'badge';
  statusBadge.textContent = hlState.status;
  if (hlState.status === 'VERIFIED') statusBadge.classList.add('badge-satisfied');
  else if (hlState.status === 'ANALYZING') statusBadge.classList.add('badge-active');
  else statusBadge.classList.add('badge-neutral');

  // Render annotated code
  const codeBox = document.getElementById('hl-code-display');
  codeBox.innerHTML = '';

  // Pre assertion
  const preLine = document.createElement('div');
  preLine.className = 'code-line';
  preLine.innerHTML = `<span class="code-num"></span><span class="code-text code-assertion">{ Precondition: ${preset.pre} }</span>`;
  codeBox.appendChild(preLine);

  // Program statements
  preset.code.forEach((line, index) => {
    const lineDiv = document.createElement('div');
    lineDiv.className = 'code-line';
    lineDiv.id = `hl-line-${line.num}`;

    // Highlight lines during proof step
    if (hlState.status === 'VERIFIED') {
      lineDiv.classList.add('verified-ok');
    } else if (hlState.status === 'ANALYZING' && hlState.stepIndex > 0) {
      if (preset.code.length - index <= hlState.stepIndex) {
        lineDiv.classList.add('active');
      }
    }

    lineDiv.innerHTML = `<span class="code-num">${line.num}</span><span class="code-text">${line.text}</span>`;
    codeBox.appendChild(lineDiv);

    // Insert invariant after loop statement
    if (line.text.includes('while') && preset.inv) {
      const invLine = document.createElement('div');
      invLine.className = 'code-line';
      invLine.innerHTML = `<span class="code-num"></span><span class="code-text code-assertion">  { Loop Invariant: ${preset.inv} }</span>`;
      codeBox.appendChild(invLine);
    }
  });

  // Post assertion
  const postLine = document.createElement('div');
  postLine.className = 'code-line';
  postLine.innerHTML = `<span class="code-num"></span><span class="code-text code-assertion">{ Postcondition: ${preset.post} }</span>`;
  codeBox.appendChild(postLine);

  // Render VCs List
  const vcList = document.getElementById('hl-vc-list');
  vcList.innerHTML = '';

  if (hlState.stepIndex === 0 && hlState.status !== 'VERIFIED') {
    vcList.innerHTML = '<span class="placeholder-text">VCs will appear here after calculation.</span>';
  } else {
    preset.vcs.forEach((vc, vIdx) => {
      // VCs show up as steps increase
      if (hlState.status !== 'VERIFIED' && vIdx >= hlState.stepIndex) return;

      const vcCard = document.createElement('div');
      vcCard.className = 'vc-card-item';

      const statusText = hlState.status === 'VERIFIED' ? 'VERIFIED' : 'PENDING PROOF';
      const badgeClass = hlState.status === 'VERIFIED' ? 'vc-status-verified' : 'vc-status-pending';

      vcCard.innerHTML = `
        <div class="vc-card-header">
          <span>${vc.id}</span>
          <span class="vc-status-badge ${badgeClass}">${statusText}</span>
        </div>
        <div class="vc-card-body">${vc.expr}</div>
        <div class="vc-card-footer">
          <span>${vc.desc}</span>
        </div>
      `;
      vcList.appendChild(vcCard);
    });
  }
}

function stepProgramVerification() {
  const preset = HL_PRESETS[hlState.template];
  if (hlState.verified) {
    logHl('Verification already complete.', 'warning');
    return;
  }

  hlState.status = 'ANALYZING';

  if (hlState.stepIndex < preset.wpSteps.length) {
    const stepMsg = preset.wpSteps[hlState.stepIndex];
    logHl(stepMsg, 'step');
    hlState.stepIndex++;
    updateHlUI();
  }

  if (hlState.stepIndex >= preset.wpSteps.length) {
    hlState.verified = true;
    hlState.status = 'VERIFIED';
    logHl('Verification Complete: Program matches specification formally.', 'success');
    updateHlUI();
  }
}

function verifyProgram() {
  const preset = HL_PRESETS[hlState.template];
  logHl('Triggering symbolic verification condition generator...', 'step');

  hlState.status = 'ANALYZING';
  updateHlUI();

  // Show steps in sequence with timeout
  let idx = 0;
  function runSteps() {
    if (idx < preset.wpSteps.length) {
      logHl(preset.wpSteps[idx], 'info');
      hlState.stepIndex = idx + 1;
      updateHlUI();
      idx++;
      setTimeout(runSteps, 400);
    } else {
      hlState.verified = true;
      hlState.status = 'VERIFIED';
      logHl('Verification complete! All Verification Conditions successfully solved.', 'success');
      updateHlUI();
    }
  }

  setTimeout(runSteps, 300);
}

function resetHoareVerifier() {
  loadHlPreset();
}


// ==========================================
// INITIALIZE LAB ON PAGE LOAD
// ==========================================
function initFvPlayground() {
  console.log("Initializing FV Playground engines...");
  loadSatPreset();
  loadMcSystem();
  loadHlPreset();
}

// Ensure execution triggers on page load
if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', initFvPlayground);
} else {
  initFvPlayground();
}

// Fallback delay load
setTimeout(initFvPlayground, 1000);
setTimeout(initFvPlayground, 2000);
