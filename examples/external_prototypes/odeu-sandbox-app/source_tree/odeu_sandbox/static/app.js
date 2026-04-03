const parameterDefinitions = [
  { key: 'scarcity', label: 'Scarcity', min: 0.1, max: 0.8, step: 0.01 },
  { key: 'regeneration_rate', label: 'Regeneration', min: 0.04, max: 0.2, step: 0.01 },
  { key: 'misinformation', label: 'Misinformation', min: 0.0, max: 0.8, step: 0.01 },
  { key: 'verification_capacity', label: 'Verification cap.', min: 0.05, max: 1.0, step: 0.01 },
  { key: 'enforcement_capacity', label: 'Enforcement cap.', min: 0.05, max: 1.0, step: 0.01 },
  { key: 'sanction_severity', label: 'Sanction severity', min: 0.4, max: 2.8, step: 0.05 },
  { key: 'initial_legitimacy', label: 'Initial legitimacy', min: 0.0, max: 1.0, step: 0.01 },
  { key: 'initial_operativity', label: 'Initial operativity', min: 0.0, max: 1.0, step: 0.01 },
  { key: 'sanction_consistency', label: 'Sanction consistency', min: 0.0, max: 1.0, step: 0.01 },
  { key: 'archive_capacity', label: 'Archive capacity', min: 0.0, max: 1.0, step: 0.01 },
  { key: 'appeal_availability', label: 'Appeal availability', min: 0.0, max: 1.0, step: 0.01 },
  { key: 'public_epistemics_level', label: 'Public epistemics', min: 0.0, max: 1.0, step: 0.01 },
  { key: 'ai_reliability', label: 'AI reliability', min: 0.0, max: 1.0, step: 0.01 },
];

const metricDefinitions = [
  ['cooperation_rate', 'Cooperation rate'],
  ['commons_health', 'Commons health'],
  ['average_belief_accuracy', 'Belief accuracy'],
  ['epistemic_integrity', 'Epistemic integrity'],
  ['institution_legitimacy', 'Legitimacy'],
  ['institution_operativity', 'Operativity'],
  ['symbolic_gap', 'Symbolic gap'],
  ['sanction_consistency', 'Sanction consistency'],
  ['utility_concentration', 'Capture proxy'],
  ['trust_fragmentation', 'Trust fragmentation'],
];

const archetypeColors = {
  cooperator: '#6be6a8',
  opportunist: '#ff9f6e',
  auditor: '#77b8ff',
  official: '#d4a5ff',
  ai_dependent: '#ffe680',
};

let scenarios = [];
let currentState = null;
let runHandle = null;

const scenarioSelect = document.getElementById('scenarioSelect');
const scenarioDescription = document.getElementById('scenarioDescription');
const parameterGrid = document.getElementById('parameterGrid');
const metricsGrid = document.getElementById('metricsGrid');
const laneCards = document.getElementById('laneCards');
const networkSvg = document.getElementById('networkSvg');
const eventLog = document.getElementById('eventLog');
const reportsList = document.getElementById('reportsList');
const evidenceList = document.getElementById('evidenceList');
const actionsList = document.getElementById('actionsList');
const regimeBadge = document.getElementById('regimeBadge');
const countsSummary = document.getElementById('countsSummary');
const speedInput = document.getElementById('speedInput');
const speedValue = document.getElementById('speedValue');

function api(path, options = {}) {
  return fetch(path, {
    headers: { 'Content-Type': 'application/json' },
    ...options,
  }).then((response) => response.json());
}

function createParameterControls() {
  const html = parameterDefinitions
    .map(
      (item) => `
      <div class="parameter-card">
        <label>
          ${item.label}
          <input id="param_${item.key}" type="range" min="${item.min}" max="${item.max}" step="${item.step}" />
          <span class="value" id="param_${item.key}_value"></span>
        </label>
      </div>`
    )
    .join('');
  parameterGrid.innerHTML =
    html +
    `
      <div class="parameter-card">
        <label>
          AI mode
          <select id="param_ai_mode">
            <option value="none">None</option>
            <option value="accurate">Accurate / audit-supporting</option>
            <option value="sycophantic">Sycophantic / capture-prone</option>
          </select>
        </label>
      </div>`;

  parameterDefinitions.forEach((item) => {
    const slider = document.getElementById(`param_${item.key}`);
    const value = document.getElementById(`param_${item.key}_value`);
    slider.addEventListener('input', () => {
      value.textContent = Number(slider.value).toFixed(2);
    });
  });
}

function setParameterValues(config) {
  parameterDefinitions.forEach((item) => {
    const slider = document.getElementById(`param_${item.key}`);
    const value = document.getElementById(`param_${item.key}_value`);
    slider.value = config[item.key];
    value.textContent = Number(config[item.key]).toFixed(2);
  });
  document.getElementById('param_ai_mode').value = config.ai_mode;
}

function collectOverrides() {
  const overrides = {};
  parameterDefinitions.forEach((item) => {
    overrides[item.key] = Number(document.getElementById(`param_${item.key}`).value);
  });
  overrides.ai_mode = document.getElementById('param_ai_mode').value;
  return overrides;
}

function sparkline(values, key) {
  if (!values.length) {
    return '<svg viewBox="0 0 100 50"></svg>';
  }
  const min = Math.min(...values);
  const max = Math.max(...values);
  const range = Math.max(0.001, max - min);
  const points = values
    .map((value, index) => {
      const x = (index / Math.max(1, values.length - 1)) * 100;
      const y = 48 - ((value - min) / range) * 44;
      return `${x.toFixed(2)},${y.toFixed(2)}`;
    })
    .join(' ');
  const stroke = key === 'symbolic_gap' || key === 'utility_concentration' ? '#ffd166' : '#72d6ff';
  return `
    <svg viewBox="0 0 100 50" preserveAspectRatio="none">
      <polyline fill="none" stroke="${stroke}" stroke-width="2.4" points="${points}"></polyline>
    </svg>`;
}

function renderMetrics(state) {
  const history = state.metrics_history;
  metricsGrid.innerHTML = metricDefinitions
    .map(([key, label]) => {
      const values = history.map((point) => point[key]);
      const current = state.current_metrics[key];
      const klass = key === 'symbolic_gap' || key === 'utility_concentration' || key === 'trust_fragmentation'
        ? (current > 0.45 ? 'bad' : current > 0.25 ? 'warn' : 'good')
        : (current < 0.35 ? 'bad' : current < 0.55 ? 'warn' : 'good');
      return `
        <div class="metric-card">
          <div class="small-note">${label}</div>
          <div class="value ${klass}">${Number(current).toFixed(3)}</div>
          ${sparkline(values, key)}
        </div>`;
    })
    .join('');
}

function renderLaneSummary(state) {
  const laneDescriptions = {
    O: 'Material substrate, commons, archive infrastructure, enforcement capacity.',
    E: 'Beliefs, uncertainty, trust, evidence access, public reporting.',
    D: 'Legitimacy, operativity, sanction consistency, symbolic gap.',
    U: 'Greed, fairness, horizon, concentration, capture pressure.',
  };
  laneCards.innerHTML = Object.entries(state.lane_summary)
    .map(([lane, values]) => `
      <div class="lane-card">
        <h3>${lane}</h3>
        <div class="small-note">${laneDescriptions[lane]}</div>
        <ul>
          ${Object.entries(values)
            .map(([key, value]) => `<li><strong>${key}</strong>: ${value}</li>`)
            .join('')}
        </ul>
      </div>`)
    .join('');
}

function renderCounts(state) {
  const archetypes = Object.entries(state.counts.archetypes)
    .map(([name, value]) => `${name}: ${value}`)
    .join(' · ');
  const actions = Object.entries(state.counts.actions)
    .map(([name, value]) => `${name}: ${value}`)
    .join(' · ');
  countsSummary.textContent = `${archetypes} | ${actions}`;
}

function renderNetwork(state) {
  const agents = [...state.agents].sort((a, b) => a.id.localeCompare(b.id));
  const width = 880;
  const height = 420;
  const centerX = width / 2;
  const centerY = height / 2;
  const radius = Math.min(width, height) * 0.36;
  const positions = {};

  agents.forEach((agent, index) => {
    const angle = (Math.PI * 2 * index) / agents.length - Math.PI / 2;
    positions[agent.id] = {
      x: centerX + Math.cos(angle) * radius,
      y: centerY + Math.sin(angle) * radius,
    };
  });

  const edgeMarkup = state.network_edges
    .map((edge) => {
      const source = positions[edge.source];
      const target = positions[edge.target];
      if (!source || !target) return '';
      const opacity = 0.12 + edge.weight * 0.35;
      return `<line x1="${source.x}" y1="${source.y}" x2="${target.x}" y2="${target.y}" stroke="rgba(184,192,224,${opacity})" stroke-width="1" />`;
    })
    .join('');

  const nodeMarkup = agents
    .map((agent) => {
      const pos = positions[agent.id];
      const fill = archetypeColors[agent.archetype] || '#72d6ff';
      const size = 6 + Math.max(0, Math.min(7, agent.resources - 3));
      const stroke = `rgba(255,255,255,${0.25 + agent.trust_institution * 0.65})`;
      const label = `${agent.id}\n${agent.archetype}\nresources=${agent.resources}\nbelief=${agent.belief_commons}\nuncertainty=${agent.uncertainty}\naction=${agent.last_action}`;
      return `
        <g>
          <circle cx="${pos.x}" cy="${pos.y}" r="${size.toFixed(1)}" fill="${fill}" stroke="${stroke}" stroke-width="1.5">
            <title>${label}</title>
          </circle>
        </g>`;
    })
    .join('');

  networkSvg.innerHTML = edgeMarkup + nodeMarkup;
}

function renderMiniList(container, items, renderer) {
  container.innerHTML = items.length
    ? items.map(renderer).join('')
    : '<div class="mini-item small-note">No items yet.</div>';
}

function renderTraces(state) {
  renderMiniList(
    reportsList,
    state.recent_public_reports.slice().reverse(),
    (report) => `
      <div class="mini-item">
        <strong>${report.source_type}</strong>
        stock=${Number(report.summary_stock).toFixed(1)} · violation=${Number(report.reported_violation_rate).toFixed(2)}<br />
        confidence=${Number(report.confidence).toFixed(2)} · truthful=${String(report.truthful)}
      </div>`
  );
  renderMiniList(
    evidenceList,
    state.recent_evidence.slice().reverse(),
    (item) => `
      <div class="mini-item">
        <strong>${item.kind}</strong>
        proposition=${item.proposition} · value=${Number(item.value).toFixed(2)}<br />
        confidence=${Number(item.confidence).toFixed(2)}
      </div>`
  );
  renderMiniList(
    actionsList,
    state.recent_actions.slice().reverse(),
    (action) => `
      <div class="mini-item">
        <strong>${action.actor_id} → ${action.action_type}</strong>
        ${action.deontic_status} · cost=${Number(action.material_cost).toFixed(2)}<br />
        <span class="small-note">${action.rationale}</span>
      </div>`
  );
}

function renderEventLog(state) {
  eventLog.innerHTML = state.event_log
    .slice()
    .reverse()
    .map((entry) => `<div class="event-entry">${entry}</div>`)
    .join('');
}

function renderState(state) {
  currentState = state;
  regimeBadge.textContent = `${state.meta.regime} · turn ${state.meta.turn}`;
  scenarioDescription.textContent = scenarios.find((item) => item.name === state.meta.scenario)?.description || '';
  renderLaneSummary(state);
  renderMetrics(state);
  renderCounts(state);
  renderNetwork(state);
  renderTraces(state);
  renderEventLog(state);
}

async function loadScenarios() {
  scenarios = await api('/api/scenarios');
  scenarioSelect.innerHTML = scenarios
    .map((scenario) => `<option value="${scenario.name}">${scenario.name}</option>`)
    .join('');
  scenarioSelect.value = 'healthy_baseline';
  scenarioSelect.addEventListener('change', () => {
    const config = scenarios.find((item) => item.name === scenarioSelect.value);
    if (config) {
      setParameterValues(config);
      scenarioDescription.textContent = config.description;
    }
  });
  const initialConfig = scenarios.find((item) => item.name === scenarioSelect.value);
  if (initialConfig) {
    setParameterValues(initialConfig);
    scenarioDescription.textContent = initialConfig.description;
  }
}

async function resetSimulation() {
  const payload = {
    scenario: scenarioSelect.value,
    seed: Number(document.getElementById('seedInput').value),
    overrides: collectOverrides(),
  };
  const state = await api('/api/reset', { method: 'POST', body: JSON.stringify(payload) });
  renderState(state);
}

async function stepSimulation(steps = 1) {
  const state = await api('/api/step', {
    method: 'POST',
    body: JSON.stringify({ steps }),
  });
  renderState(state);
}

function startRun() {
  pauseRun();
  runHandle = setInterval(() => {
    stepSimulation(1);
  }, Number(speedInput.value));
}

function pauseRun() {
  if (runHandle) {
    clearInterval(runHandle);
    runHandle = null;
  }
}

async function init() {
  createParameterControls();
  speedInput.addEventListener('input', () => {
    speedValue.textContent = speedInput.value;
    if (runHandle) {
      startRun();
    }
  });
  document.getElementById('resetBtn').addEventListener('click', resetSimulation);
  document.getElementById('stepBtn').addEventListener('click', () => stepSimulation(1));
  document.getElementById('step10Btn').addEventListener('click', () => stepSimulation(10));
  document.getElementById('startBtn').addEventListener('click', startRun);
  document.getElementById('pauseBtn').addEventListener('click', pauseRun);
  await loadScenarios();
  await resetSimulation();
}

init();
