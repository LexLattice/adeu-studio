/**
 * ADEU Codex Desktop Workbench — State Store
 *
 * Simple pub/sub state management. Each state slice is an observable value.
 * Components subscribe to changes and re-render only relevant DOM.
 *
 * All defaults are truthful: no fabricated session identity, no fake provider/build,
 * no simulated connection state. Values start as null/unavailable and are populated
 * only from real host bridge calls or explicit operator actions.
 */

/** @type {Map<string, Set<Function>>} */
const listeners = new Map();

const PERSISTENCE_KEY = 'adeu.workbench.state.v1';
const PERSISTED_KEYS = new Set([
  'reviewRequests',
  'workflowRequests',
  'recentSessions',
  'provider',
  'codexBuild',
  'configPath',
  'profileLabel',
  'appServerAvailable',
  'profilePresetId',
  'customProfileDraft',
]);

/** @type {Record<string, any>} */
const store = {
  // ── Host Bridge ───────────────────────────────────────────
  hostAvailable: false,        // true only when window.hostBridge exists (Electron)
  workspaceRoot: null,         // populated from host bridge

  // ── Local Session (host-local, not ADEU backend) ─────────
  sessionId: null,
  sessionStatus: 'idle',       // idle | active | stopped
  sessionStartedAt: null,

  // ── ADEU Backend (not wired — explicitly unavailable) ────
  adeuBackendStatus: 'unavailable',  // unavailable | connecting | connected | error
  adeuBackendReason: 'ADEU/Codex backend is not connected. No real provider is configured.',
  codexBuild: null,
  provider: null,
  configPath: null,
  profileLabel: null,
  appServerAvailable: false,
  profilePresetId: 'unconfigured',
  customProfileDraft: {
    label: 'Custom Profile',
    provider: '',
    codexBuild: '',
    configPath: '',
  },

  // ── Transcript (local session messages only) ─────────────
  messages: [],

  // ── File state ────────────────────────────────────────────
  fileTree: [],          // populated from host fs:readDir
  selectedFile: null,    // full relative path, not flattened name
  fileContent: null,     // { error, content } from host
  peekFile: null,        // { path, content } for bounded peek overlay

  // ── Git state (populated from real host bridge) ──────────
  gitBranch: null,
  gitStatusFiles: [],    // parsed from git status --porcelain
  gitDiff: null,
  gitLog: [],
  gitError: null,

  // ── Terminal state ────────────────────────────────────────
  terminalSpawned: false,
  terminalInteractive: false,
  terminalError: null,

  // ── Review requests (local request state only) ───────────
  reviewRequests: [],        // local request tokens, no fake completion

  // ── Workflow requests (local request state only) ─────────
  workflowRequests: [],      // local request tokens, no fake completion
  recentSessions: [],        // local-only history for sidebar recency lane

  // ── UI state ──────────────────────────────────────────────
  activeContextTab: 'files',
  contextVisible: false,
  sidebarCollapsed: false,
  pendingReviewOrigin: null,   // { kind, ref, scope }

  // ── Trust notices ─────────────────────────────────────────
  trustNotices: [],

  // ── General ───────────────────────────────────────────────
  error: null,
  isBusy: false,
};

hydratePersistedState();

/**
 * Get a state value.
 * @param {string} key
 * @returns {any}
 */
export function get(key) {
  return store[key];
}

/**
 * Set a state value and notify listeners.
 * @param {string} key
 * @param {any} value
 */
export function set(key, value) {
  const prev = store[key];
  store[key] = value;
  persistIfNeeded(key);
  if (prev !== value) {
    notify(key);
  }
}

/**
 * Update a state value with a function.
 * @param {string} key
 * @param {(prev: any) => any} fn
 */
export function update(key, fn) {
  const prev = store[key];
  const next = fn(prev);
  store[key] = next;
  persistIfNeeded(key);
  notify(key);
}

/**
 * Subscribe to changes on a state key.
 * @param {string} key
 * @param {(value: any) => void} fn
 * @returns {() => void} Unsubscribe function
 */
export function subscribe(key, fn) {
  if (!listeners.has(key)) {
    listeners.set(key, new Set());
  }
  listeners.get(key).add(fn);
  return () => {
    listeners.get(key)?.delete(fn);
  };
}

/**
 * Subscribe to multiple keys.
 * @param {string[]} keys
 * @param {() => void} fn
 * @returns {() => void}
 */
export function subscribeMany(keys, fn) {
  const unsubs = keys.map(k => subscribe(k, fn));
  return () => unsubs.forEach(u => u());
}

/**
 * Notify all listeners for a key.
 * @param {string} key
 */
function notify(key) {
  const fns = listeners.get(key);
  if (fns) {
    for (const fn of fns) {
      try { fn(store[key]); } catch (e) { console.error(`State listener error [${key}]:`, e); }
    }
  }
}

function hydratePersistedState() {
  if (!hasLocalStorage()) return;
  try {
    const raw = window.localStorage.getItem(PERSISTENCE_KEY);
    if (!raw) return;
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed !== 'object') return;
    for (const key of PERSISTED_KEYS) {
      if (Object.prototype.hasOwnProperty.call(parsed, key)) {
        store[key] = parsed[key];
      }
    }
  } catch (err) {
    console.warn('[State] Failed to hydrate persisted slices:', err);
  }
}

function persistIfNeeded(key) {
  if (!PERSISTED_KEYS.has(key) || !hasLocalStorage()) return;
  try {
    const payload = {};
    for (const persistedKey of PERSISTED_KEYS) {
      payload[persistedKey] = store[persistedKey];
    }
    window.localStorage.setItem(PERSISTENCE_KEY, JSON.stringify(payload));
  } catch (err) {
    console.warn('[State] Failed to persist slices:', err);
  }
}

function hasLocalStorage() {
  return typeof window !== 'undefined' && window.localStorage != null;
}

/**
 * Add a message to the transcript.
 * @param {'user' | 'assistant' | 'system'} role
 * @param {string} text
 * @param {object} [meta]
 */
export function addMessage(role, text, meta = {}) {
  update('messages', msgs => [
    ...msgs,
    {
      id: crypto.randomUUID?.() ?? `${Date.now()}-${Math.random().toString(16).slice(2)}`,
      role,
      text,
      time: new Date().toISOString(),
      ...meta,
    },
  ]);
}

/**
 * Add a trust boundary notice.
 * @param {'writes' | 'review' | 'workflow' | 'terminal'} kind
 * @param {string} message
 */
export function addTrustNotice(kind, message) {
  const id = crypto.randomUUID?.() ?? `${Date.now()}`;
  update('trustNotices', notices => [...notices, { id, kind, message }]);
  return id;
}

/**
 * Remove a trust notice by id.
 * @param {string} id
 */
export function removeTrustNotice(id) {
  update('trustNotices', notices => notices.filter(n => n.id !== id));
}
