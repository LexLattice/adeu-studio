/**
 * ADEU Codex Desktop Workbench — Host Bridge
 *
 * This module mediates between the renderer state store and the Electron
 * host process. It ONLY exposes real, truthful capabilities:
 *
 * REAL (host-owned):
 *   - workspace root identity
 *   - bounded filesystem reads
 *   - git status/branch/diff/log
 *   - PTY terminal spawn/write/kill
 *
 * UNAVAILABLE (requires real ADEU backend):
 *   - Codex session management (adeu.get_app_state, etc.)
 *   - Workflow execution (adeu.run_workflow)
 *   - Review dispatch to external targets
 *   - Evidence bundle retrieval
 *   - Provider/build/config identity
 *   - Assistant responses
 *
 * When running outside Electron (browser-only fallback), all host bridge
 * calls return explicit unavailable state.
 */

import * as state from './state.js';

const MAX_REQUEST_HISTORY = 100;
const MAX_RECENT_SESSIONS = 12;

// ── Host Bridge Availability ────────────────────────────────

/**
 * Check if we're running inside Electron with the host bridge available.
 */
export function isHostAvailable() {
  return typeof window !== 'undefined' && window.hostBridge != null;
}

/**
 * Initialize the host bridge. Call once at startup.
 */
export async function initHostBridge() {
  const available = isHostAvailable();
  state.set('hostAvailable', available);

  if (available) {
    try {
      const root = await window.hostBridge.getWorkspaceRoot();
      state.set('workspaceRoot', root);
    } catch (err) {
      console.error('[HostBridge] Failed to get workspace root:', err);
      state.set('workspaceRoot', null);
    }
  } else {
    state.addMessage('system',
      'Running in browser mode. Host bridge is not available. ' +
      'Use `npm run electron:dev` to launch the desktop workbench with real filesystem, git, and terminal access.'
    );
  }
}

// ── Local Session Management ────────────────────────────────

function archiveCurrentSession(reason = 'stopped') {
  const sessionId = state.get('sessionId');
  const sessionStartedAt = state.get('sessionStartedAt');
  if (!sessionId || !sessionStartedAt) return;

  const archived = {
    id: sessionId,
    status: reason,
    startedAt: sessionStartedAt,
    endedAt: new Date().toISOString(),
    profileLabel: state.get('profileLabel') || 'unconfigured',
  };

  state.update('recentSessions', sessions => {
    const prior = Array.isArray(sessions) ? sessions : [];
    const withoutCurrent = prior.filter(s => s.id !== archived.id);
    return [archived, ...withoutCurrent].slice(0, MAX_RECENT_SESSIONS);
  });
}

/**
 * Start a local host session.
 * This is NOT a Codex/ADEU session — it only establishes local workbench state.
 */
export function startLocalSession() {
  if (state.get('sessionStatus') === 'active') {
    archiveCurrentSession('restarted');
  }

  const id = `local_${Date.now().toString(36)}`;
  state.set('sessionId', id);
  state.set('sessionStatus', 'active');
  state.set('sessionStartedAt', new Date().toISOString());
  state.addMessage('system', `Local session ${id} started. Workspace is ready for bounded operations.`);

  if (state.get('adeuBackendStatus') === 'unavailable') {
    state.addMessage('system',
      'ADEU/Codex backend is not connected. Chat messages will be recorded locally but ' +
      'no assistant responses will be generated. Review and workflow dispatch will create ' +
      'local request tokens only.'
    );
  }
}

/**
 * Stop the local session.
 */
export function stopLocalSession() {
  const id = state.get('sessionId');
  if (!id || state.get('sessionStatus') !== 'active') return;

  state.set('sessionStatus', 'stopped');
  archiveCurrentSession('stopped');
  state.addMessage('system', `Session ${id} stopped.`);
}

/**
 * Restart: stop then start a new session.
 */
export function restartLocalSession() {
  if (state.get('sessionStatus') === 'active') {
    stopLocalSession();
  }
  startLocalSession();
}

/**
 * Clear the transcript.
 */
export function clearTranscript() {
  state.set('messages', []);
}

// ── Filesystem (real, via host bridge) ──────────────────────

/**
 * Read a directory from the real filesystem via host bridge.
 * @param {string} dirPath — relative to workspace root
 */
export async function readDir(dirPath = '') {
  if (!isHostAvailable()) {
    return [];
  }
  try {
    return await window.hostBridge.readDir(dirPath);
  } catch (err) {
    console.error('[HostBridge] readDir error:', err);
    return [];
  }
}

/**
 * Read file content from the real filesystem via host bridge.
 * @param {string} filePath — relative to workspace root
 */
export async function readFile(filePath) {
  if (!isHostAvailable()) {
    return { error: 'Host bridge not available', content: null };
  }
  try {
    return await window.hostBridge.readFile(filePath);
  } catch (err) {
    return { error: err.message, content: null };
  }
}

/**
 * Load the file tree starting from the workspace root.
 * Populates state.fileTree with real directory entries.
 */
export async function loadFileTree(dirPath = '') {
  state.set('isBusy', true);
  const entries = await readDir(dirPath);
  if (dirPath === '') {
    state.set('fileTree', entries);
  }
  state.set('isBusy', false);
  return entries;
}

/**
 * Select a file and load its content.
 * @param {string} filePath — full relative path from workspace root
 */
export async function selectFile(filePath) {
  state.set('selectedFile', filePath);
  state.set('fileContent', null);
  const result = await readFile(filePath);
  state.set('fileContent', result);
}

/**
 * Open a file in quick-peek overlay mode.
 * @param {string} filePath — full relative path
 */
export async function peekFile(filePath) {
  const result = await readFile(filePath);
  state.set('peekFile', {
    path: filePath,
    content: result.content,
    error: result.error,
  });
}

// ── Git (real, via host bridge) ─────────────────────────────

/**
 * Load all git state from the real workspace.
 */
export async function loadGitState() {
  if (!isHostAvailable()) {
    state.set('gitError', 'Host bridge not available');
    return;
  }

  try {
    const [branchResult, statusResult, diffResult, logResult] = await Promise.all([
      window.hostBridge.gitBranch(),
      window.hostBridge.gitStatus(),
      window.hostBridge.gitDiff(),
      window.hostBridge.gitLog(10),
    ]);

    state.set('gitBranch', branchResult.error ? null : branchResult.branch);
    state.set('gitDiff', diffResult.error ? null : diffResult.output);
    state.set('gitLog', logResult.error ? [] : logResult.entries);
    state.set('gitError', branchResult.error || statusResult.error || null);

    // Parse porcelain status
    if (statusResult.output != null) {
      const files = statusResult.output.trim().split('\n').filter(Boolean).map(line => {
        const status = line.substring(0, 2).trim();
        const filePath = line.substring(3);
        return { status, path: filePath };
      });
      state.set('gitStatusFiles', files);
    }
  } catch (err) {
    state.set('gitError', err.message);
  }
}

// ── Terminal (real, via host bridge, bounded) ────────────────

/**
 * Spawn a bounded terminal session.
 * @param {boolean} interactive — whether writes are enabled
 */
export async function spawnTerminal(interactive = false) {
  if (!isHostAvailable()) {
    state.set('terminalError', 'Host bridge not available. Terminal requires Electron desktop mode.');
    return;
  }

  if (interactive) {
    state.addTrustNotice('terminal',
      'Interactive terminal spawned. Shell has write access to the workspace.'
    );
  }

  const result = await window.hostBridge.spawnTerminal(interactive);
  if (result.error) {
    state.set('terminalError', result.error);
    state.set('terminalSpawned', false);
  } else {
    state.set('terminalSpawned', true);
    state.set('terminalInteractive', interactive);
    state.set('terminalError', null);
  }
}

/**
 * Kill the active terminal session.
 */
export async function killTerminal() {
  if (!isHostAvailable()) return;
  await window.hostBridge.killTerminal();
  state.set('terminalSpawned', false);
  state.set('terminalInteractive', false);
}

/**
 * Toggle terminal write mode.
 */
export async function setTerminalWriteMode(enabled) {
  if (!isHostAvailable()) return;
  const result = await window.hostBridge.setTerminalWriteMode(enabled);
  state.set('terminalInteractive', result.writeEnabled);

  if (enabled) {
    state.addTrustNotice('terminal', 'Terminal write mode enabled.');
  }
}

// ── Profile / Build / Config (local intent surface) ─────────

export const PROFILE_PRESETS = [
  {
    id: 'unconfigured',
    label: 'Unconfigured',
    description: 'No launch profile intent selected.',
    provider: null,
    codexBuild: null,
    configPath: null,
    appServerAvailable: false,
  },
  {
    id: 'adeu_codex_default',
    label: 'ADEU Codex Default (intent)',
    description: 'Local profile intent for the default ADEU Codex lane.',
    provider: 'codex',
    codexBuild: 'gpt-5.4',
    configPath: '~/.codex/config.toml',
    appServerAvailable: false,
  },
  {
    id: 'adeu_review_lane',
    label: 'ADEU Review Lane (intent)',
    description: 'Local profile intent for structured review-focused work.',
    provider: 'codex',
    codexBuild: 'gpt-5.3-codex',
    configPath: '~/.codex/review.toml',
    appServerAvailable: false,
  },
  {
    id: 'custom',
    label: 'Custom',
    description: 'Operator-defined profile/build/config intent.',
    provider: null,
    codexBuild: null,
    configPath: null,
    appServerAvailable: false,
  },
];

/**
 * Apply a local profile/build/config intent selection.
 * This does not establish a real ADEU backend connection.
 * @param {string} profileId
 * @param {{customDraft?: {label?: string, provider?: string, codexBuild?: string, configPath?: string}, restartSession?: boolean}} [options]
 */
export function applyProfileSelection(profileId, options = {}) {
  const { customDraft = null, restartSession = true } = options;
  const selected = PROFILE_PRESETS.find(p => p.id === profileId) || PROFILE_PRESETS[0];
  const usingCustom = selected.id === 'custom';

  let profileLabel = selected.label;
  let provider = selected.provider;
  let codexBuild = selected.codexBuild;
  let configPath = selected.configPath;

  if (usingCustom) {
    const safeDraft = customDraft && typeof customDraft === 'object' ? customDraft : {};
    const trimmedLabel = (safeDraft.label || '').trim();
    const trimmedProvider = (safeDraft.provider || '').trim();
    const trimmedBuild = (safeDraft.codexBuild || '').trim();
    const trimmedConfig = (safeDraft.configPath || '').trim();
    profileLabel = trimmedLabel || 'Custom Profile';
    provider = trimmedProvider || null;
    codexBuild = trimmedBuild || null;
    configPath = trimmedConfig || null;
  }

  state.set('profilePresetId', selected.id);
  state.set('profileLabel', selected.id === 'unconfigured' ? null : profileLabel);
  state.set('provider', provider);
  state.set('codexBuild', codexBuild);
  state.set('configPath', configPath);
  state.set('appServerAvailable', false);

  const profileText = selected.id === 'unconfigured' ? 'unconfigured' : profileLabel;
  state.addMessage(
    'system',
    `Profile intent updated: ${profileText}. Backend remains unavailable until ADEU/Codex host wiring is connected.`
  );

  if (restartSession && state.get('sessionStatus') === 'active') {
    restartLocalSession();
    state.addMessage('system', 'Local session restarted to apply updated profile intent.');
  }
}

// ── Chat (local recording only) ─────────────────────────────

/**
 * Send a message. Records locally. No assistant response is fabricated.
 * If a real ADEU backend were connected, this would dispatch to the provider.
 */
export function sendMessage(text) {
  if (!text.trim()) return;
  state.addMessage('user', text);

  if (state.get('adeuBackendStatus') !== 'connected') {
    state.addMessage('system',
      'Message recorded locally. No ADEU/Codex provider is connected to generate a response.'
    );
  }
}

// ── Review Dispatch (local request tokens only) ─────────────

/**
 * Create a local review request. Does NOT execute against a real backend.
 * @param {string} originKind — 'reply' | 'file' | 'diff'
 * @param {string} originRef — message id, file path, or diff identifier
 * @param {string} targetId — review target identifier
 * @param {string} [scope] — scope summary
 */
export function createReviewRequest(originKind, originRef, targetId, scope = 'full') {
  const requestId = `rev_${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 6)}`;
  const request = {
    id: requestId,
    originKind,
    originRef,
    targetId,
    scope,
    status: 'not_executed',
    statusReason: 'ADEU backend not connected. Request recorded locally.',
    createdAt: new Date().toISOString(),
    sessionId: state.get('sessionId') || null,
    returnedArtifacts: [],
  };

  state.update('reviewRequests', reqs => [request, ...reqs].slice(0, MAX_REQUEST_HISTORY));
  state.addTrustNotice('review', `Review request ${requestId} created (local only — not dispatched to backend).`);
  state.addMessage('system',
    `Review request ${requestId} created for ${originKind}:${originRef} → ${targetId}. ` +
    `Status: not_executed (no ADEU backend connected).`
  );

  return request;
}

// ── Workflow Dispatch (local request tokens only) ───────────

/**
 * Create a local workflow request. Does NOT execute against a real backend.
 * @param {string} templateId
 * @param {string} prompt
 */
export function createWorkflowRequest(templateId, prompt) {
  const requestId = `wf_${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 6)}`;
  const request = {
    id: requestId,
    templateId,
    prompt,
    status: 'not_executed',
    statusReason: 'ADEU backend not connected. Request recorded locally.',
    createdAt: new Date().toISOString(),
    sessionId: state.get('sessionId') || null,
    evidenceId: null,
    returnedArtifacts: [],
  };

  state.update('workflowRequests', reqs => [request, ...reqs].slice(0, MAX_REQUEST_HISTORY));
  state.addTrustNotice('workflow',
    `Workflow request ${requestId} created (local only — not dispatched to backend).`
  );
  state.addMessage('system',
    `Workflow request ${requestId} (${templateId}) recorded locally. ` +
    `Status: not_executed (no ADEU backend connected).`
  );

  return request;
}

// ── Review Origin Queries ───────────────────────────────────

/**
 * Find all review requests that originated from a specific origin.
 * Used by origin surfaces to render attached review state markers.
 * @param {string} kind — 'reply' | 'file' | 'diff'
 * @param {string} ref — message id, file path, or diff identifier
 */
export function getReviewRequestsForOrigin(kind, ref) {
  const requests = state.get('reviewRequests');
  return requests.filter(r => r.originKind === kind && r.originRef === ref);
}

// ── Review Targets (local knowledge, not wired to backend) ──

export const REVIEW_TARGETS = [
  {
    id: 'gpt-5.4-review',
    name: 'GPT-5.4 Code Review',
    description: 'Structured code review via GPT-5.4.',
    status: 'unavailable',
    reason: 'Requires ADEU backend connection.',
  },
  {
    id: 'gemini-pro-review',
    name: 'Gemini Pro Review',
    description: 'Intent stress / structured review via Gemini Pro.',
    status: 'unavailable',
    reason: 'Requires ADEU backend connection.',
  },
  {
    id: 'manual-review',
    name: 'Manual Review Queue',
    description: 'Add to maintainer review queue.',
    status: 'unavailable',
    reason: 'Requires ADEU backend connection.',
  },
];

// ── Workflow Templates (local knowledge, not wired to backend) ──

export const WORKFLOW_TEMPLATES = [
  {
    id: 'adeu.workflow.pipeline_worker.v0',
    description: 'Run a bounded pipeline worker task.',
    status: 'unavailable',
  },
  {
    id: 'adeu.workflow.code_review.v0',
    description: 'Dispatch for structured code review.',
    status: 'unavailable',
  },
  {
    id: 'adeu.workflow.intent_stress.v0',
    description: 'Run six-lane intent stress analysis.',
    status: 'unavailable',
  },
  {
    id: 'adeu.workflow.brokered_reflexive.v0',
    description: 'Compile and execute brokered reflexive orchestration.',
    status: 'unavailable',
  },
];
