/**
 * Status Boundary — truthful provider/build/config/writes/session status
 *
 * Renders real state only:
 * - Session controls: start / stop / restart / clear
 * - ADEU backend: explicitly unavailable with reason
 * - Host bridge: available or not
 * - Provider/build/config: always visible, shown as unconfigured when null
 * - Terminal write posture: scoped to terminal interactive mode only
 */

import * as state from '../state.js';
import {
  startLocalSession,
  stopLocalSession,
  restartLocalSession,
  clearTranscript,
  setTerminalWriteMode,
  applyProfileSelection,
  PROFILE_PRESETS,
} from '../host-bridge.js';

export function renderStatusBoundary(container) {
  function render() {
    const hostAvailable = state.get('hostAvailable');
    const sessionId = state.get('sessionId');
    const sessionStatus = state.get('sessionStatus');
    const adeuStatus = state.get('adeuBackendStatus');
    const adeuReason = state.get('adeuBackendReason');
    const workspaceRoot = state.get('workspaceRoot');
    const terminalInteractive = state.get('terminalInteractive');
    const terminalSpawned = state.get('terminalSpawned');

    // Real values — null means unconfigured (always shown)
    const provider = state.get('provider');
    const codexBuild = state.get('codexBuild');
    const configPath = state.get('configPath');
    const profileLabel = state.get('profileLabel');
    const appServerAvailable = state.get('appServerAvailable');
    const profilePresetId = state.get('profilePresetId') || 'unconfigured';
    const customProfileDraft = state.get('customProfileDraft') || {
      label: 'Custom Profile',
      provider: '',
      codexBuild: '',
      configPath: '',
    };

    const sessionDot = sessionStatus === 'active' ? 'green' :
                       sessionStatus === 'stopped' ? 'amber' : 'gray';

    const hostDot = hostAvailable ? 'green' : 'gray';
    const selectedProfile = PROFILE_PRESETS.find(p => p.id === profilePresetId) || PROFILE_PRESETS[0];

    container.innerHTML = `
      <div class="status-group" id="status-host">
        <span class="dot dot--${hostDot}"></span>
        <span class="label">Host</span>
        <span class="mono">${hostAvailable ? 'electron' : 'browser'}</span>
      </div>

      <div class="status-group" id="status-session">
        <span class="dot dot--${sessionDot}"></span>
        <span class="label">Session</span>
        <span class="mono">${sessionId ? sessionId : 'none'}</span>
        <span class="badge badge--${sessionStatus === 'active' ? 'success' : 'stale'}">${sessionStatus}</span>
      </div>

      <div class="status-group" id="status-backend">
        <span class="dot dot--${adeuStatus === 'connected' ? 'green' : adeuStatus === 'connecting' ? 'amber' : 'gray'}"></span>
        <span class="label">ADEU</span>
        <span class="badge badge--stale" title="${adeuReason || ''}">${adeuStatus}</span>
      </div>

      <div class="status-group" id="status-provider">
        <span class="label">Provider</span>
        ${provider
          ? `<span class="mono">${provider}</span>`
          : `<span class="badge badge--stale">unconfigured</span>`}
      </div>

      <div class="status-group" id="status-build">
        <span class="label">Build</span>
        ${codexBuild
          ? `<span class="mono">${codexBuild}</span>`
          : `<span class="badge badge--stale">unconfigured</span>`}
      </div>

      <div class="status-group" id="status-config">
        <span class="label">Config</span>
        ${configPath
          ? `<span class="mono">${configPath}</span>`
          : `<span class="badge badge--stale">unconfigured</span>`}
      </div>

      <div class="status-group" id="status-profile">
        <span class="label">Profile</span>
        ${profileLabel
          ? `<span class="mono">${escapeHtml(profileLabel)}</span>`
          : `<span class="badge badge--stale">unconfigured</span>`}
      </div>

      <div class="status-group" id="status-app-server">
        <span class="label">App Server</span>
        <span class="badge badge--${appServerAvailable ? 'success' : 'stale'}">${appServerAvailable ? 'available' : 'unavailable'}</span>
      </div>

      ${workspaceRoot ? `
        <div class="status-group" id="status-workspace">
          <span class="label">Workspace</span>
          <span class="mono" title="${workspaceRoot}">${truncatePath(workspaceRoot)}</span>
        </div>
      ` : ''}

      <div class="status-group status-group--profile-controls" id="status-profile-controls">
        <span class="label">Profile Intent</span>
        <select class="select status-select" id="profile-preset-select" title="${escapeHtml(selectedProfile.description)}">
          ${PROFILE_PRESETS.map(p => `
            <option value="${p.id}" ${p.id === profilePresetId ? 'selected' : ''}>${escapeHtml(p.label)}</option>
          `).join('')}
        </select>
        <button class="btn btn--sm" id="profile-apply-btn">Apply + Restart</button>
      </div>

      ${profilePresetId === 'custom' ? `
        <div class="status-group status-group--profile-draft" id="status-profile-draft">
          <input class="input status-input" id="profile-custom-label" placeholder="Profile label"
            value="${escapeHtml(customProfileDraft.label || '')}" />
          <input class="input status-input" id="profile-custom-provider" placeholder="Provider"
            value="${escapeHtml(customProfileDraft.provider || '')}" />
          <input class="input status-input" id="profile-custom-build" placeholder="Build"
            value="${escapeHtml(customProfileDraft.codexBuild || '')}" />
          <input class="input status-input status-input--wide" id="profile-custom-config" placeholder="Config path"
            value="${escapeHtml(customProfileDraft.configPath || '')}" />
        </div>
      ` : ''}

      <div class="status-group status-group--controls" id="status-controls">
        ${sessionStatus === 'idle' ? `
          <button class="btn btn--sm btn--accent" id="btn-start-session">▶ Start Session</button>
        ` : sessionStatus === 'active' ? `
          <button class="btn btn--sm" id="btn-stop-session">⏹ Stop</button>
          <button class="btn btn--sm" id="btn-restart-session">↻ Restart</button>
          <button class="btn btn--sm" id="btn-clear-transcript">Clear</button>
        ` : `
          <button class="btn btn--sm btn--accent" id="btn-start-session">▶ New Session</button>
          <button class="btn btn--sm" id="btn-clear-transcript">Clear</button>
        `}
      </div>

      <div class="status-group status-group--writes" id="status-writes">
        <button class="btn btn--sm ${terminalInteractive ? 'btn--danger' : ''}" id="toggle-writes-btn"
          title="Controls terminal write mode only. Does not grant global filesystem write access."
          ${!terminalSpawned ? 'disabled' : ''}>
          <span class="dot dot--${terminalInteractive ? 'red' : 'gray'}"></span>
          Terminal Writes: ${terminalInteractive ? 'ENABLED' : 'disabled'}
        </button>
      </div>
    `;

    // Wire session controls
    container.querySelector('#btn-start-session')?.addEventListener('click', () => {
      startLocalSession();
    });
    container.querySelector('#btn-stop-session')?.addEventListener('click', () => {
      stopLocalSession();
    });
    container.querySelector('#btn-restart-session')?.addEventListener('click', () => {
      restartLocalSession();
    });
    container.querySelector('#btn-clear-transcript')?.addEventListener('click', () => {
      clearTranscript();
    });

    container.querySelector('#profile-preset-select')?.addEventListener('change', (event) => {
      const nextPresetId = event.target.value;
      state.set('profilePresetId', nextPresetId);
    });

    container.querySelector('#profile-apply-btn')?.addEventListener('click', () => {
      applyProfileSelection(
        state.get('profilePresetId') || 'unconfigured',
        { customDraft: state.get('customProfileDraft'), restartSession: true }
      );
    });

    container.querySelector('#profile-custom-label')?.addEventListener('input', (event) => {
      updateCustomProfileField('label', event.target.value);
    });
    container.querySelector('#profile-custom-provider')?.addEventListener('input', (event) => {
      updateCustomProfileField('provider', event.target.value);
    });
    container.querySelector('#profile-custom-build')?.addEventListener('input', (event) => {
      updateCustomProfileField('codexBuild', event.target.value);
    });
    container.querySelector('#profile-custom-config')?.addEventListener('input', (event) => {
      updateCustomProfileField('configPath', event.target.value);
    });

    // Wire terminal write toggle — scoped to terminal interactive only
    container.querySelector('#toggle-writes-btn')?.addEventListener('click', () => {
      if (!terminalInteractive) {
        if (confirm('Enable terminal write mode? The terminal shell will accept input.')) {
          setTerminalWriteMode(true);
        }
      } else {
        setTerminalWriteMode(false);
      }
    });
  }

  state.subscribeMany([
    'hostAvailable', 'sessionId', 'sessionStatus',
    'adeuBackendStatus', 'adeuBackendReason',
    'workspaceRoot', 'terminalInteractive', 'terminalSpawned',
    'provider', 'codexBuild', 'configPath',
    'profileLabel', 'appServerAvailable', 'profilePresetId', 'customProfileDraft',
  ], render);
  render();
}

function updateCustomProfileField(field, value) {
  const draft = state.get('customProfileDraft') || {};
  state.set('customProfileDraft', {
    ...draft,
    [field]: value,
  });
}

function truncatePath(p) {
  if (!p) return '';
  const parts = p.split('/');
  if (parts.length <= 3) return p;
  return '…/' + parts.slice(-2).join('/');
}

function escapeHtml(text) {
  return (text || '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

// Status group layout styles
const style = document.createElement('style');
style.textContent = `
  .status-group {
    display: inline-flex;
    align-items: center;
    gap: 6px;
    font-size: var(--wb-text-sm);
    padding-right: var(--wb-space-3);
    border-right: 1px solid var(--wb-glass-border);
  }
  .status-group:last-child {
    border-right: none;
    padding-right: 0;
  }
  .status-group--controls {
    display: inline-flex;
    gap: 4px;
  }
  .status-group--profile-controls {
    gap: 8px;
  }
  .status-group--profile-draft {
    gap: 6px;
  }
  .status-select {
    max-width: 220px;
    height: 26px;
    padding: 2px 8px;
  }
  .status-input {
    height: 26px;
    min-width: 110px;
    font-size: var(--wb-text-xs);
    padding: 3px 8px;
  }
  .status-input--wide {
    min-width: 220px;
  }
  .status-group--writes {
    margin-left: auto;
  }
`;
document.head.appendChild(style);
