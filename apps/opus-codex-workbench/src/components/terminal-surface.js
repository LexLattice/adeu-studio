/**
 * Terminal Surface — bounded PTY via host bridge
 *
 * Uses real node-pty through Electron IPC.
 * Write mode is explicitly gated with trust posture notice.
 * Falls back to explicit unavailable state in browser mode.
 *
 * This is a secondary artifact surface, not terminal-first.
 */

import * as state from '../state.js';
import { spawnTerminal, killTerminal, setTerminalWriteMode, isHostAvailable } from '../host-bridge.js';

let terminalUnsubData = null;
let terminalUnsubExit = null;

export function renderTerminalSurface(container) {
  const hostAvailable = state.get('hostAvailable');
  const spawned = state.get('terminalSpawned');
  const interactive = state.get('terminalInteractive');
  const termError = state.get('terminalError');

  if (!hostAvailable) {
    container.innerHTML = `
      <div class="terminal-surface">
        <div class="surface-header">
          <h3>⬛ Terminal <span class="surface-posture">unavailable</span></h3>
        </div>
        <div class="empty-state">
          <div class="empty-state-icon">⬛</div>
          <p>Terminal requires Electron host bridge.</p>
          <p style="color: var(--wb-text-muted);">Run with <code class="mono">npm run electron:dev</code></p>
        </div>
      </div>
    `;
    return;
  }

  if (termError) {
    container.innerHTML = `
      <div class="terminal-surface">
        <div class="surface-header">
          <h3>⬛ Terminal <span class="surface-posture">error</span></h3>
        </div>
        <div class="empty-state">
          <div class="empty-state-icon">⚠</div>
          <p style="color: var(--wb-warning);">${escapeHtml(termError)}</p>
          <button class="btn btn--sm" id="term-retry">Retry</button>
        </div>
      </div>
    `;
    container.querySelector('#term-retry')?.addEventListener('click', () => {
      state.set('terminalError', null);
      spawnTerminal(false);
    });
    return;
  }

  container.innerHTML = `
    <div class="terminal-surface">
      <div class="surface-header">
        <h3>⬛ Terminal <span class="surface-posture">${spawned ? (interactive ? 'interactive' : 'read-only') : 'not started'}</span></h3>
        <div style="display:flex; gap:6px; align-items:center;">
          ${spawned ? `
            <button class="btn btn--sm ${interactive ? 'btn--danger' : ''}" id="term-write-toggle">
              <span class="dot dot--${interactive ? 'red' : 'gray'}"></span>
              Writes: ${interactive ? 'ENABLED' : 'disabled'}
            </button>
            <button class="btn btn--sm" id="term-kill">Kill</button>
          ` : `
            <button class="btn btn--sm" id="term-spawn-ro">Spawn (read-only)</button>
            <button class="btn btn--sm btn--handoff" id="term-spawn-rw">Spawn (interactive)</button>
          `}
        </div>
      </div>
      <div class="terminal-output" id="terminal-output" style="min-height: 200px;">
        ${!spawned ? `
          <div class="empty-state" style="height:100%;">
            <p>Terminal not started.</p>
            <p style="color: var(--wb-text-muted);">Spawn a bounded terminal session to begin.</p>
            ${interactive ? '' : `<p class="badge badge--advisory" style="margin-top:8px;">Terminal sessions are secondary to the chat workbench posture.</p>`}
          </div>
        ` : `
          <div class="terminal-line terminal-line--info">[ADEU Workbench] Bounded terminal session. Workspace: ${escapeHtml(state.get('workspaceRoot') || '.')}</div>
          <div class="terminal-line terminal-line--info">[ADEU Workbench] Write mode: ${interactive ? 'enabled' : 'disabled (read-only)'}</div>
        `}
      </div>
      ${spawned && interactive ? `
        <div class="terminal-input-row">
          <input type="text" class="terminal-input" id="terminal-cmd" placeholder="$ command...">
          <button class="btn btn--sm" id="terminal-run">Run</button>
        </div>
      ` : ''}
    </div>
  `;

  // Wire spawn buttons
  container.querySelector('#term-spawn-ro')?.addEventListener('click', () => spawnTerminal(false));
  container.querySelector('#term-spawn-rw')?.addEventListener('click', () => {
    if (confirm('Spawn interactive terminal? The shell will have write access to the workspace.')) {
      spawnTerminal(true);
    }
  });

  // Wire kill
  container.querySelector('#term-kill')?.addEventListener('click', () => killTerminal());

  // Wire write toggle
  container.querySelector('#term-write-toggle')?.addEventListener('click', () => {
    const next = !interactive;
    if (next) {
      if (confirm('Enable terminal write mode? The shell will have write access.')) {
        setTerminalWriteMode(true);
      }
    } else {
      setTerminalWriteMode(false);
    }
  });

  // Wire terminal data output
  if (spawned && window.hostBridge) {
    const output = container.querySelector('#terminal-output');

    // Clean up old listeners
    if (terminalUnsubData) terminalUnsubData();
    if (terminalUnsubExit) terminalUnsubExit();

    terminalUnsubData = window.hostBridge.onTerminalData((data) => {
      if (output) {
        const line = document.createElement('div');
        line.className = 'terminal-line';
        line.textContent = data;
        output.appendChild(line);
        output.scrollTop = output.scrollHeight;
      }
    });

    terminalUnsubExit = window.hostBridge.onTerminalExit(() => {
      state.set('terminalSpawned', false);
      state.set('terminalInteractive', false);
    });

    // Wire input
    const cmdInput = container.querySelector('#terminal-cmd');
    const runBtn = container.querySelector('#terminal-run');
    if (cmdInput && runBtn) {
      const exec = () => {
        const cmd = cmdInput.value;
        if (!cmd) return;
        window.hostBridge.writeTerminal(cmd + '\n');
        cmdInput.value = '';
      };
      runBtn.addEventListener('click', exec);
      cmdInput.addEventListener('keydown', (e) => {
        if (e.key === 'Enter') exec();
      });
    }
  }
}

function escapeHtml(text) {
  return (text || '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}
