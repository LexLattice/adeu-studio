/**
 * Git Status Surface — real git state from host bridge
 *
 * Shows: branch, changed files (from `git status --porcelain`),
 * recent commits (from `git log`).
 * All data is real, loaded from the Electron host bridge.
 */

import * as state from '../state.js';
import { loadGitState, selectFile } from '../host-bridge.js';

export function renderGitStatus(container) {
  function render() {
    const hostAvailable = state.get('hostAvailable');
    const branch = state.get('gitBranch');
    const files = state.get('gitStatusFiles');
    const log = state.get('gitLog');
    const gitError = state.get('gitError');

    if (!hostAvailable) {
      container.innerHTML = `
        <div class="git-surface">
          <div class="surface-header">
            <h3>🔀 Git Status <span class="surface-posture">unavailable</span></h3>
          </div>
          <div class="empty-state">
            <div class="empty-state-icon">🔀</div>
            <p>Git status requires Electron host bridge.</p>
          </div>
        </div>
      `;
      return;
    }

    container.innerHTML = `
      <div class="git-surface">
        <div class="surface-header">
          <h3>🔀 Git Status <span class="surface-posture">read-only</span></h3>
          <button class="btn btn--sm" id="git-refresh">↻ Refresh</button>
        </div>

        ${gitError ? `
          <div style="padding: 8px 0;">
            <span class="badge badge--warning">⚠ ${escapeHtml(gitError)}</span>
          </div>
        ` : ''}

        <div class="git-branch">
          <span class="git-branch-icon">⑂</span>
          <span>${branch ? escapeHtml(branch) : 'unknown'}</span>
        </div>

        <div>
          <div class="label" style="margin-bottom: 8px;">Changed Files (${files.length})</div>
          ${files.length > 0 ? `
            <div class="git-file-list">
              ${files.map(f => `
                <div class="git-file" data-file-path="${escapeHtml(f.path)}">
                  <span class="git-file-status git-file-status--${f.status.charAt(0)}">${escapeHtml(f.status)}</span>
                  <span>${escapeHtml(f.path)}</span>
                </div>
              `).join('')}
            </div>
          ` : `
            <div style="color: var(--wb-text-muted); font-size: var(--wb-text-sm); padding: 4px 0;">
              Working tree clean.
            </div>
          `}
        </div>

        <div>
          <div class="label" style="margin-bottom: 8px;">Recent Commits (${log.length})</div>
          ${log.length > 0 ? `
            <div class="git-log">
              ${log.map(entry => `
                <div class="git-log-entry">
                  <div style="display:flex; justify-content:space-between; align-items:center;">
                    <span class="git-log-hash">${escapeHtml(entry.short || entry.hash?.slice(0, 7) || '')}</span>
                    <span class="git-log-meta">${escapeHtml(entry.date || '')}</span>
                  </div>
                  <div class="git-log-message">${escapeHtml(entry.message || '')}</div>
                  <div class="git-log-meta">${escapeHtml(entry.author || '')}</div>
                </div>
              `).join('')}
            </div>
          ` : `
            <div style="color: var(--wb-text-muted); font-size: var(--wb-text-sm); padding: 4px 0;">
              No commit history available.
            </div>
          `}
        </div>
      </div>
    `;

    container.querySelector('#git-refresh')?.addEventListener('click', () => loadGitState());

    // Wire file clicks to open in file viewer (with actual content loading)
    container.querySelectorAll('.git-file').forEach(el => {
      el.style.cursor = 'pointer';
      el.addEventListener('click', () => {
        const filePath = el.dataset.filePath;
        if (filePath) {
          // Use selectFile() to actually load content via IPC, not just set state
          selectFile(filePath);
          state.set('activeContextTab', 'files');
          state.set('contextVisible', true);
        }
      });
    });
  }

  state.subscribeMany(['hostAvailable', 'gitBranch', 'gitStatusFiles', 'gitLog', 'gitError'], render);
  render();
}

function escapeHtml(text) {
  return (text || '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}
