/**
 * Diff Surface — real git diff from host bridge
 *
 * Renders actual `git diff` output from the workspace.
 * No fabricated diff content.
 * Shows origin-attached review markers when reviews exist for the diff.
 */

import * as state from '../state.js';
import { loadGitState, getReviewRequestsForOrigin } from '../host-bridge.js';

export function renderDiffSurface(container) {
  function render() {
    const hostAvailable = state.get('hostAvailable');
    const gitDiff = state.get('gitDiff');
    const gitError = state.get('gitError');

    if (!hostAvailable) {
      container.innerHTML = `
        <div class="diff-surface">
          <div class="surface-header">
            <h3>± Diff Inspector <span class="surface-posture">unavailable</span></h3>
          </div>
          <div class="empty-state">
            <div class="empty-state-icon">±</div>
            <p>Diff viewer requires Electron host bridge.</p>
          </div>
        </div>
      `;
      return;
    }

    const attachedReviews = getReviewRequestsForOrigin('diff', 'working_tree_diff');

    container.innerHTML = `
      <div class="diff-surface">
        <div class="surface-header">
          <h3>± Diff Inspector <span class="surface-posture">read-only</span></h3>
          <div style="display:flex; gap:6px;">
            <button class="btn btn--sm" id="diff-refresh">↻ Refresh</button>
            <button class="btn btn--sm message-action-btn--review" id="diff-send-review"
              ${!gitDiff ? 'disabled' : ''}>Send For Review</button>
          </div>
        </div>
        ${attachedReviews.length > 0 ? `
          <div class="origin-review-markers">
            ${attachedReviews.map(req => `
              <div class="origin-review-pill" data-review-id="${req.id}">
                <span class="origin-review-pill-icon">📋</span>
                <span class="origin-review-pill-id">${req.id}</span>
                <span class="badge badge--warning">${req.status}</span>
                <button class="origin-review-pill-goto" data-goto-review="${req.id}" title="View in Review dock">→</button>
              </div>
            `).join('')}
          </div>
        ` : ''}
        <div class="diff-content">
          ${gitError ? `
            <div class="empty-state">
              <p style="color: var(--wb-warning);">${escapeHtml(gitError)}</p>
            </div>
          ` : !gitDiff || gitDiff.trim() === '' ? `
            <div class="empty-state">
              <div class="empty-state-icon">✓</div>
              <p>Working tree is clean — no uncommitted changes.</p>
            </div>
          ` : renderDiffLines(gitDiff)}
        </div>
      </div>
    `;

    container.querySelector('#diff-refresh')?.addEventListener('click', () => loadGitState());
    container.querySelector('#diff-send-review')?.addEventListener('click', () => {
      state.set('pendingReviewOrigin', {
        kind: 'diff',
        ref: 'working_tree_diff',
      });
    });

    container.querySelectorAll('[data-goto-review]').forEach(btn => {
      btn.addEventListener('click', (e) => {
        e.stopPropagation();
        state.set('activeContextTab', 'review');
        state.set('contextVisible', true);
      });
    });
  }

  state.subscribeMany(['hostAvailable', 'gitDiff', 'gitError', 'reviewRequests'], render);
  render();
}

function renderDiffLines(diff) {
  const lines = diff.split('\n');
  return lines.map(line => {
    let cls = 'diff-line diff-line--context';
    let gutter = ' ';
    if (line.startsWith('diff ') || line.startsWith('index ')) {
      return `<div class="diff-file-header">${escapeHtml(line)}</div>`;
    } else if (line.startsWith('+++') || line.startsWith('---')) {
      cls = 'diff-line diff-line--context';
    } else if (line.startsWith('+')) {
      cls = 'diff-line diff-line--add';
      gutter = '+';
    } else if (line.startsWith('-')) {
      cls = 'diff-line diff-line--del';
      gutter = '-';
    } else if (line.startsWith('@@')) {
      cls = 'diff-line diff-line--hunk';
      gutter = '⋯';
    }
    return `<div class="${cls}"><span class="diff-gutter">${gutter}</span>${escapeHtml(line)}</div>`;
  }).join('');
}

function escapeHtml(text) {
  return (text || '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}
