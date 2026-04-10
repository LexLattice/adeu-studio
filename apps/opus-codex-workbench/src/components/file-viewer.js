/**
 * File Viewer — read-only file content display (real filesystem via host bridge)
 *
 * Two modes:
 * - Docked tab (context region) showing selected file
 * - Bounded peek overlay
 *
 * Full relative paths preserved for provenance.
 * Origin-attached review markers shown when reviews exist for the current file.
 */

import * as state from '../state.js';
import { selectFile, getReviewRequestsForOrigin } from '../host-bridge.js';

export function renderFileViewer(container) {
  function render() {
    const selectedFile = state.get('selectedFile');
    const fileContent = state.get('fileContent');
    const hostAvailable = state.get('hostAvailable');

    if (!hostAvailable) {
      container.innerHTML = `
        <div class="surface-header">
          <h3>📄 File Viewer <span class="surface-posture">unavailable</span></h3>
        </div>
        <div class="empty-state">
          <div class="empty-state-icon">📄</div>
          <p>File viewer requires Electron host bridge.</p>
          <p style="color: var(--wb-text-muted);">Run with <code class="mono">npm run electron:dev</code></p>
        </div>
      `;
      return;
    }

    if (!selectedFile) {
      container.innerHTML = `
        <div class="surface-header">
          <h3>📄 File Viewer <span class="surface-posture">read-only</span></h3>
        </div>
        <div class="empty-state">
          <div class="empty-state-icon">📄</div>
          <p>Select a file from the tree to view.</p>
        </div>
      `;
      return;
    }

    if (!fileContent) {
      container.innerHTML = `
        <div class="surface-header">
          <h3>📄 File Viewer <span class="surface-posture">read-only</span></h3>
        </div>
        <div class="empty-state"><p>Loading ${escapeHtml(selectedFile)}…</p></div>
      `;
      return;
    }

    if (fileContent.error) {
      container.innerHTML = `
        <div class="surface-header">
          <h3>📄 File Viewer <span class="surface-posture">read-only</span></h3>
        </div>
        <div class="empty-state">
          <div class="empty-state-icon">⚠</div>
          <p>${escapeHtml(selectedFile)}</p>
          <p style="color: var(--wb-warning);">${escapeHtml(fileContent.error)}</p>
        </div>
      `;
      return;
    }

    const lines = fileContent.content.split('\n');
    const attachedReviews = getReviewRequestsForOrigin('file', selectedFile);

    container.innerHTML = `
      <div class="file-viewer">
        <div class="file-viewer-header">
          <span class="file-viewer-path" title="${escapeHtml(selectedFile)}">${escapeHtml(selectedFile)}</span>
          <span class="badge badge--stale">read-only</span>
          <button class="btn btn--sm message-action-btn--review" id="fv-send-review">
            Send For Review
          </button>
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
        <div class="file-viewer-content">
          ${lines.map((line, i) => `
            <div class="file-line">
              <span class="file-line-num">${i + 1}</span>
              <span class="file-line-content">${highlightSyntax(escapeHtml(line))}</span>
            </div>
          `).join('')}
        </div>
      </div>
    `;

    container.querySelector('#fv-send-review')?.addEventListener('click', () => {
      state.set('pendingReviewOrigin', {
        kind: 'file',
        ref: selectedFile,
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

  state.subscribeMany(['selectedFile', 'fileContent', 'hostAvailable', 'reviewRequests'], render);
  render();
}

/**
 * Bounded peek overlay — same-context reachable file inspection.
 */
export function renderPeekOverlay(overlayContainer) {
  function render() {
    const peek = state.get('peekFile');

    if (!peek) {
      overlayContainer.innerHTML = '';
      return;
    }

    if (peek.error) {
      overlayContainer.innerHTML = `
        <div class="peek-overlay-backdrop" id="peek-backdrop"></div>
        <div class="peek-overlay">
          <div class="peek-header">
            <h3>${escapeHtml(peek.path)}</h3>
            <button class="peek-close" id="peek-close">✕ Close</button>
          </div>
          <div class="peek-body">
            <div class="empty-state">
              <p style="color: var(--wb-warning);">${escapeHtml(peek.error)}</p>
            </div>
          </div>
        </div>
      `;
      wireClose(overlayContainer);
      return;
    }

    const lines = (peek.content || '').split('\n');
    const attachedReviews = getReviewRequestsForOrigin('file', peek.path);

    overlayContainer.innerHTML = `
      <div class="peek-overlay-backdrop" id="peek-backdrop"></div>
      <div class="peek-overlay">
        <div class="peek-header">
          <h3 title="${escapeHtml(peek.path)}">${escapeHtml(peek.path)}</h3>
          <span class="badge badge--stale">peek · read-only</span>
          <button class="peek-close" id="peek-close">✕ Close</button>
        </div>
        ${attachedReviews.length > 0 ? `
          <div class="origin-review-markers" style="padding: 0 16px;">
            ${attachedReviews.map(req => `
              <div class="origin-review-pill">
                <span class="origin-review-pill-icon">📋</span>
                <span class="origin-review-pill-id">${req.id}</span>
                <span class="badge badge--warning">${req.status}</span>
              </div>
            `).join('')}
          </div>
        ` : ''}
        <div class="peek-body">
          <div class="file-viewer-content">
            ${lines.map((line, i) => `
              <div class="file-line">
                <span class="file-line-num">${i + 1}</span>
                <span class="file-line-content">${highlightSyntax(escapeHtml(line))}</span>
              </div>
            `).join('')}
          </div>
        </div>
        <div class="peek-actions">
          <button class="btn" id="peek-open-context">Open in Context Pane</button>
          <button class="btn btn--handoff" id="peek-send-review">Send For Review</button>
        </div>
      </div>
    `;

    wireClose(overlayContainer);

    overlayContainer.querySelector('#peek-open-context')?.addEventListener('click', () => {
      selectFile(peek.path);
      state.set('activeContextTab', 'files');
      state.set('contextVisible', true);
      state.set('peekFile', null);
    });

    overlayContainer.querySelector('#peek-send-review')?.addEventListener('click', () => {
      state.set('pendingReviewOrigin', {
        kind: 'file',
        ref: peek.path,
      });
      state.set('peekFile', null);
    });
  }

  function wireClose(c) {
    c.querySelector('#peek-backdrop')?.addEventListener('click', () => state.set('peekFile', null));
    c.querySelector('#peek-close')?.addEventListener('click', () => state.set('peekFile', null));
  }

  state.subscribeMany(['peekFile', 'reviewRequests'], render);
  render();
}

function escapeHtml(text) {
  return (text || '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
}

function highlightSyntax(text) {
  return text
    .replace(/\b(import|export|from|const|let|var|function|return|if|else|for|while|class|new|typeof|async|await|default|def|elif|try|except|raise|with|as|yield)\b/g,
      '<span class="tok-keyword">$1</span>')
    .replace(/('(?:[^'\\]|\\.)*'|"(?:[^"\\]|\\.)*"|`(?:[^`\\]|\\.)*`)/g,
      '<span class="tok-string">$1</span>')
    .replace(/(\/\/.*$|#.*$)/gm, '<span class="tok-comment">$1</span>')
    .replace(/\b(\d+\.?\d*)\b/g, '<span class="tok-number">$1</span>');
}
