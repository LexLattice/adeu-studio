/**
 * Trust Boundary — notices bar for writes, review dispatch, workflow handoff, terminal
 */

import * as state from '../state.js';

export function renderTrustBoundary(container) {
  function render() {
    const notices = state.get('trustNotices');

    if (notices.length === 0) {
      container.innerHTML = '';
      return;
    }

    container.innerHTML = notices.map(notice => `
      <div class="trust-notice trust-notice--${notice.kind}">
        <span>${getIcon(notice.kind)}</span>
        <span>${notice.message}</span>
        <button class="trust-notice-dismiss" data-dismiss="${notice.id}" title="Dismiss">✕</button>
      </div>
    `).join('');

    container.querySelectorAll('[data-dismiss]').forEach(btn => {
      btn.addEventListener('click', () => {
        state.removeTrustNotice(btn.dataset.dismiss);
      });
    });
  }

  state.subscribe('trustNotices', render);
  render();
}

function getIcon(kind) {
  switch (kind) {
    case 'writes': return '🔓';
    case 'review': return '📤';
    case 'workflow': return '⚡';
    case 'terminal': return '⬛';
    default: return '⚠';
  }
}
