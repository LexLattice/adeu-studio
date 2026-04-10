/**
 * Review Routing Surface — governed review dispatch
 *
 * Creates local review request tokens. Does NOT dispatch to a real backend.
 * Each request shows:
 *   - origin identity (kind + ref with full path provenance)
 *   - scope summary
 *   - advisory-only posture
 *   - request id (local token)
 *   - status: not_executed (no real ADEU backend)
 *   - reason for unavailability
 *
 * Returned evidence is NOT fabricated.
 */

import * as state from '../state.js';
import { createReviewRequest, REVIEW_TARGETS } from '../host-bridge.js';

export function renderReviewRouting(container) {
  function render() {
    const requests = state.get('reviewRequests');
    const adeuStatus = state.get('adeuBackendStatus');

    container.innerHTML = `
      <div class="review-surface">
        <div class="surface-header">
          <h3>📋 Review Dispatch <span class="surface-posture">advisory · bounded</span></h3>
          <span class="badge badge--${adeuStatus === 'connected' ? 'success' : 'stale'}">${adeuStatus}</span>
        </div>

        <div>
          <div class="label" style="margin-bottom: 8px;">Review Targets</div>
          <div style="display:flex; flex-direction:column; gap:6px;">
            ${REVIEW_TARGETS.map(t => `
              <div class="review-request" style="cursor:default;">
                <div style="display:flex; justify-content:space-between; align-items:center;">
                  <span style="font-weight:500;">${t.name}</span>
                  <span class="badge badge--stale">${t.status}</span>
                </div>
                <div style="font-size: var(--wb-text-sm); color: var(--wb-text-secondary);">
                  ${t.description}
                </div>
                <div style="font-size: var(--wb-text-xs); color: var(--wb-text-muted); margin-top:2px;">
                  ${t.reason}
                </div>
              </div>
            `).join('')}
          </div>
        </div>

        <div>
          <div class="label" style="margin-bottom: 8px;">Request History (${requests.length})</div>
          ${requests.length > 0 ? `
            <div style="display:flex; flex-direction:column; gap:8px;">
              ${requests.map(req => `
                <div class="review-request">
                  <div class="review-request-header">
                    <span class="review-request-id">${req.id}</span>
                    <span class="badge badge--warning">${req.status}</span>
                  </div>
                  <div class="review-field">
                    <span class="review-field-label">Origin</span>
                    <span class="review-field-value">${escapeHtml(req.originKind)}: ${escapeHtml(req.originRef)}</span>
                  </div>
                  <div class="review-field">
                    <span class="review-field-label">Target</span>
                    <span class="review-field-value">${escapeHtml(req.targetId)}</span>
                  </div>
                  <div class="review-field">
                    <span class="review-field-label">Scope</span>
                    <span class="review-field-value">${escapeHtml(req.scope)}</span>
                  </div>
                  <div class="review-field">
                    <span class="review-field-label">Posture</span>
                    <span class="badge badge--advisory">advisory</span>
                  </div>
                  <div class="review-field">
                    <span class="review-field-label">Created</span>
                    <span class="review-field-value">${formatTime(req.createdAt)}</span>
                  </div>
                  <div style="margin-top:4px; padding:6px 8px; background:var(--wb-stale-bg); border-radius:var(--wb-radius-sm); font-size:var(--wb-text-xs); color:var(--wb-text-muted);">
                    ${escapeHtml(req.statusReason)}
                  </div>
                  ${req.returnedArtifacts.length > 0 ? `
                    <div class="review-returned">
                      <span class="label" style="color: var(--wb-advisory);">Returned Artifacts</span>
                      <div class="mono" style="margin-top:4px;">${req.returnedArtifacts.join(', ')}</div>
                    </div>
                  ` : ''}
                </div>
              `).join('')}
            </div>
          ` : `
            <div class="empty-state" style="padding: 16px 0;">
              <p>No review requests yet.</p>
              <p style="color: var(--wb-text-muted);">Use "Send For Review" on a message, file, or diff to create a request.</p>
            </div>
          `}
        </div>
      </div>
    `;
  }

  state.subscribeMany(['reviewRequests', 'adeuBackendStatus'], render);
  render();
}

/**
 * Review target picker overlay — shown when user clicks "Send For Review"
 */
export function renderReviewPicker(overlayContainer) {
  function render() {
    const pending = state.get('pendingReviewOrigin');
    if (!pending) {
      overlayContainer.innerHTML = '';
      return;
    }

    overlayContainer.innerHTML = `
      <div class="peek-overlay-backdrop" id="review-picker-backdrop"></div>
      <div class="review-picker">
        <div class="review-picker-header">
          <h3>Send For Review</h3>
          <div style="margin-top:4px; display:flex; align-items:center; gap:6px;">
            <span class="badge badge--warning">${pending.kind}</span>
            <span class="mono" style="font-size:var(--wb-text-sm);" title="${escapeHtml(pending.ref)}">${escapeHtml(pending.ref)}</span>
          </div>
          <div style="margin-top:4px;">
            <span class="badge badge--advisory">advisory-only posture</span>
          </div>
        </div>
        <div class="review-picker-list">
          ${REVIEW_TARGETS.map(t => `
            <div class="review-picker-target" data-target="${t.id}">
              <div class="review-picker-target-name">${t.name}</div>
              <div class="review-picker-target-desc">${t.description}</div>
              <div style="font-size: var(--wb-text-xs); color: var(--wb-text-muted); margin-top:2px;">
                Status: ${t.status} — ${t.reason}
              </div>
            </div>
          `).join('')}
        </div>
      </div>
    `;

    overlayContainer.querySelector('#review-picker-backdrop')?.addEventListener('click', () => {
      state.set('pendingReviewOrigin', null);
    });

    overlayContainer.querySelectorAll('.review-picker-target').forEach(el => {
      el.addEventListener('click', () => {
        const targetId = el.dataset.target;
        createReviewRequest(pending.kind, pending.ref, targetId, 'full');
        state.set('pendingReviewOrigin', null);
        state.set('activeContextTab', 'review');
        state.set('contextVisible', true);
      });
    });
  }

  state.subscribe('pendingReviewOrigin', render);
  render();
}

function escapeHtml(text) {
  return (text || '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

function formatTime(iso) {
  if (!iso) return '';
  const d = new Date(iso);
  return d.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', second: '2-digit' });
}
