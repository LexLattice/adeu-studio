/**
 * Workflow Dock — bounded workflow dispatch surface
 *
 * Creates local workflow request tokens. Does NOT execute against a real backend.
 * Each request shows:
 *   - template identity
 *   - prompt/input
 *   - request id (local token)
 *   - status: not_executed (no real ADEU backend)
 *   - reason for unavailability
 *   - evidenceId: null (no real evidence produced)
 */

import * as state from '../state.js';
import { createWorkflowRequest, WORKFLOW_TEMPLATES } from '../host-bridge.js';

export function renderWorkflowDock(container) {
  function render() {
    const requests = state.get('workflowRequests');
    const adeuStatus = state.get('adeuBackendStatus');

    container.innerHTML = `
      <div class="workflow-surface">
        <div class="surface-header">
          <h3>⚡ Workflow Dock</h3>
          <span class="badge badge--${adeuStatus === 'connected' ? 'success' : 'stale'}">${adeuStatus}</span>
        </div>

        <!-- Launcher -->
        <div class="workflow-launcher">
          <h4>Create Workflow Request</h4>

          <div class="workflow-field">
            <label class="workflow-field-label">Template</label>
            <select class="select" id="wf-template-select">
              ${WORKFLOW_TEMPLATES.map(t => `
                <option value="${t.id}">${t.id} (${t.status})</option>
              `).join('')}
            </select>
          </div>

          <div style="font-size: var(--wb-text-xs); color: var(--wb-text-muted); padding: 2px 0;">
            ${WORKFLOW_TEMPLATES[0]?.description || ''}
          </div>

          <div class="workflow-field">
            <label class="workflow-field-label">Prompt / Input</label>
            <textarea class="input" id="wf-input" rows="3"
              placeholder="Describe the task for this workflow..."
              style="resize:vertical; min-height:60px;"></textarea>
          </div>

          <div style="display:flex; gap:8px; align-items:center; flex-wrap:wrap;">
            <button class="btn btn--handoff" id="wf-launch">
              ⚡ Create Request
            </button>
            <span class="badge badge--warning" style="font-size:10px;">handoff boundary</span>
            ${adeuStatus !== 'connected' ? `
              <span class="badge badge--stale" style="font-size:10px;">backend unavailable — request will be local only</span>
            ` : ''}
          </div>
        </div>

        <!-- Templates info -->
        <div>
          <div class="label" style="margin-bottom: 8px;">Available Templates (${WORKFLOW_TEMPLATES.length})</div>
          <div style="display:flex; flex-direction:column; gap:4px;">
            ${WORKFLOW_TEMPLATES.map(t => `
              <div style="display:flex; justify-content:space-between; align-items:center; padding:4px 8px; background:var(--wb-bg-surface); border-radius:var(--wb-radius-sm); font-size:var(--wb-text-sm);">
                <span class="mono">${t.id}</span>
                <span class="badge badge--stale">${t.status}</span>
              </div>
            `).join('')}
          </div>
        </div>

        <!-- Request History -->
        <div>
          <div class="label" style="margin-bottom: 8px;">Request History (${requests.length})</div>
          ${requests.length > 0 ? `
            <div style="display:flex; flex-direction:column; gap:8px;">
              ${requests.map(req => `
                <div class="workflow-run">
                  <div class="workflow-run-header">
                    <span class="workflow-run-template">${escapeHtml(req.templateId)}</span>
                    <span class="badge badge--warning">${req.status}</span>
                  </div>
                  <div class="review-field">
                    <span class="review-field-label">Request ID</span>
                    <span class="review-field-value">${escapeHtml(req.id)}</span>
                  </div>
                  <div class="review-field">
                    <span class="review-field-label">Prompt</span>
                    <span class="review-field-value" style="word-break:break-word;">${escapeHtml(req.prompt)}</span>
                  </div>
                  <div class="review-field">
                    <span class="review-field-label">Evidence</span>
                    <span class="review-field-value">${req.evidenceId ? escapeHtml(req.evidenceId) : 'none (not executed)'}</span>
                  </div>
                  <div class="review-field">
                    <span class="review-field-label">Created</span>
                    <span class="review-field-value">${formatTime(req.createdAt)}</span>
                  </div>
                  <div style="margin-top:4px; padding:6px 8px; background:var(--wb-stale-bg); border-radius:var(--wb-radius-sm); font-size:var(--wb-text-xs); color:var(--wb-text-muted);">
                    ${escapeHtml(req.statusReason)}
                  </div>
                </div>
              `).join('')}
            </div>
          ` : `
            <div class="empty-state" style="padding: 16px 0;">
              <p>No workflow requests yet.</p>
            </div>
          `}
        </div>
      </div>
    `;

    // Wire template select description update
    const select = container.querySelector('#wf-template-select');
    if (select) {
      select.addEventListener('change', () => {
        const t = WORKFLOW_TEMPLATES.find(t => t.id === select.value);
        const desc = container.querySelector('.workflow-field + div');
        if (desc && t) desc.textContent = t.description;
      });
    }

    // Wire launch
    container.querySelector('#wf-launch')?.addEventListener('click', () => {
      const templateId = container.querySelector('#wf-template-select')?.value;
      const prompt = container.querySelector('#wf-input')?.value?.trim();
      if (templateId && prompt) {
        createWorkflowRequest(templateId, prompt);
        const input = container.querySelector('#wf-input');
        if (input) input.value = '';
      }
    });
  }

  state.subscribeMany(['workflowRequests', 'adeuBackendStatus'], render);
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
