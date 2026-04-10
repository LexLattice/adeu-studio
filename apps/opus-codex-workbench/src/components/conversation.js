/**
 * Conversation Region — Transcript + Composer
 *
 * Chat messages are recorded locally. No assistant responses are fabricated.
 * If no ADEU backend is connected, messages are logged with explicit
 * system notices about unavailability.
 *
 * Origin-attached review markers: when a review request is created from a
 * message, the transcript shows the request id and status on that message.
 */

import * as state from '../state.js';
import { sendMessage, getReviewRequestsForOrigin } from '../host-bridge.js';

export function renderConversation(container) {
  container.innerHTML = `
    <div class="conversation-container">
      <div class="transcript" id="transcript"></div>
      <div class="composer">
        <div class="composer-input-row">
          <textarea class="composer-textarea" id="composer-input"
            placeholder="Send a message…"
            rows="1"></textarea>
          <button class="composer-send" id="composer-send" disabled>Send</button>
        </div>
        <div class="composer-toolbar" id="composer-toolbar">
          <button class="composer-toggle" data-toggle="files" title="File tree">📁 Files</button>
          <button class="composer-toggle" data-toggle="diff" title="Diff view">± Diff</button>
          <button class="composer-toggle" data-toggle="terminal" title="Terminal">⬛ Term</button>
          <button class="composer-toggle" data-toggle="git" title="Git status">🔀 Git</button>
          <button class="composer-toggle" data-toggle="workflow" title="Workflows">⚡ Workflow</button>
          <button class="composer-toggle" data-toggle="review" title="Reviews">📋 Review</button>
        </div>
      </div>
    </div>
  `;

  const transcript = container.querySelector('#transcript');
  const input = container.querySelector('#composer-input');
  const sendBtn = container.querySelector('#composer-send');

  // Auto-resize textarea
  input.addEventListener('input', () => {
    input.style.height = 'auto';
    input.style.height = Math.min(input.scrollHeight, 160) + 'px';
    updateSendState();
  });

  // Send on Enter (without Shift)
  input.addEventListener('keydown', (e) => {
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault();
      if (canSend()) handleSend();
    }
  });

  sendBtn.addEventListener('click', handleSend);

  function canSend() {
    return input.value.trim() && state.get('sessionStatus') === 'active';
  }

  function updateSendState() {
    sendBtn.disabled = !canSend();
  }

  function handleSend() {
    const text = input.value.trim();
    if (!text) return;
    input.value = '';
    input.style.height = 'auto';
    sendBtn.disabled = true;
    sendMessage(text);
  }

  // Render transcript
  function renderMessages() {
    const messages = state.get('messages');

    transcript.innerHTML = messages.map(msg => {
      // Find any review requests that originated from this message
      const attachedReviews = msg.role === 'user'
        ? getReviewRequestsForOrigin('reply', msg.id)
        : [];

      return `
        <div class="message message--${msg.role}" data-message-id="${msg.id}">
          <div class="message-header">
            <span class="message-role">${msg.role}</span>
            <span class="message-time">${formatTime(msg.time)}</span>
            ${msg.role === 'user' ? `
              <div class="message-actions">
                <button class="message-action-btn" data-action="copy" data-id="${msg.id}">Copy</button>
                <button class="message-action-btn message-action-btn--review" data-action="review" data-id="${msg.id}">Send For Review</button>
              </div>
            ` : ''}
          </div>
          <div class="message-body">${formatMessageText(msg.text)}</div>
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
        </div>
      `;
    }).join('');

    // Scroll to bottom
    transcript.scrollTop = transcript.scrollHeight;
    updateSendState();
    wireMessageActions();
  }

  function wireMessageActions() {
    transcript.querySelectorAll('[data-action="copy"]').forEach(btn => {
      btn.addEventListener('click', () => {
        const msg = state.get('messages').find(m => m.id === btn.dataset.id);
        if (msg) navigator.clipboard?.writeText(msg.text);
      });
    });

    transcript.querySelectorAll('[data-action="review"]').forEach(btn => {
      btn.addEventListener('click', () => {
        state.set('pendingReviewOrigin', {
          kind: 'reply',
          ref: btn.dataset.id,
        });
      });
    });

    // Wire "goto review dock" buttons on attached pills
    transcript.querySelectorAll('[data-goto-review]').forEach(btn => {
      btn.addEventListener('click', (e) => {
        e.stopPropagation();
        state.set('activeContextTab', 'review');
        state.set('contextVisible', true);
      });
    });
  }

  // Artifact toggle buttons
  container.querySelectorAll('.composer-toggle').forEach(btn => {
    btn.addEventListener('click', () => {
      const tab = btn.dataset.toggle;
      state.set('activeContextTab', tab);
      state.set('contextVisible', true);
      updateToggles();
    });
  });

  function updateToggles() {
    const active = state.get('activeContextTab');
    const visible = state.get('contextVisible');
    container.querySelectorAll('.composer-toggle').forEach(b => {
      b.classList.toggle('composer-toggle--active', b.dataset.toggle === active && visible);
    });
  }

  state.subscribe('messages', renderMessages);
  state.subscribe('reviewRequests', renderMessages); // re-render when reviews change
  state.subscribe('sessionStatus', updateSendState);
  state.subscribe('activeContextTab', updateToggles);
  state.subscribe('contextVisible', updateToggles);
  renderMessages();
}

function formatTime(iso) {
  if (!iso) return '';
  const d = new Date(iso);
  return d.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
}

function formatMessageText(text) {
  return text
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/`([^`]+)`/g, '<code class="mono" style="background:var(--wb-bg-surface-alt);padding:1px 4px;border-radius:3px;">$1</code>')
    .replace(/\n/g, '<br>');
}
