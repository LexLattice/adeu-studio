/**
 * ADEU Codex Desktop Workbench — Main Entry Point
 *
 * Bootstraps the application:
 * 1. Detect host bridge (Electron vs browser fallback)
 * 2. Initialize host bridge and load real workspace state
 * 3. Render all regions with truthful state
 * 4. Wire keyboard shortcuts
 */

import * as state from './state.js';
import { initHostBridge, loadFileTree, loadGitState } from './host-bridge.js';

import { renderStatusBoundary } from './components/status-boundary.js';
import { renderWorkspaceSidebar } from './components/workspace-sidebar.js';
import { renderConversation } from './components/conversation.js';
import { renderContextArtifacts } from './components/context-artifacts.js';
import { renderTrustBoundary } from './components/trust-boundary.js';
import { renderPeekOverlay } from './components/file-viewer.js';
import { renderReviewPicker } from './components/review-routing.js';

// ── Initialize ──────────────────────────────────────────────

async function init() {
  const statusRegion = document.getElementById('status-boundary-region');
  const sidebarRegion = document.getElementById('workspace-region');
  const conversationRegion = document.getElementById('conversation-region');
  const contextRegion = document.getElementById('context-region');
  const trustRegion = document.getElementById('trust-boundary-region');
  const overlayRegion = document.getElementById('overlay-region');

  // Initialize host bridge — detects Electron or browser mode
  await initHostBridge();

  // Render all regions
  renderStatusBoundary(statusRegion);
  renderWorkspaceSidebar(sidebarRegion);
  renderConversation(conversationRegion);
  renderContextArtifacts(contextRegion);
  renderTrustBoundary(trustRegion);

  // Overlay containers
  const peekContainer = document.createElement('div');
  peekContainer.id = 'peek-container';
  const reviewContainer = document.createElement('div');
  reviewContainer.id = 'review-container';
  overlayRegion.innerHTML = '';
  overlayRegion.appendChild(peekContainer);
  overlayRegion.appendChild(reviewContainer);
  renderPeekOverlay(peekContainer);
  renderReviewPicker(reviewContainer);

  // Context pane visibility
  state.subscribe('contextVisible', (visible) => {
    contextRegion.classList.toggle('context--visible', visible);
  });

  // ── Load real workspace state ────────────────────────────

  if (state.get('hostAvailable')) {
    // Load real file tree and git state from the host
    await Promise.all([
      loadFileTree(),
      loadGitState(),
    ]);
    state.addMessage('system',
      `Workspace loaded: ${state.get('workspaceRoot')}`
    );
  }

  // ── Keyboard shortcuts ───────────────────────────────────

  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape') {
      if (state.get('peekFile')) {
        state.set('peekFile', null);
        return;
      }
      if (state.get('pendingReviewOrigin')) {
        state.set('pendingReviewOrigin', null);
        return;
      }
      if (state.get('contextVisible')) {
        state.set('contextVisible', false);
        return;
      }
    }

    // Ctrl+` toggles terminal
    if (e.key === '`' && (e.ctrlKey || e.metaKey)) {
      e.preventDefault();
      state.set('activeContextTab', 'terminal');
      state.set('contextVisible', !state.get('contextVisible'));
    }

    // Ctrl+Shift+E toggles files
    if (e.key === 'E' && (e.ctrlKey || e.metaKey) && e.shiftKey) {
      e.preventDefault();
      state.set('activeContextTab', 'files');
      state.set('contextVisible', !state.get('contextVisible'));
    }
  });

  // ── Responsive context visibility ─────────────────────────

  function handleResize() {
    if (window.innerWidth >= 1280) {
      contextRegion.classList.remove('context--visible');
    }
  }
  window.addEventListener('resize', handleResize);

  console.log('[ADEU Workbench] Initialized.');
}

// Boot
if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', init);
} else {
  init();
}
