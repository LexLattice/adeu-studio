/**
 * Workspace Sidebar — sessions + real file tree from host bridge
 *
 * File tree is loaded from the real filesystem via Electron IPC.
 * Preserves full relative paths for provenance.
 * Falls back to empty state in browser mode.
 */

import * as state from '../state.js';
import { readDir, selectFile, peekFile } from '../host-bridge.js';

// Track expanded directories
const expandedDirs = new Set(['']);

export function renderWorkspaceSidebar(container) {
  function render() {
    const sessionId = state.get('sessionId');
    const sessionStatus = state.get('sessionStatus');
    const recentSessions = state.get('recentSessions') || [];
    const hostAvailable = state.get('hostAvailable');
    const workspaceRoot = state.get('workspaceRoot');
    const fileTree = state.get('fileTree');
    const selectedFile = state.get('selectedFile');
    const reviewRequests = state.get('reviewRequests') || [];
    const workspaceLabel = workspaceRoot ? truncatePath(workspaceRoot) : 'workspace unavailable';

    container.innerHTML = `
      <div class="sidebar-section">
        <div class="sidebar-header">
          <h3>Current Session</h3>
        </div>
        <div class="session-list">
          ${sessionId ? `
            <div class="session-item session-item--active">
              <span class="dot dot--${sessionStatus === 'active' ? 'green' : 'gray'}"></span>
              <span class="session-item-label">${sessionId}</span>
              <span class="badge badge--accent">current</span>
              <span class="session-item-time">${sessionStatus}</span>
            </div>
          ` : `
            <div class="empty-state" style="padding: 8px 0;">
              <p style="font-size: var(--wb-text-sm);">No active session. Use Start Session above.</p>
            </div>
          `}
        </div>
      </div>

      <div class="sidebar-section">
        <div class="sidebar-header">
          <h3>Recent Sessions</h3>
          <span class="badge badge--stale">${recentSessions.length}</span>
        </div>
        <div class="session-list">
          ${recentSessions.length > 0 ? recentSessions.map(s => `
            <div class="session-item">
              <span class="dot dot--${s.status === 'stopped' ? 'amber' : 'gray'}"></span>
              <span class="session-item-label" title="${escapeHtml(s.id)}">${escapeHtml(s.id)}</span>
              <span class="session-item-time">${formatRelativeTime(s.endedAt)}</span>
            </div>
          `).join('') : `
            <div class="empty-state" style="padding: 8px 0;">
              <p style="font-size: var(--wb-text-sm);">No ended sessions recorded yet.</p>
            </div>
          `}
        </div>
      </div>

      <div class="sidebar-section">
        <div class="sidebar-header">
          <h3>Workspace Switch</h3>
          <span class="badge badge--stale">bounded</span>
        </div>
        <div class="workspace-switch-row">
          <select class="select" disabled title="${escapeHtml(workspaceRoot || 'Workspace not available')}">
            <option>${escapeHtml(workspaceLabel)}</option>
          </select>
          <button class="btn btn--sm" disabled>Switch</button>
        </div>
        <div class="workspace-switch-note">
          Workspace switching is intentionally disabled. This host is bound to one workspace root.
        </div>
      </div>

      <div class="sidebar-section" style="flex:1; overflow-y:auto;">
        <div class="sidebar-header">
          <h3>Project Files</h3>
          <span class="badge badge--stale">read-only</span>
        </div>
        ${hostAvailable ? `
          <div class="file-tree" id="sidebar-file-tree">
            ${fileTree.length > 0 ? renderTreeEntries(fileTree, selectedFile, reviewRequests, sessionId) : `
              <div class="empty-state" style="padding: 12px 0;">
                <p>Loading file tree…</p>
              </div>
            `}
          </div>
        ` : `
          <div class="empty-state" style="padding: 16px 0;">
            <div class="empty-state-icon">📁</div>
            <p>File tree requires Electron host bridge.</p>
            <p style="color: var(--wb-text-muted);">Run with <code class="mono">npm run electron:dev</code></p>
          </div>
        `}
      </div>
    `;

    wireTreeEvents(container);
  }

  state.subscribeMany([
    'sessionId', 'sessionStatus', 'recentSessions',
    'hostAvailable', 'workspaceRoot',
    'fileTree', 'selectedFile', 'reviewRequests',
  ], render);
  render();
}

function renderTreeEntries(entries, selectedFile, reviewRequests, currentSessionId) {
  return entries.map(entry => {
    const fullPath = entry.path; // Already a full relative path from host bridge
    const isDir = entry.isDirectory;
    const isSelected = selectedFile === fullPath;
    const isExpanded = expandedDirs.has(fullPath);
    const depth = fullPath.split('/').length - 1;
    const icon = isDir ? (isExpanded ? '📂' : '📁') : getFileIcon(entry.name);
    const fileReviews = isDir
      ? []
      : reviewRequests.filter(r => r.originKind === 'file' && r.originRef === fullPath);
    const hasCurrentSessionReview = !isDir && fileReviews.some(r => r.sessionId === currentSessionId);

    let html = `
      <div class="tree-item ${isDir ? 'tree-item--dir' : ''} ${isSelected ? 'tree-item--selected' : ''}"
           style="--tree-depth: ${depth}"
           data-path="${escapeHtml(fullPath)}" data-name="${escapeHtml(entry.name)}" data-type="${isDir ? 'dir' : 'file'}">
        <span class="tree-icon">${icon}</span>
        <span class="tree-name">${entry.name}</span>
        ${!isDir && fileReviews.length > 0 ? `
          <span class="tree-session-marker ${hasCurrentSessionReview ? 'tree-session-marker--current' : ''}"
            title="${hasCurrentSessionReview ? 'Current session has review requests on this file' : 'Prior session review requests on this file'}">
            R${fileReviews.length}
          </span>
        ` : ''}
        <div class="tree-context-actions">
          ${!isDir ? `
            <button class="btn btn--sm message-action-btn--review" data-action="review" data-path="${escapeHtml(fullPath)}" title="Send file for review">📋</button>
            <button class="btn btn--sm" data-action="peek" data-path="${escapeHtml(fullPath)}" title="Quick peek">👁</button>
            <button class="btn btn--sm" data-action="open" data-path="${escapeHtml(fullPath)}" title="Open in context">↗</button>
          ` : ''}
        </div>
      </div>
    `;

    // Render children if expanded
    if (isDir && isExpanded && entry.children) {
      html += renderTreeEntries(entry.children, selectedFile, reviewRequests, currentSessionId);
    }

    return html;
  }).join('');
}

function getFileIcon(name) {
  if (name.endsWith('.md')) return '📄';
  if (name.endsWith('.ts') || name.endsWith('.tsx')) return '🔷';
  if (name.endsWith('.js') || name.endsWith('.jsx')) return '🟡';
  if (name.endsWith('.css')) return '🎨';
  if (name.endsWith('.json')) return '📋';
  if (name.endsWith('.toml') || name.endsWith('.yaml') || name.endsWith('.yml')) return '⚙';
  if (name.endsWith('.py')) return '🐍';
  if (name === 'Makefile') return '🔧';
  return '📄';
}

function wireTreeEvents(container) {
  container.querySelectorAll('.tree-item').forEach(item => {
    item.addEventListener('click', async (e) => {
      if (e.target.closest('.tree-context-actions')) return;
      const path = item.dataset.path;
      const type = item.dataset.type;

      if (type === 'dir') {
        // Toggle directory expansion and load children
        if (expandedDirs.has(path)) {
          expandedDirs.delete(path);
        } else {
          expandedDirs.add(path);
          // Load children from real filesystem
          const children = await readDir(path);
          // Update the entry in the file tree with children
          updateTreeChildren(state.get('fileTree'), path, children);
          state.set('fileTree', [...state.get('fileTree')]); // trigger re-render
        }
        // Re-render
        state.set('fileTree', [...state.get('fileTree')]);
      } else {
        selectFile(path);
      }
    });
  });

  container.querySelectorAll('[data-action="peek"]').forEach(btn => {
    btn.addEventListener('click', (e) => {
      e.stopPropagation();
      peekFile(btn.dataset.path);
    });
  });

  container.querySelectorAll('[data-action="open"]').forEach(btn => {
    btn.addEventListener('click', (e) => {
      e.stopPropagation();
      selectFile(btn.dataset.path);
      state.set('activeContextTab', 'files');
      state.set('contextVisible', true);
    });
  });

  container.querySelectorAll('[data-action="review"]').forEach(btn => {
    btn.addEventListener('click', (e) => {
      e.stopPropagation();
      state.set('pendingReviewOrigin', {
        kind: 'file',
        ref: btn.dataset.path,
      });
    });
  });
}

/**
 * Recursively update children for a directory node in the file tree.
 */
function updateTreeChildren(tree, targetPath, children) {
  for (const entry of tree) {
    if (entry.path === targetPath && entry.isDirectory) {
      entry.children = children;
      return true;
    }
    if (entry.children) {
      if (updateTreeChildren(entry.children, targetPath, children)) return true;
    }
  }
  return false;
}

function formatRelativeTime(iso) {
  if (!iso) return '';
  const deltaMs = Date.now() - new Date(iso).getTime();
  if (!Number.isFinite(deltaMs) || deltaMs < 0) return 'now';
  const minutes = Math.floor(deltaMs / 60000);
  if (minutes < 1) return 'now';
  if (minutes < 60) return `${minutes}m`;
  const hours = Math.floor(minutes / 60);
  if (hours < 24) return `${hours}h`;
  const days = Math.floor(hours / 24);
  return `${days}d`;
}

function truncatePath(pathValue) {
  if (!pathValue) return '';
  const parts = pathValue.split('/').filter(Boolean);
  if (parts.length <= 3) return pathValue;
  return `…/${parts.slice(-3).join('/')}`;
}

function escapeHtml(text) {
  return (text || '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}
