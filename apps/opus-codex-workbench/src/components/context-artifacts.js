/**
 * Context Artifacts — Tabbed docked artifact region
 * Contains: Files, Diff, Terminal, Git, Review, Workflow
 */

import * as state from '../state.js';
import { renderFileViewer } from './file-viewer.js';
import { renderTerminalSurface } from './terminal-surface.js';
import { renderDiffSurface } from './diff-surface.js';
import { renderGitStatus } from './git-status.js';
import { renderReviewRouting } from './review-routing.js';
import { renderWorkflowDock } from './workflow-dock.js';

const TABS = [
  { id: 'files',    label: '📁 Files' },
  { id: 'diff',     label: '± Diff' },
  { id: 'terminal', label: '⬛ Terminal' },
  { id: 'git',      label: '🔀 Git' },
  { id: 'review',   label: '📋 Review' },
  { id: 'workflow', label: '⚡ Workflow' },
];

export function renderContextArtifacts(container) {
  container.innerHTML = `
    <div class="context-tabs" id="context-tabs">
      ${TABS.map(t => `
        <button class="context-tab" data-tab="${t.id}" id="ctx-tab-${t.id}">${t.label}</button>
      `).join('')}
    </div>
    <div class="context-tab-content" id="context-tab-content"></div>
  `;

  const tabBar = container.querySelector('#context-tabs');
  const content = container.querySelector('#context-tab-content');

  tabBar.querySelectorAll('.context-tab').forEach(tab => {
    tab.addEventListener('click', () => {
      state.set('activeContextTab', tab.dataset.tab);
    });
  });

  function renderActiveTab() {
    const activeTab = state.get('activeContextTab');

    tabBar.querySelectorAll('.context-tab').forEach(tab => {
      tab.classList.toggle('context-tab--active', tab.dataset.tab === activeTab);
    });

    content.innerHTML = '';

    switch (activeTab) {
      case 'files':    renderFileViewer(content); break;
      case 'diff':     renderDiffSurface(content); break;
      case 'terminal': renderTerminalSurface(content); break;
      case 'git':      renderGitStatus(content); break;
      case 'review':   renderReviewRouting(content); break;
      case 'workflow': renderWorkflowDock(content); break;
    }
  }

  state.subscribe('activeContextTab', renderActiveTab);
  renderActiveTab();
}
