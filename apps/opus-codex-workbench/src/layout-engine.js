/**
 * ADEU Codex Desktop Workbench — Layout Engine (Support Artifact)
 *
 * Owns repeatable layout constraint math:
 * - Conversation width floor
 * - Context pane bounds
 * - Sidebar bounds
 * - Non-overlap rules
 * - Same-context reachability guarantees
 */

const CONSTRAINTS = {
  sidebar: { min: 200, max: 280, default: 240 },
  conversation: { min: 360 },
  context: { min: 300, max: 420, default: 340 },
  statusBar: { height: 36 },
  trustBar: { height: 28 },
};

/**
 * Compute region widths given viewport width.
 * @param {number} viewportWidth
 * @returns {{ sidebar: number, conversation: number, context: number, mode: 'wide' | 'medium' | 'narrow' }}
 */
export function computeLayout(viewportWidth) {
  if (viewportWidth >= 1280) {
    const sidebar = CONSTRAINTS.sidebar.default;
    const context = CONSTRAINTS.context.default;
    const conversation = viewportWidth - sidebar - context;
    return {
      sidebar,
      conversation: Math.max(conversation, CONSTRAINTS.conversation.min),
      context,
      mode: 'wide',
    };
  }

  if (viewportWidth >= 860) {
    const sidebar = CONSTRAINTS.sidebar.min;
    const conversation = viewportWidth - sidebar;
    return {
      sidebar,
      conversation: Math.max(conversation, CONSTRAINTS.conversation.min),
      context: Math.min(380, viewportWidth * 0.5),
      mode: 'medium',
    };
  }

  return {
    sidebar: viewportWidth,
    conversation: viewportWidth,
    context: viewportWidth,
    mode: 'narrow',
  };
}

/**
 * Check if context pane can be open without violating conversation width floor.
 * @param {number} viewportWidth
 * @param {number} sidebarWidth
 * @param {number} contextWidth
 * @returns {boolean}
 */
export function canShowContextPane(viewportWidth, sidebarWidth, contextWidth) {
  const remaining = viewportWidth - sidebarWidth - contextWidth;
  return remaining >= CONSTRAINTS.conversation.min;
}

/**
 * Check if peek overlay can be shown without breaking same-context reachability
 * (transcript must remain partially visible).
 * @param {number} viewportWidth
 * @param {number} overlayWidth
 * @returns {boolean}
 */
export function canShowPeekOverlay(viewportWidth, overlayWidth) {
  return viewportWidth - overlayWidth > 200;
}

export { CONSTRAINTS };
