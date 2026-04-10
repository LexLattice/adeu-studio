/**
 * File Tree — standalone file tree component for context region
 * Delegates to workspace-sidebar's tree model but renders in context pane.
 */

import * as state from '../state.js';
import { selectFile, peekFile } from '../host-bridge.js';

export function renderFileTree(container) {
  // This component is not directly used; the context-artifacts tab
  // delegates to file-viewer.js which handles both tree selection
  // and file content display.
}
