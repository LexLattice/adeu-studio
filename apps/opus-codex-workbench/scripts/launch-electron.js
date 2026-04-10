/**
 * ADEU Codex Desktop Workbench — Electron Launcher
 *
 * Guards against ELECTRON_RUN_AS_NODE=1 which is set in some repo shell
 * environments. Without this guard, Electron imports fail with:
 * "The requested module 'electron' does not provide an export named 'BrowserWindow'"
 */

import { spawn } from 'child_process';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// Scrub ELECTRON_RUN_AS_NODE from the child environment
const childEnv = { ...process.env };
delete childEnv.ELECTRON_RUN_AS_NODE;

const electronPath = path.resolve(__dirname, '../node_modules/.bin/electron');

console.log('[ADEU Workbench] Starting Electron (ELECTRON_RUN_AS_NODE scrubbed)...');

const child = spawn(electronPath, ['.'], {
  cwd: path.resolve(__dirname, '..'),
  env: childEnv,
  stdio: 'inherit',
  shell: process.platform === 'win32',
});

child.on('exit', (code) => {
  process.exit(code || 0);
});
