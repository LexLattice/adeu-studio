import { spawn } from 'child_process';
import path from 'path';

// Duplicate environment but scrub ELECTRON_RUN_AS_NODE
const childEnv = { ...process.env };
delete childEnv.ELECTRON_RUN_AS_NODE;

const electronPath = path.resolve('./node_modules/.bin/electron');

console.log('[Launch] Starting Electron without ELECTRON_RUN_AS_NODE...');
const child = spawn(electronPath, ['.'], {
  env: childEnv,
  stdio: 'inherit',
  shell: process.platform === 'win32'
});

child.on('exit', (code) => {
  process.exit(code || 0);
});
