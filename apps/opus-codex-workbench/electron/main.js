/**
 * ADEU Codex Desktop Workbench — Electron Main Process
 *
 * Host-owned capabilities:
 * - Bounded filesystem reads (contained to workspace root)
 * - Git status/diff via child process
 * - PTY-backed terminal (bounded, with explicit trust posture)
 * - Workspace root identity
 *
 * NOT provided (requires real ADEU backend):
 * - Codex session management
 * - ADEU workflow execution
 * - Review dispatch to external targets
 * - Evidence bundle retrieval
 * - Provider/build/config identity
 */

import { app, BrowserWindow, ipcMain } from 'electron';
import path from 'path';
import { fileURLToPath } from 'url';
import fs from 'fs';
import { exec } from 'child_process';
import util from 'util';

const execAsync = util.promisify(exec);

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// Workspace root: the repo root (two levels up from electron/)
// electron/ → opus-codex-workbench/ → odeu/ (repo root)
const WORKSPACE_ROOT = path.resolve(__dirname, '../..');

let mainWindow;

function createWindow() {
  mainWindow = new BrowserWindow({
    width: 1280,
    height: 860,
    minWidth: 800,
    minHeight: 600,
    title: 'ADEU Codex Desktop Workbench',
    backgroundColor: '#0b0e14',
    webPreferences: {
      preload: path.join(__dirname, 'preload.js'),
      nodeIntegration: false,
      contextIsolation: true,
      sandbox: false,
    },
  });

  const isDev = process.env.NODE_ENV !== 'production';

  if (isDev) {
    const devPort = process.env.VITE_DEV_PORT || '5174';
    mainWindow.loadURL(`http://localhost:${devPort}`).catch(() => {
      // Fallback to built files if dev server isn't running
      mainWindow.loadFile(path.join(__dirname, '../dist/index.html'));
    });
  } else {
    mainWindow.loadFile(path.join(__dirname, '../dist/index.html'));
  }

  mainWindow.on('closed', () => {
    mainWindow = null;
  });
}

app.whenReady().then(() => {
  createWindow();

  app.on('activate', () => {
    if (BrowserWindow.getAllWindows().length === 0) {
      createWindow();
    }
  });
});

app.on('window-all-closed', () => {
  if (process.platform !== 'darwin') {
    app.quit();
  }
});

// ── Path Containment ────────────────────────────────────────

/**
 * Check that a resolved path is within the workspace root.
 * Prevents directory traversal attacks.
 */
function isContainedPath(targetPath) {
  const resolved = path.resolve(WORKSPACE_ROOT, targetPath);
  return resolved === WORKSPACE_ROOT || resolved.startsWith(WORKSPACE_ROOT + path.sep);
}

function resolveContained(relativePath) {
  const resolved = path.resolve(WORKSPACE_ROOT, relativePath);
  if (!isContainedPath(resolved)) {
    throw new Error('Path traversal blocked: ' + relativePath);
  }
  return resolved;
}

// ── IPC: Workspace Identity ─────────────────────────────────

ipcMain.handle('workspace:root', () => {
  return WORKSPACE_ROOT;
});

// ── IPC: Filesystem (bounded, read-only) ────────────────────

ipcMain.handle('fs:readDir', async (_event, dirPath = '') => {
  const target = resolveContained(dirPath);
  try {
    const entries = await fs.promises.readdir(target, { withFileTypes: true });
    return entries
      .filter(e => !e.name.startsWith('.') || e.name === '.agents')
      .map(e => ({
        name: e.name,
        isDirectory: e.isDirectory(),
        path: path.relative(WORKSPACE_ROOT, path.join(target, e.name)),
      }))
      .sort((a, b) => {
        if (a.isDirectory !== b.isDirectory) return a.isDirectory ? -1 : 1;
        return a.name.localeCompare(b.name);
      });
  } catch (err) {
    console.error('[FS] readDir error:', target, err.message);
    return [];
  }
});

ipcMain.handle('fs:readFile', async (_event, filePath) => {
  const target = resolveContained(filePath);
  try {
    const stat = await fs.promises.stat(target);
    // Limit to 2MB to avoid loading huge binaries
    if (stat.size > 2 * 1024 * 1024) {
      return { error: 'File too large to display (> 2MB)', content: null };
    }
    const content = await fs.promises.readFile(target, 'utf8');
    return { error: null, content };
  } catch (err) {
    return { error: err.message, content: null };
  }
});

// ── IPC: Git (read-only) ────────────────────────────────────

ipcMain.handle('git:status', async () => {
  try {
    const { stdout } = await execAsync('git status --porcelain', {
      cwd: WORKSPACE_ROOT,
      timeout: 10000,
    });
    return { error: null, output: stdout };
  } catch (err) {
    return { error: err.message, output: null };
  }
});

ipcMain.handle('git:branch', async () => {
  try {
    const { stdout } = await execAsync('git branch --show-current', {
      cwd: WORKSPACE_ROOT,
      timeout: 5000,
    });
    return { error: null, branch: stdout.trim() };
  } catch (err) {
    return { error: err.message, branch: null };
  }
});

ipcMain.handle('git:diff', async () => {
  try {
    const { stdout } = await execAsync('git diff', {
      cwd: WORKSPACE_ROOT,
      timeout: 15000,
    });
    return { error: null, output: stdout };
  } catch (err) {
    return { error: err.message, output: null };
  }
});

ipcMain.handle('git:log', async (_event, count = 10) => {
  try {
    const n = Math.min(Math.max(1, count), 50);
    const { stdout } = await execAsync(
      `git log -n ${n} --format='%H||%h||%s||%an||%ar'`,
      { cwd: WORKSPACE_ROOT, timeout: 10000 }
    );
    const entries = stdout.trim().split('\n').filter(Boolean).map(line => {
      const [hash, short, message, author, date] = line.split('||');
      return { hash, short, message, author, date };
    });
    return { error: null, entries };
  } catch (err) {
    return { error: err.message, entries: [] };
  }
});

// ── IPC: Terminal (bounded, with trust posture) ─────────────

let ptyProcess = null;
let ptyWriteEnabled = false;

ipcMain.handle('terminal:spawn', async (_event, interactive = false) => {
  // Lazy-import node-pty only when needed
  let pty;
  try {
    pty = await import('node-pty');
  } catch {
    return { error: 'node-pty not available. Terminal requires native module compilation.', spawned: false };
  }

  if (ptyProcess) {
    try { ptyProcess.kill(); } catch { /* ignore */ }
  }

  const shell = process.platform === 'win32' ? 'powershell.exe' : 'bash';
  ptyWriteEnabled = interactive;

  try {
    ptyProcess = pty.default.spawn(shell, [], {
      name: 'xterm-color',
      cols: 80,
      rows: 24,
      cwd: WORKSPACE_ROOT,
      env: { ...process.env, TERM: 'xterm-256color' },
    });

    ptyProcess.onData((data) => {
      if (mainWindow && !mainWindow.isDestroyed()) {
        mainWindow.webContents.send('terminal:data', data);
      }
    });

    ptyProcess.onExit(() => {
      if (mainWindow && !mainWindow.isDestroyed()) {
        mainWindow.webContents.send('terminal:exit');
      }
      ptyProcess = null;
    });

    return { error: null, spawned: true, interactive };
  } catch (err) {
    return { error: err.message, spawned: false };
  }
});

ipcMain.on('terminal:write', (_event, data) => {
  if (ptyProcess && ptyWriteEnabled) {
    ptyProcess.write(data);
  }
});

ipcMain.on('terminal:resize', (_event, cols, rows) => {
  if (ptyProcess) {
    try { ptyProcess.resize(cols, rows); } catch { /* ignore */ }
  }
});

ipcMain.handle('terminal:kill', () => {
  if (ptyProcess) {
    try { ptyProcess.kill(); } catch { /* ignore */ }
    ptyProcess = null;
  }
});

ipcMain.handle('terminal:setWriteMode', (_event, enabled) => {
  ptyWriteEnabled = enabled;
  return { writeEnabled: ptyWriteEnabled };
});

// Clean up PTY on app quit
app.on('before-quit', () => {
  if (ptyProcess) {
    try { ptyProcess.kill(); } catch { /* ignore */ }
  }
});
