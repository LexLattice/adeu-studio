import { app, BrowserWindow, ipcMain } from 'electron';
import path from 'path';
import { fileURLToPath } from 'url';
import fs from 'fs';
import * as pty from 'node-pty';
import os from 'os';
import { exec } from 'child_process';
import util from 'util';

const execAsync = util.promisify(exec);

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const ROOT_DIR = path.resolve(__dirname, '../../..');

let mainWindow;

function createWindow() {
  mainWindow = new BrowserWindow({
    width: 1200,
    height: 800,
    webPreferences: {
      preload: path.join(__dirname, 'preload.js'),
      nodeIntegration: false,
      contextIsolation: true,
    },
  });

  const isDev = process.env.NODE_ENV !== 'production';

  if (isDev) {
    try {
      mainWindow.loadURL('http://localhost:5173');
    } catch(e) {
      mainWindow.loadFile(path.join(__dirname, '../dist/index.html'));
    }
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

function isSafePath(targetPath) {
  const resolved = path.resolve(ROOT_DIR, targetPath);
  return resolved === ROOT_DIR || resolved.startsWith(ROOT_DIR + path.sep);
}

// IPC File System
ipcMain.handle('read-dir', async (_event, dirPath = '') => {
  const target = path.resolve(ROOT_DIR, dirPath);
  if (!isSafePath(target)) {
    console.error("Path traversal blocked:", target);
    throw new Error('Path traversal blocked');
  }

  try {
    const entries = await fs.promises.readdir(target, { withFileTypes: true });
    const formatted = entries.map(ent => ({ 
      name: ent.name, 
      isDirectory: ent.isDirectory(), 
      path: path.relative(ROOT_DIR, path.join(target, ent.name)) 
    }));
    return formatted.sort((a, b) => {
      if (a.isDirectory === b.isDirectory) {
        return a.name.localeCompare(b.name);
      }
      return a.isDirectory ? -1 : 1;
    });
  } catch (err) {
    console.error("Failed to read dir:", target, err);
    return [];
  }
});

ipcMain.handle('read-file', async (_event, filePath) => {
  const target = path.resolve(ROOT_DIR, filePath);
  if (!isSafePath(target)) {
    throw new Error('Path traversal blocked');
  }

  try {
    return await fs.promises.readFile(target, 'utf8');
  } catch (err) {
    if (err instanceof Error) return 'Error reading file: ' + err.message;
    return 'Unknown Error reading file';
  }
});

// IPC Git
ipcMain.handle('git-status', async () => {
  try {
    const { stdout } = await execAsync('git status', { cwd: ROOT_DIR });
    return stdout;
  } catch (err) {
    if (err instanceof Error) return 'Error checking git status: ' + err.message;
    return 'Unknown Git Error';
  }
});

ipcMain.handle('git-diff', async () => {
  try {
    const { stdout } = await execAsync('git diff', { cwd: ROOT_DIR });
    return stdout;
  } catch (err) {
    if (err instanceof Error) return 'Error executing git diff: ' + err.message;
    return 'Unknown Git Error';
  }
});

// IPC PTY
let ptyProcess;
ipcMain.handle('spawn-pty', () => {
  const shell = os.platform() === 'win32' ? 'powershell.exe' : 'bash';
  if (ptyProcess) {
    ptyProcess.kill();
  }
  
  ptyProcess = pty.spawn(shell, [], {
    name: 'xterm-color',
    cols: 80,
    rows: 30,
    cwd: ROOT_DIR,
    env: process.env
  });

  ptyProcess.onData((data) => {
    if (mainWindow) {
      mainWindow.webContents.send('terminal.incData', data);
    }
  });

  // Small delay then write initial context message to indicate bounded scope
  setTimeout(() => {
    if (ptyProcess) {
      ptyProcess.write('\x1b[36m[ADEU Codex Workbench] Bounded Session Started.\x1b[0m\r\n');
    }
  }, 100);
  
  return true;
});

ipcMain.on('terminal.toTerm', (_event, data) => {
  if (ptyProcess) {
    ptyProcess.write(data);
  }
});

ipcMain.on('terminal.resize', (_event, cols, rows) => {
  if (ptyProcess) {
    try {
      ptyProcess.resize(cols, rows);
    } catch(e) {
      console.error('resize issue', e);
    }
  }
});
