/**
 * ADEU Codex Desktop Workbench — Preload (Context Bridge)
 *
 * Exposes only the governed IPC surface to the renderer.
 * All host bridge capabilities are read-only or explicitly gated.
 */

const { contextBridge, ipcRenderer } = require('electron');

contextBridge.exposeInMainWorld('hostBridge', {
  // Workspace
  getWorkspaceRoot: () => ipcRenderer.invoke('workspace:root'),

  // Filesystem (read-only, bounded)
  readDir: (dirPath) => ipcRenderer.invoke('fs:readDir', dirPath),
  readFile: (filePath) => ipcRenderer.invoke('fs:readFile', filePath),

  // Git (read-only)
  gitStatus: () => ipcRenderer.invoke('git:status'),
  gitBranch: () => ipcRenderer.invoke('git:branch'),
  gitDiff: () => ipcRenderer.invoke('git:diff'),
  gitLog: (count) => ipcRenderer.invoke('git:log', count),

  // Terminal (bounded, gated)
  spawnTerminal: (interactive) => ipcRenderer.invoke('terminal:spawn', interactive),
  killTerminal: () => ipcRenderer.invoke('terminal:kill'),
  setTerminalWriteMode: (enabled) => ipcRenderer.invoke('terminal:setWriteMode', enabled),
  writeTerminal: (data) => ipcRenderer.send('terminal:write', data),
  resizeTerminal: (cols, rows) => ipcRenderer.send('terminal:resize', cols, rows),
  onTerminalData: (callback) => {
    const handler = (_event, data) => callback(data);
    ipcRenderer.on('terminal:data', handler);
    return () => ipcRenderer.removeListener('terminal:data', handler);
  },
  onTerminalExit: (callback) => {
    const handler = () => callback();
    ipcRenderer.on('terminal:exit', handler);
    return () => ipcRenderer.removeListener('terminal:exit', handler);
  },
});
