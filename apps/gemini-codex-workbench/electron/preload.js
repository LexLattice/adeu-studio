import { contextBridge, ipcRenderer } from 'electron';

contextBridge.exposeInMainWorld('electronAPI', {
  readDir: (p) => ipcRenderer.invoke('read-dir', p),
  readFile: (p) => ipcRenderer.invoke('read-file', p),
  gitStatus: () => ipcRenderer.invoke('git-status'),
  gitDiff: () => ipcRenderer.invoke('git-diff'),
  spawnPty: () => ipcRenderer.invoke('spawn-pty'),
  onTerminalData: (callback) => {
    const listener = (_event, data) => callback(data);
    ipcRenderer.on('terminal.incData', listener);
    return () => ipcRenderer.removeListener('terminal.incData', listener);
  },
  sendTerminalData: (data) => ipcRenderer.send('terminal.toTerm', data),
  resizeTerminal: (cols, rows) => ipcRenderer.send('terminal.resize', cols, rows)
});
