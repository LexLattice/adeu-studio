import { contextBridge, ipcRenderer } from "electron";

import type { CopilotStreamEnvelope, HostBridge, ToolCallRequestArgs } from "./shared/types";

const bridge: HostBridge = {
  getHostState: () => ipcRenderer.invoke("host:get-state"),
  updateHostState: (partial) => ipcRenderer.invoke("host:update-state", partial),
  chooseWorkspaceRoot: () => ipcRenderer.invoke("workspace:choose-root"),
  listDirectory: (relativePath) => ipcRenderer.invoke("workspace:list-directory", relativePath),
  readWorkspaceFile: (relativePath) => ipcRenderer.invoke("workspace:read-file", relativePath),
  getGitSnapshot: () => ipcRenderer.invoke("git:get-snapshot"),
  getFileDiff: (relativePath) => ipcRenderer.invoke("git:get-diff", relativePath ?? null),
  runTerminalPreset: (commandId) => ipcRenderer.invoke("terminal:run-preset", commandId),
  startSession: () => ipcRenderer.invoke("adeu:start-session"),
  stopSession: (sessionId) => ipcRenderer.invoke("adeu:stop-session", sessionId),
  sendMessage: (sessionId, text) => ipcRenderer.invoke("adeu:send-message", { sessionId, text }),
  setWrites: (sessionId, writesAllowed) =>
    ipcRenderer.invoke("adeu:set-writes", { sessionId, writesAllowed }),
  callTool: (args: ToolCallRequestArgs) => ipcRenderer.invoke("adeu:call-tool", args),
  listPolicyProfiles: () => ipcRenderer.invoke("adeu:list-policy-profiles"),
  getCurrentPolicyProfile: (sessionId) =>
    ipcRenderer.invoke("adeu:get-current-policy-profile", sessionId),
  selectPolicyProfile: (sessionId, profileId) =>
    ipcRenderer.invoke("adeu:select-policy-profile", { sessionId, profileId }),
  startCopilotStream: (sessionId) => ipcRenderer.invoke("adeu:start-stream", sessionId),
  stopCopilotStream: (sessionId) => ipcRenderer.invoke("adeu:stop-stream", sessionId),
  onCopilotEvent: (listener: (event: CopilotStreamEnvelope) => void) => {
    const wrapped = (_event: Electron.IpcRendererEvent, envelope: CopilotStreamEnvelope) => {
      listener(envelope);
    };
    ipcRenderer.on("adeu:copilot-event", wrapped);
    return () => {
      ipcRenderer.off("adeu:copilot-event", wrapped);
    };
  },
};

contextBridge.exposeInMainWorld("opusWorkbench", bridge);
