# ADEU Codex Workbench

This is a local bounded desktop UI for the ADEU Codex architecture. It operates primarily as a frontend host mapping real OS layers (File System, `node-pty` Terminals, Git Exec) directly onto standard GUI artifacts governed by explicit Morphic UX boundary paths. 

## Running The Workbench

This app utilizes `electron` to spawn local PTY nodes and file connections securely. 
**Do Not Run Directly with node**. The launcher script safely zeroes out internal environment flags that typically crash node instances acting as standard OS packages inside `.venv`.

```sh
cd apps/gemini-codex-workbench
npm install
npm run electron:dev
```

## Current Limitations
- **ADEU App Server Backend (`get_app_state`) Unavailable**: The UI operates currently decoupled from the actual Codex internal Python runtime intent loops. 
- You will see UI markers explicitely noting `Unconfigured` statuses, along with "Blocked Request" transcript stubs confirming requests have stopped securely before breaking internal state logic boundaries.
- **PTY Terminals Default to Safe-Readonly**: You physically cannot execute keystrokes within the context shell until clicking `Enable Writes` to actively declare explicit intent to step out of advisory bounds.
