# GPT-5.4 Codex ADEU Desktop Workbench

Standalone Electron workbench implementing the governed desktop surface described in:

- `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md`

Run stance for this implementation:

- `task_mode`: `implementation`
- `execution_mode`: `governed_enactment`
- `grounding_status`: `artifact_grounded_repo_incomplete`
- `implementation_inspection_status`: `implementation_inspected`

What this app implements:

- transcript-first desktop workbench layout
- explicit status boundary for provider, build, config intent, policy profile, writes, and reachability
- read-only workspace tree and file reader with docked and peek modes
- bounded git, diff, and read-only terminal artifacts
- explicit review dispatch artifact with advisory return posture
- ADEU workflow dock backed by the repo's existing URM/ADEU APIs
- live copilot event streaming through the repo API

What remains intentionally bounded in v0:

- no in-place file editing
- no full PTY terminal emulation
- no automatic authority transfer from review outputs
- launch profile config paths are host-declared metadata unless backed by the connected API runtime

## Run

From this folder:

```bash
npm install
npm run dev
```

The launcher clears `ELECTRON_RUN_AS_NODE` before spawning Electron. That matters in shells where Electron is forced into Node mode and `require("electron")` no longer exposes the desktop API.

For a bounded headless verification run:

```bash
npm run smoke
```

This is the GPT-5.4 Codex implementation variant.

The renderer expects the ADEU API to be reachable at `http://127.0.0.1:8000` by default.
You can change the API base inside the workbench.
