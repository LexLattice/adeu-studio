# V54-D Semantic IR Bridge (Implementation Stage 007)

Status: Boundary-authoritative semantic IR bridge locked for workspace seam
widening only in advisory reconstruction surfaces.

Allowed scope for this stage:
- `HistoryWorkspaceQuestion`
- `HistoryWorkspaceThemeFrame`
- `HistoryWorkspaceSnapshot`

Semantic IR bridge summary:
- source authority remains `HistorySourceArtifact` as the only authority root.
- reconstruction packets remain advisory overlays over released `HistorySlice` and
  `HistoryThemeAnchor` artifacts.
- each workspace frame is derived as a deterministic projection of one theme anchor
  over its released slices and packets.
- each workspace snapshot is derived from released slice ordering plus heuristic
  inferential ordering for packet-present richness.

Canonical identity bridge points:
- `compute_history_workspace_question_id` is now required by emitted frame
  questions.
- `compute_history_workspace_frame_id` is now required by emitted theme frames.
- `compute_history_workspace_snapshot_id` is now required by the snapshot record.

Deferred/non-goal in this stage:
- no changes to source authority posture, corpus waves, API/Runtime/Runtime UI.
- no authority-posture promotion for workspace synthesis (must remain advisory
  reconstruction-only).
- no non-goals from V54-D carry-forward docs.
