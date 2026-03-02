# Locked Continuation vNext+31 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS30.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+30` (`D1`-`D4`) is merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md`.
- Post-v30 planning baseline is `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`.
- Selected v31 thin-slice is `B31-AB`:
  - `V31-A` Evidence Explorer contract closure.
  - `V31-B` closeout consistency guard rail.
- `vNext+31` is constrained to deterministic additive hardening only:
  - no solver/runtime semantics release,
  - no policy-enforcement expansion,
  - no L2 boundary release.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS30.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v31,
  - v31 keyset must be exactly equal to v30 keyset (set equality, derived cardinality),
  - keyset authority is `stop_gate_metrics@1` payload field `metrics` object keys only.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion.
- Non-enforcement/no-mutation continuity remains frozen for evidence surfaces in this arc.
- L2 boundaries remain deferred in this arc:
  - no `/urm/worker/run` governance boundary release,
  - no proposer idempotency persistence boundary release.
- L2 scaffolding prohibition remains frozen:
  - no partial implementation of L2 authority/persistence surfaces may land under this L1/L0 arc.
- Closeout observability continuity lock is frozen:
  - v31 closeout must include a runtime-observability comparison row against v30 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `E1` Evidence Explorer template-contract closure (`V31-A`)
2. `E2` closeout consistency guard rail and baseline normalization (`V31-B`)

Out-of-scope note:

- any runtime policy-enforcement behavior changes,
- any `SEMANTICS_v4` runtime contract release,
- any L2 governance/persistence releases,
- formal-lane expansion path (`V31-C`) and repo-root consolidation path (`V31-D`),
- worker CLI safety policy path (`V31-E`),
- new stop-gate metric keys or schema-family forks.

## E1) Evidence Explorer Contract Closure (`V31-A`)

### Goal

Align web contract validation with the frozen API catalog contract so the v29 Evidence Explorer surface remains operational under deterministic fail-closed rules.

### Scope

- Keep API-side catalog contract unchanged.
- Update web-side validation/expansion logic to consume template-form `list_ref.path` deterministically.
- Add fixture-backed frontend contract tests for catalog path handling and fail-closed branches.
- Keep implementation authority for this slice on web-side explorer code and related web tests only.

### Locks

- API template-path continuity lock is frozen:
  - frontend catalog validator must require exact string equality:
    - `families[].list_ref.path == "/urm/evidence-explorer/catalog/{family}"`.
  - pre-expanded path values (for example `"/urm/evidence-explorer/catalog/read_surface"`) fail closed.
  - `families[].list_ref.path` remains template form `"/urm/evidence-explorer/catalog/{family}"`.
  - authoritative API template constant remains `_EVIDENCE_EXPLORER_LIST_REF_PATH_TEMPLATE` in `apps/api/src/adeu_api/main.py`.
- Evidence-family enum lock is frozen to exactly:
  - `read_surface`
  - `normative_advice`
  - `proof_trust`
  - `semantics_v4_candidate`
  - `extraction_fidelity`
- Family-enum source-of-truth lock is frozen:
  - authoritative source is API-side `_EVIDENCE_EXPLORER_FAMILIES`.
  - web-side family typing must remain value-identical to that frozen set.
- Family-enum contract-test lock is frozen:
  - tests must assert accepted frontend family values are exactly equal to the frozen set using set equality (order-agnostic).
  - tests must assert unknown family values fail-closed.
  - tests must assert family ordering used for deterministic UI selection/defaulting is lexicographic.
- Expansion authority boundary lock is frozen:
  - API returns template form only.
  - frontend performs expansion for request dispatch.
  - dual-contract acceptance (`{family}` plus pre-expanded forms) is forbidden in this arc.
- Template expansion rule lock is frozen:
  - accept only frozen family-enum values as expansion inputs,
  - replace exact substring `{family}` only,
  - URL-encode family token using `encodeURIComponent` before insertion,
  - fail closed if `{family}` placeholder is missing,
  - fail closed if `{family}` appears more than once,
  - fail closed if template contains any placeholder token other than exact `{family}`,
  - fail closed if expanded path does not preserve `/urm/evidence-explorer/catalog/` prefix.
- Placeholder-token parser lock is frozen:
  - placeholder detection scans brace-delimited `{...}` tokens left-to-right with non-overlapping extraction.
  - allowed token set is exactly `{family}`.
  - any other placeholder token fails closed.
- API payload contract continuity lock is frozen:
  - no API payload shape/schema changes in this slice.
- API implementation no-mutation lock is frozen:
  - API-side Evidence Explorer constants/contracts are consumed as authoritative inputs and may not be mutated in this arc.
- E1 parser-boundary lock is frozen:
  - placeholder-token parsing applies only to `families[].list_ref.path` validation.
  - generalized URI-template engine behavior is out-of-scope.
- E1 dependency-surface lock is frozen:
  - RFC 6570/general-purpose URI-template library adoption is out-of-scope for this arc.
- No-network/no-provider-expansion lock is frozen:
  - no new provider dispatch or outbound-network behavior is introduced by this slice.

### Acceptance

- Evidence Explorer family catalog validates successfully against live API payload.
- Explorer family fetches resolve via deterministic template expansion.
- Malformed template payloads fail closed with deterministic error handling.
- Expanded-path payloads fail closed (no dual-contract acceptance).
- Existing API endpoint tests remain behavior-compatible.

## E2) Closeout Consistency Guard Rail (`V31-B`)

### Goal

Prevent closeout-doc drift between claimed continuity assertions and committed artifact evidence.

### Scope

- Add deterministic docs-reference lint over required closeout docs `vNext+29` and `vNext+30`.
- Also lint any additional `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS*.md` doc that contains a continuity assertion block.
- Validate continuity-assertion-block artifact paths exist.
- Parse referenced JSON artifacts and fail closed on invalid JSON.
- Validate stop-gate metrics artifacts use `schema == "stop_gate_metrics@1"`.
- Validate metric-key continuity claims by comparing referenced baseline/current keysets.
- Validate provenance-proxy fields in referenced metrics JSON using frozen quality-dashboard path mapping.
- Normalize v29/v30 closeout docs by adding the frozen machine-checkable continuity assertion block.

### Locks

- Lint target-set lock is frozen:
  - required docs are exactly:
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md`
  - additional candidate docs are selected by filename regex:
    - `^DRAFT_STOP_GATE_DECISION_vNEXT_PLUS([0-9]+)\\.md$`
  - additional candidate docs are linted only when they contain a continuity assertion block matching frozen grammar.
  - checked-doc emission order is deterministic sorted path order.
- Artifact-reference validation lock is frozen:
  - linted artifact paths are sourced only from continuity assertion block fields:
    - `baseline_metrics_path`
    - `current_metrics_path`
  - referenced paths must be repository-relative under `artifacts/`.
  - absolute paths and any path containing `..` are fail-closed.
  - any path containing `\\` is fail-closed.
  - missing references fail closed.
- Metrics artifact schema lock is frozen:
  - referenced metrics JSON must declare `schema = "stop_gate_metrics@1"`.
- Metric-key continuity claim grammar lock is frozen:
  - claim source is exactly one fenced JSON block under heading `## Metric-Key Continuity Assertion`.
  - required docs-only schema: `metric_key_continuity_assertion@1`.
  - required keys:
    - `schema`
    - `baseline_metrics_path`
    - `current_metrics_path`
    - `expected_relation`
  - allowed `expected_relation` value in v31:
    - `exact_keyset_equality`
- Docs-only schema boundary lock is frozen:
  - `metric_key_continuity_assertion@1` is docs-validation-only and is not a runtime/public schema-family addition.
- Baseline normalization lock is frozen:
  - v29 and v30 closeout docs must be backfilled to include the frozen continuity assertion block.
  - backfill edits are additive-only (no edits outside insertion of the required block).
  - block insertion is idempotent (if required block exists and is valid, no duplicate block may be inserted).
- Backfill mapping lock is frozen:
  - v29 closeout continuity block maps baseline to `artifacts/stop_gate/metrics_v28_closeout.json` and current to `artifacts/stop_gate/metrics_v29_closeout.json`.
  - v30 closeout continuity block maps baseline to `artifacts/stop_gate/metrics_v29_closeout.json` and current to `artifacts/stop_gate/metrics_v30_closeout.json`.
- Provenance-proxy mapping lock is frozen:
  - referenced metrics JSON must include object field `inputs` with string fields:
    - `quality_baseline_path`
    - `quality_current_path`
  - v29 mapping requirement:
    - `inputs.quality_baseline_path == "artifacts/quality_dashboard_v28_closeout.json"`
    - `inputs.quality_current_path == "artifacts/quality_dashboard_v29_closeout.json"`
  - v30 mapping requirement:
    - `inputs.quality_baseline_path == "artifacts/quality_dashboard_v29_closeout.json"`
    - `inputs.quality_current_path == "artifacts/quality_dashboard_v30_closeout.json"`
  - missing/non-string/mismatched provenance-proxy fields fail closed.
- Continuity comparison lock is frozen:
  - keyset continuity is evaluated as set equality over `metrics` object keys only.
  - missing/non-object `metrics` fails closed.
  - derived cardinality may be reported but may not be hardcoded as authority.
- Deterministic failure-mode lock is frozen:
  - missing block, schema-invalid block, missing file, invalid JSON, or keyset mismatch all fail closed deterministically.
- Failure-code taxonomy lock is frozen:
  - allowed failure `code` values are exactly:
    - `MISSING_BLOCK`
    - `MULTIPLE_BLOCKS`
    - `BLOCK_SCHEMA_INVALID`
    - `PATH_INVALID`
    - `ARTIFACT_NOT_FOUND`
    - `JSON_INVALID`
    - `SCHEMA_MISMATCH`
    - `METRICS_OBJECT_INVALID`
    - `KEYSET_MISMATCH`
    - `PROVENANCE_MISMATCH`
- Guard output contract lock is frozen:
  - guard emits a machine-checkable report with `schema = "closeout_consistency_lint@1"`.
  - required top-level keys:
    - `schema`
    - `checked_docs`
    - `failures`
  - `checked_docs` are emitted in deterministic sorted order.
  - `failures` are emitted in deterministic sorted order by `(doc_path, code)`.
  - each failure row includes:
    - `doc_path`
    - `code`
    - `details`
- Guard output sink lock is frozen:
  - guard emits report payload to stdout only in this arc.
  - writing committed lint-report artifacts to repository paths is out-of-scope.
- CI enforcement lock is frozen:
  - closeout consistency lint must execute in CI and fail closed on violations.
  - merge is blocked when the required CI check for this lint is failing.

### Acceptance

- Guard fails closed on missing/invalid referenced artifacts.
- Guard fails closed when required continuity-assertion block is missing or schema-invalid.
- Guard fails closed on provenance-proxy mismatches in mapped v29/v30 metrics artifacts.
- Guard passes deterministically for required v29/v30 closeout chain after baseline normalization.
- Guard lints any additional closeout docs that include continuity assertion block and fails closed on violations.
- Guard output (`closeout_consistency_lint@1`) is deterministic across reruns.

## Stop-Gate Impact (v31)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- v31 closeout must include runtime-observability comparison row against v30 baseline.
- Runtime-observability closeout placement lock is frozen:
  - v31 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS31.md` inside a machine-checkable JSON block.

## Error/Exit Policy (v31)

- No new URM error-code family is introduced in this arc.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `web: close evidence-explorer template-path contract gap with deterministic fail-closed expansion`
2. `docs/tests: add v31 closeout consistency lint and backfill v29/v30 continuity assertion blocks`

## Intermediate Preconditions (for v31 start)

1. v30 lock/closeout artifacts remain authoritative and unchanged.
2. v30 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md`
3. Evidence Explorer API template contract remains available at v31 start:
   - `apps/api/src/adeu_api/main.py` (`_EVIDENCE_EXPLORER_LIST_REF_PATH_TEMPLATE`)
4. v28-v30 stop-gate metrics artifacts remain available:
   - `artifacts/stop_gate/metrics_v28_closeout.json`
   - `artifacts/stop_gate/metrics_v29_closeout.json`
   - `artifacts/stop_gate/metrics_v30_closeout.json`
5. No L2 boundary release is introduced in this arc.

## Exit Criteria (Draft)

- `E1` and `E2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Evidence Explorer API/web contract mismatch is resolved under frozen template rules.
- Closeout consistency guard passes deterministically on baseline and reruns.
- v31 closeout evidence includes runtime-observability comparison row against v30 baseline.
- No solver semantics contract delta and no trust-lane regression introduced.
