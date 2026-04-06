# DRAFT ADEU Edge Ledger Implementation Mapping v0

## Mapping stance

This note maps the logical-edge-ledger proto onto concrete repo surfaces.
It is intentionally implementation-facing and bounded.

## Upstream inputs preserved as-is

### V45 preserved as descriptive substrate

The proto reuses V45 conventions but does not alter V45 contracts:

- canonical hash / id construction
- typed schemas
- repo-native `symbol:` and `test:` ref conventions
- explicit epistemic posture vocabulary
- schema export discipline

### V50 preserved as released symbol-audit family

The proto consumes these released V50 artifacts as already-bounded inputs:

- scope manifest
- symbol census
- coverage report
- semantic audit

The proto requires a `closed_clean` coverage posture before deriving applicability or adjudication.
That is the guard against hidden scope drift.

## Module-to-artifact mapping

### `models.py`

Defines five artifact families and their associated status vocabularies.

Important design choices:

- archetype rows are unique and lexicographically ordered;
- hashes and ids are computed only from canonical payload fields;
- status fields are typed, not free prose;
- revision judgments encode both topology and maturity posture.

### `taxonomy.py`

Owns the constant layer.

It materializes:

- the edge-class catalog;
- the probe-template catalog;
- helper lookup functions.

Each archetype carries:

- applicability cues;
- structural-safety cues;
- test tokens;
- default probe templates.

This is the module that prevents every future review from reinventing the abstract edge space from scratch.

### `applicability.py`

Owns the first variable layer.

It joins:

- verified repo source text;
- AST feature extraction;
- name/signature cues;
- V50 semantic-audit side-effect and family cues;
- starter taxonomy rules.

Its output is a full per-symbol frame over all archetypes, not only a sparse list of found witnesses.
That is important because absence of applicability evidence and partial applicability evidence are represented explicitly.

### `adjudicate.py`

Owns the second variable layer.

It does not attempt to prove correctness.
Instead it composes bounded signals into explicit status rows:

- package-local test evidence
- structural-safety cues
- semantic-audit confidence posture
- optional explicit witness / checked-without-witness inputs

This is where the proto stops pretending that every symbol is either “green” or “red”.

### `revision.py`

Owns the compounding doctrine.

The main responsibility is not to decide whether a specific bug exists.
The responsibility is to decide whether a new finding changes the **ledger itself**.

That decision is typed, hashed, and reviewable.

### `export_schema.py`

Keeps the package repo-native by exporting authoritative schemas under:

- `packages/adeu_edge_ledger/schema/`
- `spec/`

It also preserves the repo norm that exported schemas must not leak absolute local paths.

## Pilot symbol choices in tests

The tests intentionally stay inside the V50 pilot scope rooted in `adeu_architecture_ir`.
The fixtures and assertions focus on symbols that expose distinct adjudication postures:

- `AdeuArchitectureAnalysisRequest`
  - shows `covered_by_existing_tests`
- `capture_adeu_architecture_analysis_source_set_payload`
  - shows `bounded_safe_by_structure`
- `materialize_adeu_architecture_analysis_settlement_frame_payload`
  - shows `applicable_unchecked`
- `_run_git`
  - shows `deferred`

This provides a real, bounded demonstration that the ledger is not just a flat pass/fail wrapper.

## Why package-local test scanning was chosen

A broader integration with V45 test-intent matrices was deliberately deferred.
The shipped proto uses a simpler bounded method first:

- stay inside the admitted package test tree;
- collect repo-native `test:` refs;
- match symbol identity tokens and edge test tokens conservatively.

That keeps the proto small, deterministic, and compatible with the “adjacent consumer” placement choice.

## Why the taxonomy is three levels deep now

Three levels were chosen because the repo needs enough depth to separate:

- broad families such as `failure_path` or `dependency_boundary`;
- meaningful stable subfamilies such as `rejection_fail_closed` or `filesystem_external_tool`;
- concrete reusable archetypes such as `fail_closed_on_mismatch` or `git_command_failure_surface`.

A flat label list would not support principled ledger growth.
A deeper ontology would be premature for the shipped bounded scope.

## Boundaries that were intentionally preserved

The proto preserves these repo boundaries:

- no code mutation;
- no broad API surface;
- no full CI redesign;
- no reinterpretation of V45/V50 release contracts;
- no hidden authority leap from advisory descriptive outputs to normative execution rights.

## Expected next iteration points

Natural next steps, if later selected, would be:

1. a witness artifact family for externally executed probes;
2. optional joins to V45 test-intent matrices;
3. cross-symbol family ledgers and coverage rollups;
4. migration helpers for split/merge operations inside the taxonomy.

Those are future extensions, not hidden requirements of the current proto.
