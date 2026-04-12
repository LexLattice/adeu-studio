## A. Hardened `v0` concept

After inspecting the repo, the strongest first landing is **not** a standalone executable phase-1 witness pytest suite yet. The repo already has witness-adjacent assets, but they are still metadata-first:

* `packages/adeu_repo_description` already owns repo graph / symbol / test-intent description logic.
* `packages/adeu_edge_ledger/src/adeu_edge_ledger/probe_test_intent.py` is a **bridge** from test-intent metadata to probe applicability, not a runnable cross-repo witness harness.
* `apps/api/fixtures/repo_description/vnext_plus103/repo_test_intent_matrix_v103_reference.json` currently has **19 entries**, all bound to one `packages/adeu_repo_description/tests/test_repo_description_v45b.py` module, so it is useful as an overlay, not as a complete dependency oracle.
* Under the repo’s current root pytest posture, the in-scope runnable package/app suite is **278 test modules / 2182 `test_*` functions**. That is large enough that a conservative local selector already has real developer value.

So `v0` should be a **dependency-witness planner/selector**: it computes witness statuses from repo structure plus explicit metadata, emits a machine-readable artifact, and lets the developer run the selected pytest slice.

### Dependency classes in scope

`v0` supports these dependency classes:

1. `changed_test_file`
   Directly changed `test_*.py` files.

2. `test_support_surface`
   Changed non-test Python under an owner’s `tests/` tree.

3. `source_module`
   Changed Python source module under an owner `src/` tree, with local reverse import closure.

4. `package_local_blast_radius`
   Any changed owner-local source/metadata widens to all tests in that owner.

5. `reverse_local_package_dependency`
   Any owner depending transitively on a changed owner has its tests selected.

6. `intent_guarded_surface`
   `repo_test_intent_matrix` guarded-surface bindings add tests when a guarded source path changes.

7. `artifact_or_fixture_surface`
   Changed non-Python fixture/config/artifact paths under recognized roots, mapped by explicit path references when possible.

8. `app_script_surface`
   Changed `apps/*/scripts/*.py` paths, mapped by literal path consumers in tests.

9. `owner_pyproject`
   Changed package/app `pyproject.toml`.

10. `foundational_repo_config`
    Root `pyproject.toml` and root `Makefile`.

11. `escalation_rule`
    Synthetic witness used when widening rules require the full local Python suite.

### Witness semantics

General rule:

* `changed`: the witnessed surface is directly hit by the delta, and its reach is known enough to act on.
* `unknown`: the surface is hit, but reach is ambiguous or parsing/mapping failed.
* `identical`: the surface is not hit by the delta and no widening rule forces rerun.

Important `v0` detail: it does **not** materialize a full global inventory of `identical` witnesses. It computes witnesses only for delta-induced subjects, then skips all tests not touched by any `changed` or `unknown` witness.

Per class:

* `changed_test_file`
  Entity: a pytest module.
  `changed`: its path is in the delta.
  `unknown`: never.

* `test_support_surface`
  Entity: Python file under `tests/` but not named `test_*.py`.
  `changed`: file changed.
  Reach: all tests in that owner.
  `unknown`: never.

* `source_module`
  Entity: source file under `src/`, resolved to a local import path.
  `changed`: file changed and AST/module recovery succeeds.
  Reach: tests importing the changed module or any local reverse-import dependent.
  `unknown`: source parse failure or module-path recovery failure.

* `package_local_blast_radius`
  Entity: package/app owner.
  `changed`: any owner source or owner metadata changed.
  Reach: all tests in that owner.
  `unknown`: never.

* `reverse_local_package_dependency`
  Entity: dependent owner <- changed owner relation.
  `changed`: dependent owner is in the transitive reverse local dependency closure of the changed owner, based on package-local `pyproject.toml` dependencies.
  `unknown`: never.

* `intent_guarded_surface`
  Entity: guarded source path from the test-intent matrix.
  `changed`: changed source path matches a guarded surface entry.
  Reach: tests bound by matrix entries.
  `unknown`: never in `v0`. Missing bindings do **not** create unknown.

* `artifact_or_fixture_surface`
  Entity: changed non-Python path under recognized fixture/artifact/config roots or extensions.
  `changed`: explicit literal/path-join consumers are found in tests.
  `unknown`: artifact changed but explicit consumers are not fully recovered.
  Reach under `unknown`: owner tests or family-level path consumers.

* `app_script_surface`
  Entity: changed script under `apps/*/scripts`.
  `changed`: explicit literal/path-join consumer tests found.
  `unknown`: script changed but no consumer tests recovered.
  Reach under `unknown`: all tests in the owning app.

* `owner_pyproject`
  Entity: package/app `pyproject.toml`.
  `changed`: file changed.
  Reach: owner tests + reverse local dependent owner tests.
  `unknown`: never.

* `foundational_repo_config`
  Entity: root `pyproject.toml` or root `Makefile`.
  `changed`: file changed.
  Reach: escalation to full local Python suite.
  `unknown`: never.

* `escalation_rule`
  Entity: full local Python suite.
  `unknown`: widening posture requires full run.
  This is synthetic because the “subject” is the execution posture itself.

### Selection law

For a changed set `Δ`, `v0` computes all witness subjects induced by `Δ`.

Run test `T` when any of these is true:

* `T` is itself a changed test file.
* A `changed` or `unknown` witness has `T` in its related test set.
* `T` is in the changed owner’s package-local blast radius.
* `T` is in an owner that depends transitively on the changed owner.
* `T` is bound to a changed guarded surface by the intent matrix.
* Escalation is active.

Skip `T` only when:

* no induced witness with status `changed` or `unknown` reaches `T`, and
* no escalation rule applies.

Two repo-native refinements matter:

* `repo_test_intent_matrix` is a **positive overlay**, not an exclusive source of truth.
* Absence of an intent binding is **not blocking** in `v0`; structural rules still decide.

### Escalation law

`v0` escalates to the full in-scope local Python suite when:

1. root `pyproject.toml` changes
2. root `Makefile` changes
3. a foundational owner changes

Foundational owner is defined in `v0` as an owner with transitive reverse local dependency closure size `>= 8`. In the current ADEU repo graph, that resolves to:

* `packages/adeu_ir`
* `packages/adeu_patch_core`
* `packages/adeu_lean`
* `packages/adeu_kernel`
* `packages/urm_runtime`

Unknown artifact/script reach widens conservatively, but does **not** full-escalate in `v0`.

### Out-of-scope law

`v0` does **not** try to prove:

* full semantic impact closure
* dynamic fixture dependency flow
* runtime environment / env-var witness equivalence
* external provider/API contract equivalence
* DB schema/runtime state equivalence
* transitive impact through arbitrary non-literal file loading
* complete symbol-level guarded-surface inference for all tests

Also, changed paths outside the bounded in-scope surfaces are recorded in `out_of_scope_changed_paths`, but they do **not** currently force a full run. That is an intentional `v0` limit, not a hidden guarantee.

---

## B. Proposed module placement and rationale

### Files created or modified

`packages/adeu_repo_description/src/adeu_repo_description/test_selection_v0.py`
Purpose: reusable selector/planner core.
Why here: `adeu_repo_description` already owns repo-self-description logic, repo dependency graph semantics, symbol/test-intent models, and schema-visible repo analysis.

`apps/api/scripts/select_tests_v0.py`
Purpose: thin operator-facing CLI entrypoint.
Why here: `apps/api/scripts` is already the repo’s seam for small utility/lint/build scripts invoked locally.

`packages/adeu_repo_description/tests/test_test_selection_v0.py`
Purpose: bounded selector test suite.
Why here: colocated with the core library it exercises.

`packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
Purpose: export the selector API from the package.
Why here: repo-native package API surfacing.

### Why this placement is better than alternatives

Not `adeu_edge_ledger`: `probe_test_intent.py` is downstream and bridge-oriented. The selector belongs upstream with repo topology and test-intent description assets.

Not root-only script code: the owner graph, AST indexing, witness computation, and artifact schema are reusable library logic.

Not a Makefile-first landing: root `Makefile` currently keeps `test` as plain `pytest`. I left that contract unchanged so `v0` lands as an opt-in local accelerator rather than silently redefining repo test behavior.

---

## C. Actual implementation plan

### Core data structures

`OwnerInfo`

* owner key like `packages/adeu_repo_description` or `apps/api`
* owner kind: `package` or `app`
* distribution name from `project.name`
* import roots from `src/*`
* local dependency owners
* reverse local dependency owners
* tests root, scripts root, pyproject path

`SelectorIndex`

* discovered owners
* all in-scope test paths
* tests by owner
* module ↔ source-path maps
* reverse source import graph
* test imported modules
* test literal repo paths
* parse errors
* intent-matrix path → tests overlay

`DependencyWitness`

* `witness_id`
* `dependency_class`
* `subject`
* `status`
* `detail`
* related tests
* changed paths

`SelectionReason`

* per-test explanation row
* dependency class + witness id + changed paths

`_Accumulator`

* selected tests
* deduped reasons
* witness rows
* escalation reasons
* warnings
* out-of-scope changed paths

### How changed paths are discovered

Three modes are supported:

1. explicit repeated `--changed-path`
2. newline-delimited `--changed-paths-file`
3. git discovery with `--base-ref`

Git discovery is conservative and repo-native:

* `git merge-base <base-ref> HEAD`
* diff merge-base..HEAD
* diff working tree vs `HEAD`
* optionally include untracked files

All paths are normalized to repo-relative POSIX form.

### How dependency-class witnesses are computed

`build_selector_index(...)` does the structural indexing:

* discover owners from:

  * `packages/*/pyproject.toml`
  * `apps/*/pyproject.toml`
* parse package metadata with `tomllib`
* map `project.name` to owner
* compute local dependency edges from `project.dependencies`
* compute transitive reverse dependency closure per owner
* walk `src/` trees to map local modules
* parse source ASTs to recover local imports and build reverse source import closure
* parse tests to recover:

  * imported local modules
  * literal repo-relative string paths
  * piecewise `Path(...) / "..." / ...` path joins
* load `repo_test_intent_matrix` as a light JSON overlay and map guarded source paths to tests

`_process_changed_path(...)` then classifies each changed path into witness classes:

* direct test file
* test support module
* changed source module
* owner pyproject
* app script
* artifact/fixture/config surface
* root foundational config

For source files:

* derive module path
* compute reverse import closure
* select tests importing any impacted module
* also widen to the full owner test set
* also widen to reverse dependent owners
* also overlay intent-matrix bindings when present

For artifacts/scripts:

* use explicit literal path consumers when found
* otherwise emit `unknown` and widen conservatively to owner/family tests

### How tests are mapped to dependency classes

Tests are mapped by three mechanisms:

1. **import-based mapping**
   AST import recovery against local known modules

2. **owner-based mapping**
   every test belongs to exactly one discovered owner

3. **explicit surface mapping**
   path literals / path-join expressions and intent-matrix guarded surfaces

This is intentionally simple and robust. It avoids heavyweight static dataflow.

### How `repo_test_intent_matrix` is consumed

Default path:

`apps/api/fixtures/repo_description/vnext_plus103/repo_test_intent_matrix_v103_reference.json`

`v0` reads it as a lightweight JSON overlay and supports:

* `internal_module_boundary` with `module:<path>`
* `internal_symbol` with `symbol:<path>:<qualname>:<kind>`

In both cases, `v0` extracts the guarded source path and adds those bound tests when that source path changes.

Because current matrix coverage is sparse, the overlay is additive only.

### How reverse package dependency closure is computed

From each package/app `pyproject.toml`:

* read `project.name`
* normalize dependency specifiers to distribution names
* connect local owner A → local owner B when A depends on B by distribution name
* compute transitive reverse closure for widening

This naturally pulls in app-level tests when apps depend on changed packages, because `apps/api/pyproject.toml` participates as an owner.

### Result serialization

The selector emits a machine-readable artifact like this:

```json
{
  "schema": "repo_test_selection_plan@1",
  "selection_algorithm": "dependency_witness_selector_v0",
  "changed_paths": ["..."],
  "dependency_class_statuses": [{ "...": "..." }],
  "selected_test_paths": ["..."],
  "skipped_test_paths": ["..."],
  "selection_reasons": [{ "...": "..." }],
  "risk_posture": "narrow",
  "full_suite_recommended": false,
  "escalation_reasons": [],
  "out_of_scope_changed_paths": [],
  "warnings": [],
  "pytest_args": ["..."],
  "summary": {
    "selected_test_count": 6,
    "skipped_test_count": 272,
    "unknown_witness_count": 0,
    "changed_witness_count": 2,
    "out_of_scope_changed_path_count": 0
  }
}
```

`risk_posture` is one of:

* `narrow`
* `widened`
* `escalated`

The CLI never silently runs pytest. It plans and emits.

---

## D. File-by-file code skeleton or patch-quality code

Full drop-in artifacts:

* [Patch provenance: `adeu_test_selection_v0.patch`](/home/rose/work/LexLattice/odeu/docs/support/adeu_test_selection_v0.patch)
* [Core module: `test_selection_v0.py`](/home/rose/work/LexLattice/odeu/packages/adeu_repo_description/src/adeu_repo_description/test_selection_v0.py)
* [CLI entrypoint: `select_tests_v0.py`](/home/rose/work/LexLattice/odeu/apps/api/scripts/select_tests_v0.py)
* [Test suite: `test_test_selection_v0.py`](/home/rose/work/LexLattice/odeu/packages/adeu_repo_description/tests/test_test_selection_v0.py)

### 1. `packages/adeu_repo_description/src/adeu_repo_description/test_selection_v0.py`

Key public API from the actual file:

```python
SCHEMA = "repo_test_selection_plan@1"
SELECTOR_VERSION = "dependency_witness_selector_v0"
DEFAULT_INTENT_MATRIX_PATH = (
    "apps/api/fixtures/repo_description/vnext_plus103/"
    "repo_test_intent_matrix_v103_reference.json"
)

def build_selector_index(
    *,
    repo_root: Path | None = None,
    intent_matrix_path: str | None = DEFAULT_INTENT_MATRIX_PATH,
) -> SelectorIndex: ...

def discover_changed_paths_from_git(
    *,
    repo_root: Path | None = None,
    base_ref: str | None = None,
    include_untracked: bool = True,
) -> list[str]: ...

def select_python_tests_v0(
    *,
    changed_paths: Iterable[str],
    repo_root: Path | None = None,
    intent_matrix_path: str | None = DEFAULT_INTENT_MATRIX_PATH,
) -> dict[str, Any]: ...

def main(argv: list[str] | None = None) -> int: ...
```

Actual selector entrypoint:

```python
def select_python_tests_v0(
    *,
    changed_paths: Iterable[str],
    repo_root: Path | None = None,
    intent_matrix_path: str | None = DEFAULT_INTENT_MATRIX_PATH,
) -> dict[str, Any]:
    index = build_selector_index(repo_root=repo_root, intent_matrix_path=intent_matrix_path)
    accumulator = _Accumulator()
    accumulator.warnings.extend(index.warnings)

    normalized_changed_paths = sorted({_normalize_repo_rel_path(path) for path in changed_paths})
    for changed_path in normalized_changed_paths:
        _process_changed_path(index, accumulator, changed_path)

    full_suite_recommended = bool(accumulator.escalation_reasons)
    if full_suite_recommended:
        for test_path in index.all_test_paths:
            accumulator.select_tests(
                test_paths=[test_path],
                reason_kind="escalation_full_suite",
                dependency_class="escalation_rule",
                witness_id="escalation:full_suite",
                detail="one or more widening rules require a full local Python test run",
                changed_paths=normalized_changed_paths,
            )
        accumulator.add_witness(
            DependencyWitness(
                witness_id="escalation:full_suite",
                dependency_class="escalation_rule",
                subject="full_python_suite",
                status="unknown",
                detail="widening rules recommend a full local Python test run",
                related_tests=tuple(index.all_test_paths),
                changed_paths=tuple(normalized_changed_paths),
            )
        )

    selected_test_paths = sorted(accumulator.selected)
    skipped_test_paths = sorted(set(index.all_test_paths) - set(selected_test_paths))
    if full_suite_recommended:
        risk_posture = "escalated"
    elif any(witness.status == "unknown" for witness in accumulator.witnesses.values()):
        risk_posture = "widened"
    else:
        risk_posture = "narrow"

    return {
        "schema": SCHEMA,
        "selection_algorithm": SELECTOR_VERSION,
        "repo_root": index.repo_root.as_posix(),
        "changed_paths": normalized_changed_paths,
        "dependency_class_statuses": [
            witness.to_dict()
            for witness in sorted(accumulator.witnesses.values(), key=lambda row: row.witness_id)
        ],
        "selected_test_paths": selected_test_paths,
        "skipped_test_paths": skipped_test_paths,
        "selection_reasons": accumulator.selection_reasons(),
        "risk_posture": risk_posture,
        "full_suite_recommended": full_suite_recommended,
        "escalation_reasons": sorted(set(accumulator.escalation_reasons)),
        "out_of_scope_changed_paths": sorted(set(accumulator.out_of_scope_changed_paths)),
        "warnings": sorted(set(accumulator.warnings)),
        "pytest_args": selected_test_paths,
        "summary": {
            "selected_test_count": len(selected_test_paths),
            "skipped_test_count": len(skipped_test_paths),
            "unknown_witness_count": sum(
                1 for witness in accumulator.witnesses.values() if witness.status == "unknown"
            ),
            "changed_witness_count": sum(
                1 for witness in accumulator.witnesses.values() if witness.status == "changed"
            ),
            "out_of_scope_changed_path_count": len(set(accumulator.out_of_scope_changed_paths)),
        },
    }
```

Actual CLI plumbing in the same module:

```python
def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Plan a conservative local Python pytest selection using dependency witnesses, "
            "owner metadata, import closure, and optional repo_test_intent_matrix bindings."
        )
    )
    parser.add_argument("--repo-root", type=Path, default=None)
    parser.add_argument("--changed-path", action="append", default=[])
    parser.add_argument("--changed-paths-file", type=Path, default=None)
    parser.add_argument("--base-ref", default=None)
    parser.add_argument("--no-untracked", action="store_true")
    parser.add_argument("--intent-matrix-path", default=DEFAULT_INTENT_MATRIX_PATH)
    parser.add_argument("--no-intent-matrix", action="store_true")
    parser.add_argument("--write-artifact", type=Path, default=None)
    parser.add_argument(
        "--stdout-format",
        choices=("json", "paths", "pytest-args"),
        default="json",
    )
    return parser.parse_args(argv)
```

### 2. `apps/api/scripts/select_tests_v0.py`

This is the full file:

```python
from __future__ import annotations

from adeu_repo_description.test_selection_v0 import main


if __name__ == "__main__":
    raise SystemExit(main())
```

### 3. `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`

Minimal export change:

```python
from .test_selection_v0 import (
    DEFAULT_INTENT_MATRIX_PATH,
    SCHEMA as TEST_SELECTION_PLAN_SCHEMA,
    SELECTOR_VERSION as TEST_SELECTION_SELECTOR_VERSION,
    build_selector_index,
    discover_changed_paths_from_git,
    main as test_selection_main,
    select_python_tests_v0,
)
```

### 4. `packages/adeu_repo_description/tests/test_test_selection_v0.py`

Representative real test from the file:

```python
def test_repo_test_intent_matrix_bindings_are_used_when_present(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": _package_pyproject("pkg_a"),
            "packages/pkg_a/src/pkg_a/__init__.py": "__all__ = []\n",
            "packages/pkg_a/src/pkg_a/core.py": "VALUE = 1\n",
            "packages/pkg_b/pyproject.toml": _package_pyproject("pkg_b"),
            "packages/pkg_b/src/pkg_b/__init__.py": "__all__ = []\n",
            "packages/pkg_b/tests/test_contract.py": (
                "def test_contract() -> None:\n"
                "    assert True\n"
            ),
            "apps/api/fixtures/repo_description/vnext_plus103/repo_test_intent_matrix_v103_reference.json": json.dumps(
                {
                    "test_intent_entries": [
                        {
                            "test_ref": "test:packages/pkg_b/tests/test_contract.py#test_contract",
                            "guarded_surface_ref": {
                                "guarded_surface_ref_kind": "internal_module_boundary",
                                "guarded_surface_ref_value": "module:packages/pkg_a/src/pkg_a/core.py",
                            },
                        }
                    ]
                }
            ),
        },
    )

    payload = select_python_tests_v0(
        repo_root=repo_root,
        changed_paths=["packages/pkg_a/src/pkg_a/core.py"],
    )

    assert "packages/pkg_b/tests/test_contract.py" in payload["selected_test_paths"]
    assert _witness_status(payload, "intent_guard:packages/pkg_a/src/pkg_a/core.py") == "changed"
```

---

## E. Tests for the new module

The new bounded test suite is here:

* [Selector tests](/home/rose/work/LexLattice/odeu/packages/adeu_repo_description/tests/test_test_selection_v0.py)

It verifies exactly the behaviors you asked for:

* changed test files are included
* direct source-import impact selects dependent tests
* reverse local package dependency widening selects dependent owner tests
* empty delta skips everything
* unknown artifact/fixture reach widens conservatively
* root config change escalates to full suite
* repo test-intent matrix bindings are applied when present
* changed app scripts select piecewise path consumers

Repo-native validation command:

```bash
.venv/bin/python -m pytest -q packages/adeu_repo_description/tests/test_test_selection_v0.py
```

Result:

```text
........                                                                 [100%]
```

There are pre-existing warnings from current repo modules, but the selector tests themselves pass.

---

## F. Usage examples

Assume the repo is bootstrapped in its normal editable-install `.venv`.

### Narrow local delta

```bash
.venv/bin/python apps/api/scripts/select_tests_v0.py \
  --changed-path packages/adeu_edge_ledger/src/adeu_edge_ledger/probe_test_intent.py \
  --stdout-format paths
```

In the current repo this selects 6 `adeu_edge_ledger` tests and reports:

* `risk_posture = "narrow"`
* `full_suite_recommended = false`

Sample artifact: [narrow selection JSON fixture](/home/rose/work/LexLattice/odeu/packages/adeu_repo_description/tests/fixtures/test_selection_v0/selection_narrow_example.json)

Example excerpt:

```json
{
  "changed_paths": [
    "packages/adeu_edge_ledger/src/adeu_edge_ledger/probe_test_intent.py"
  ],
  "risk_posture": "narrow",
  "full_suite_recommended": false
}
```

### Broad run from foundational config change

```bash
.venv/bin/python apps/api/scripts/select_tests_v0.py \
  --changed-path pyproject.toml \
  --stdout-format json
```

In the current repo this selects all 278 in-scope test modules and reports:

* `risk_posture = "escalated"`
* `full_suite_recommended = true`

Sample artifact: [broad selection JSON fixture](/home/rose/work/LexLattice/odeu/packages/adeu_repo_description/tests/fixtures/test_selection_v0/selection_broad_example.json)

### Delta from git

```bash
.venv/bin/python apps/api/scripts/select_tests_v0.py \
  --base-ref origin/main \
  --write-artifact .artifacts/test-selection.json \
  --stdout-format pytest-args
```

### Example JSON shape

```json
{
  "schema": "repo_test_selection_plan@1",
  "selection_algorithm": "dependency_witness_selector_v0",
  "selected_test_paths": [
    "packages/adeu_edge_ledger/tests/test_edge_ledger_probe_test_intent.py"
  ],
  "selection_reasons": [
    {
      "test_path": "packages/adeu_edge_ledger/tests/test_edge_ledger_probe_test_intent.py",
      "reason_kind": "owner_local_surface",
      "dependency_class": "package_local_blast_radius",
      "witness_id": "package_surface:packages/adeu_edge_ledger",
      "detail": "packages/adeu_edge_ledger local surface changed",
      "changed_paths": [
        "packages/adeu_edge_ledger/src/adeu_edge_ledger/probe_test_intent.py"
      ]
    }
  ]
}
```

---

## G. Honest limitations and next-step extensions

### Current limitations

1. This is a **planner/selector**, not an executable phase-1 witness pytest suite. That is deliberate.

2. `repo_test_intent_matrix` is only a sparse positive overlay right now. In the current repo fixture it covers 19 guarded-surface rows, all pointing into one repo-description test module.

3. Artifact and fixture reach is path-based, not full semantic loader tracing. Indirect `open(...)`, helper loaders, dynamic fixture factories, and registry-driven lookups can fall back to `unknown`.

4. Import analysis is bounded to local Python AST recovery. It does not attempt heroic resolution across dynamic imports, plugin registries, or runtime monkeypatch behavior.

5. Out-of-scope changed paths are recorded, but not blocking. That is the sharpest conservative gap in `v0`.

6. `identical` is implicit, not globally enumerated as a full witness inventory.

7. The selector does not change `make test`; it is opt-in for local developer speedup.

### Best next extensions

1. Add `--strict-out-of-scope`, which escalates on any unmatched changed path.

2. Persist a cached selector index / witness manifest so repeated local runs are faster.

3. Add fixture-family and `conftest.py` indexing to improve `artifact_or_fixture_surface` precision.

4. Add symbol-level guarded-surface overlays derived from `adeu_repo_description` artifacts rather than only consuming the reference matrix JSON.

5. Add provider/runtime witness classes for app contract surfaces where the repo already has parity/config assets.

6. Add optional Makefile sugar such as `make test-select BASE_REF=origin/main`, while keeping `make test` unchanged.

7. Use the existing `probe_test_intent.py` seam as the basis for a later `v1` executable witness layer, once there is broader released applicability-frame coverage.

The current landing is already useful: it is real, conservative, repo-native, and it reduces wasted local pytest runs without pretending to solve perfect semantic impact analysis.
