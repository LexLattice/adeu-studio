## A. Precision-hardening assessment

The retained `v0` got the hard parts right:

* repo-native placement was correct
* trinary witness status was correct
* artifact emission was correct
* intent-matrix overlay was worth keeping
* conservative widening/escalation hooks were already in place

The real precision bottleneck was simpler:

* **ordinary source changes still triggered owner-wide selection too early**
* that made the selector good at **repo → owner narrowing**
* but weak at **owner → relevant sub-slice narrowing**

The single most important policy change in this pass is:

* **owner-wide selection is no longer the default consequence of an ordinary source delta**
* it is now a **fallback**, used only when direct reach is absent or unresolved

In practice, that means the planner now tries to win with:

1. import evidence
2. support-module/import evidence
3. intent bindings
4. explicit path consumers

and only then widens.

On this repo snapshot, that materially helps the biggest pain point: `apps/api` source changes. In my local run against the real repo, a change to `apps/api/src/adeu_api/openai_config.py` selected **71 tests by evidence only** instead of the retained `v0`’s **106 owner-wide app tests**.

---

## B. Refined selection law

### Evidence-first selection

For a changed path `Δp`, select tests first from **concrete evidence**:

* changed test module itself
* tests importing the changed source module or its reverse import closure
* tests that import a **test-support module** which imports the changed source
* tests bound by `repo_test_intent_matrix`
* tests that explicitly consume the changed source/script/artifact path

These are recorded as `selection_stage = "evidence"`.

### Owner fallback

Owner-wide fallback is allowed only when one of these is true:

* changed source module has **no recoverable direct test evidence**
* changed source module path cannot be derived
* changed script/artifact/config surface has **unknown consumer reach**
* owner `pyproject.toml` changed

These are recorded as `selection_stage = "fallback"` with reasons like:

* `owner_fallback_widening`
* `reverse_local_package_dependency`

### Escalation

Full-suite escalation is now reserved for:

* root `pyproject.toml`
* root `Makefile`
* foundational-owner metadata changes
* foundational-owner source changes whose reach is unresolved or evidence-free

These are recorded as `selection_stage = "escalation"` with reasons like:

* `root_config_escalation`
* `foundational_owner_escalation`
* `unknown_reach_escalation`

### Unknown handling

`unknown` remains blocking, but it no longer automatically implies owner-wide selection when direct evidence still exists.

So:

* `unknown + evidence exists` → run the evidenced tests, mark posture widened
* `unknown + no evidence` → fallback or escalate conservatively

That is the main precision/safety balance in this pass.

---

## C. File-by-file patch plan

`packages/adeu_repo_description/src/adeu_repo_description/test_selection_v0.py`
Purpose: sharpen the selector core without relocating it.
Why needed: this is where owner fallback policy, support-module propagation, path-consumer recovery, staged reason emission, and new artifact fields belong.

`packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
Purpose: export the selector entrypoints from the package API.
Why needed: keeps the module repo-native and importable the same way other repo-description APIs are surfaced.

`apps/api/scripts/select_tests_v0.py`
Purpose: retain the thin repo-native CLI seam.
Why needed: local developers still need a stable script entrypoint under the existing `apps/api/scripts` convention.

`packages/adeu_repo_description/tests/test_test_selection_v0.py`
Purpose: replace toy tests with stronger topology-shaped selector tests.
Why needed: this pass is mostly about behavior law, not just code movement.

Patch artifact: [v0.2 patch](adeu_test_selection_v0_2.patch)

---

## D. Patch-quality code

Full updated files:

* `packages/adeu_repo_description/src/adeu_repo_description/test_selection_v0.py`
* `apps/api/scripts/select_tests_v0.py`
* `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
* `packages/adeu_repo_description/tests/test_test_selection_v0.py`

Key code changes below.

### 1. Evidence / fallback / escalation are separated structurally

```python
SelectionStage = Literal["evidence", "fallback", "escalation"]

@dataclass(frozen=True)
class SelectionReason:
    test_path: str
    selection_stage: SelectionStage
    reason_kind: str
    dependency_class: str
    witness_id: str
    detail: str
    changed_paths: tuple[str, ...] = ()

@dataclass
class _Accumulator:
    selected_by_stage: dict[SelectionStage, set[str]] = field(
        default_factory=lambda: {
            "evidence": set(),
            "fallback": set(),
            "escalation": set(),
        }
    )
    reasons_by_test: dict[str, dict[tuple[str, str, str, str, str], SelectionReason]] = field(
        default_factory=lambda: defaultdict(dict)
    )
    witnesses: dict[str, DependencyWitness] = field(default_factory=dict)
    warnings: list[str] = field(default_factory=list)
    escalation_rows: dict[tuple[str, str, str, tuple[str, ...]], EscalationDecision] = field(
        default_factory=dict
    )
    out_of_scope_changed_paths: list[str] = field(default_factory=list)

    def select_tests(
        self,
        *,
        stage: SelectionStage,
        test_paths: Iterable[str],
        reason_kind: str,
        dependency_class: str,
        witness_id: str,
        detail: str,
        changed_paths: Iterable[str],
    ) -> None:
        normalized_changed_paths = tuple(sorted(set(changed_paths)))
        for test_path in sorted(set(test_paths)):
            self.selected_by_stage[stage].add(test_path)
            reason = SelectionReason(
                test_path=test_path,
                selection_stage=stage,
                reason_kind=reason_kind,
                dependency_class=dependency_class,
                witness_id=witness_id,
                detail=detail,
                changed_paths=normalized_changed_paths,
            )
            key = (
                reason.selection_stage,
                reason.reason_kind,
                reason.dependency_class,
                reason.witness_id,
                reason.detail,
            )
            self.reasons_by_test[test_path][key] = reason
```

### 2. Test-support modules are indexed and propagated

This matters in the real repo because `apps/api/tests/path_helpers.py` is actually imported by app tests.

```python
TEST_SUPPORT_MODULE_ROOT = "__testsupport__"

def _support_module_path_for_file(*, owner: OwnerInfo, repo_rel_path: str) -> str | None:
    if owner.tests_root is None:
        return None
    prefix = f"{owner.tests_root}/"
    if not repo_rel_path.startswith(prefix) or not repo_rel_path.endswith(".py"):
        return None
    suffix = repo_rel_path[len(prefix) :]
    if Path(repo_rel_path).name.startswith("test_"):
        return None
    namespace = ".".join([TEST_SUPPORT_MODULE_ROOT, *owner.owner_key.split("/")])
    if suffix == "__init__.py":
        return namespace
    if suffix.endswith("/__init__.py"):
        body = suffix[: -len("/__init__.py")].replace("/", ".")
        return f"{namespace}.{body}" if body else namespace
    body = suffix[: -len(".py")].replace("/", ".")
    return f"{namespace}.{body}" if body else namespace
```

```python
(
    support_module_to_path,
    support_module_to_owner,
    support_module_ids_by_owner,
    support_aliases_by_owner,
    conftest_module_by_owner,
) = _walk_support_modules(resolved_repo_root, owners)
```

```python
for support_module_id, support_path in support_module_to_path.items():
    owner_key = support_module_to_owner[support_module_id]
    imported_modules, literal_paths, parse_error = _parse_python_file(
        resolved_repo_root / support_path,
        current_module=support_module_id,
        known_modules=known_modules_for_tests,
        known_roots=known_roots_for_tests,
        repo_root=resolved_repo_root,
        special_module_aliases=support_aliases_by_owner.get(owner_key),
    )
    support_imported_modules[support_module_id] = imported_modules
    support_literal_paths[support_module_id] = literal_paths
    for imported_module in imported_modules:
        if imported_module == support_module_id:
            continue
        reverse_module_imports[imported_module].add(support_module_id)
```

### 3. Relative path consumers are recovered more precisely

This matters because ADEU tests often do things like:

* `_repo_root() / "apps" / "api" / "scripts" / ...`
* `Path(__file__).resolve().parent / "fixtures" / ...`

```python
def _resolve_repo_candidate_path(*, candidate: str, repo_root: Path, file_path: Path) -> str | None:
    normalized = _normalize_path_fragment(candidate)
    if not normalized:
        return None
    if _is_repo_candidate_path(normalized, repo_root=repo_root):
        return normalized.rstrip("/")
    try:
        joined = (file_path.parent / normalized).resolve()
    except (OSError, RuntimeError, ValueError):
        return None
    try:
        repo_rel = joined.relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        return None
    try:
        exists = joined.exists()
    except (OSError, RuntimeError, ValueError):
        return None
    if exists and _is_repo_candidate_path(repo_rel, repo_root=repo_root):
        return repo_rel.rstrip("/")
    return None
```

### 4. Ordinary source changes no longer auto-widen to the owner

This is the main behavior change.

```python
if (
    owner is not None
    and owner.src_root is not None
    and changed_path.startswith(f"{owner.src_root}/")
    and changed_path.endswith(".py")
):
    matched_scope = True
    module_path = _source_module_path_for_file(owner=owner, repo_rel_path=changed_path)
    if module_path is None:
        accumulator.add_witness(
            DependencyWitness(
                witness_id=f"source_module:{changed_path}",
                dependency_class="source_module",
                subject=changed_path,
                status="unknown",
                detail="could not derive module import path for changed source file",
                changed_paths=(changed_path,),
            )
        )
        if _is_foundational_owner(owner):
            _record_full_suite_escalation(...)
        else:
            _record_owner_fallback(...)
    else:
        impacted_modules = _reverse_module_closure(index, [module_path])
        impacted_tests = set(_tests_importing_any_module(index, impacted_modules))
        path_tests = set(_tests_referencing_path(index, changed_path))
        intent_tests = set(index.intent_source_path_to_tests.get(changed_path, set()))
        evidence_tests = sorted(impacted_tests | path_tests | intent_tests)

        if changed_path in index.source_parse_errors:
            status: WitnessStatus = "unknown"
            detail = (
                f"changed source file could not be parsed ({index.source_parse_errors[changed_path]})"
            )
        else:
            status = "changed"
            detail = f"changed source module {module_path} propagates through recovered imports"

        accumulator.add_witness(...)

        if impacted_tests:
            accumulator.select_tests(
                stage="evidence",
                test_paths=sorted(impacted_tests),
                reason_kind="direct_import_dependency",
                ...
            )
        if path_tests:
            accumulator.select_tests(
                stage="evidence",
                test_paths=sorted(path_tests),
                reason_kind="artifact_consumer_dependency",
                ...
            )
        if intent_tests:
            accumulator.select_tests(
                stage="evidence",
                test_paths=sorted(intent_tests),
                reason_kind="guarded_surface_binding",
                ...
            )

        if not evidence_tests:
            if _is_foundational_owner(owner):
                _record_full_suite_escalation(...)
            else:
                _record_owner_fallback(...)
```

### 5. The artifact now shows whether the selector won narrowly or widened

```python
return {
    "schema": SCHEMA,
    "selection_algorithm": SELECTOR_VERSION,
    "repo_root": index.repo_root.as_posix(),
    "changed_paths": normalized_changed_paths,
    "dependency_class_statuses": [...],
    "evidence_selected_test_paths": evidence_selected_test_paths,
    "fallback_selected_test_paths": fallback_selected_test_paths,
    "escalation_selected_test_paths": escalation_selected_test_paths,
    "selected_test_paths": selected_test_paths,
    "skipped_test_paths": skipped_test_paths,
    "selection_reasons": accumulator.selection_reasons(),
    "risk_posture": risk_posture,
    "full_suite_recommended": full_suite_recommended,
    "escalation_reasons": accumulator.escalation_reasons(),
    "out_of_scope_changed_paths": sorted(set(accumulator.out_of_scope_changed_paths)),
    "warnings": sorted(set(accumulator.warnings)),
    "pytest_args": selected_test_paths,
    "summary": {
        "selected_test_count": len(selected_test_paths),
        "evidence_selected_test_count": len(evidence_selected_test_paths),
        "fallback_selected_test_count": len(fallback_selected_test_paths),
        "escalation_selected_test_count": len(escalation_selected_test_paths),
        "skipped_test_count": len(skipped_test_paths),
        ...
    },
}
```

---

## E. Stronger tests

Updated test suite:

* `packages/adeu_repo_description/tests/test_test_selection_v0.py`

This suite now verifies the sharpened law, not just toy correctness.

Coverage added:

* changed test files are selected directly
* direct source import closure beats owner fallback
* cross-package import closure narrows dependent-owner reach
* owner `pyproject.toml` changes still select reverse dependents
* intent-matrix bindings narrow selection without owner fallback
* owner fallback happens only when there is no direct evidence
* parse-error source changes can remain narrow when direct reach is still recoverable
* support-module imports propagate into test mapping
* script path consumers can flow through support modules
* root config still escalates

I ran:

```bash
cd <repo-root>
PYTHONPATH=$(find packages -maxdepth 2 -path '*/src' -type d | paste -sd: -):apps/api/src \
python -m pytest -q packages/adeu_repo_description/tests/test_test_selection_v0.py
```

Result: `10` tests passed.

---

## F. Example output artifacts

Example files:

* `packages/adeu_repo_description/tests/fixtures/test_selection_v0/selection_narrow_example.json`
* `packages/adeu_repo_description/tests/fixtures/test_selection_v0/selection_fallback_example.json`
* `packages/adeu_repo_description/tests/fixtures/test_selection_v0/selection_escalation_example.json`

### Narrow selection

```json
{
  "risk_posture": "narrow",
  "evidence_selected_test_paths": [
    "packages/pkg_b/tests/test_service.py"
  ],
  "fallback_selected_test_paths": [],
  "escalation_selected_test_paths": [],
  "selection_reasons": [
    {
      "test_path": "packages/pkg_b/tests/test_service.py",
      "selection_stage": "evidence",
      "reason_kind": "direct_import_dependency",
      "dependency_class": "source_module",
      "witness_id": "source_module:pkg_a.core"
    }
  ]
}
```

### Fallback-widened

```json
{
  "risk_posture": "widened",
  "evidence_selected_test_paths": [],
  "fallback_selected_test_paths": [
    "packages/pkg_a/tests/test_api.py",
    "packages/pkg_a/tests/test_smoke.py"
  ],
  "selection_reasons": [
    {
      "selection_stage": "fallback",
      "reason_kind": "owner_fallback_widening",
      "dependency_class": "package_local_blast_radius",
      "witness_id": "owner_fallback:packages/pkg_a:pkg_a.latent"
    }
  ]
}
```

### Broad escalation

```json
{
  "risk_posture": "escalated",
  "full_suite_recommended": true,
  "evidence_selected_test_paths": [],
  "fallback_selected_test_paths": [],
  "escalation_selected_test_paths": [
    "apps/api/tests/test_health.py",
    "packages/pkg_a/tests/test_core.py"
  ],
  "selection_reasons": [
    {
      "selection_stage": "escalation",
      "reason_kind": "root_config_escalation",
      "dependency_class": "escalation_rule",
      "witness_id": "escalation:root_config:pyproject.toml"
    }
  ]
}
```

Real repo sanity check from this pass:

* `apps/api/src/adeu_api/openai_config.py` moved from the retained `v0`’s owner-wide `106` selected app tests to `70` evidence-selected tests with `0` fallback tests.
* root `pyproject.toml` still correctly escalates to the full local Python suite: `278` selected test modules.

---

## G. Honest limits

This is materially sharper, but it still does **not** attempt to prove perfect impact closure.

Still out of scope:

* perfect dynamic dependency recovery
* runtime tracing / witness replay
* deep fixture dependency indexing
* semantic effect analysis at symbol/body level
* provider/API contract witnesses
* environment-variable equivalence witnesses
* database/runtime state witnesses
* full out-of-scope-path blocking
* cache invalidation machinery for persistent selector indexes

I deliberately did **not** add caching in this pass. The precision gain here came from better reach recovery, not from faster re-index invalidation logic, and adding cache state now would cost more maintenance complexity than it returns.

The highest-value next steps after this pass are:

* fixture-family and `conftest` refinement beyond owner-wide implicit reach
* optional strict mode for out-of-scope changed paths
* cached index manifests once the selection law stabilizes
* richer guarded-surface joins from repo-description artifacts, not just the reference matrix JSON
* later executable phase-1 witness tests, built on top of this sharper planner rather than replacing it

This is still the same repo-native `v0` backbone, but now it behaves much more like an evidence-first selector and much less like a package-wide blaster.
