# ADEU v3.0 Semantics (Locked)

This document defines the v3.0 SMT integration contract for deterministic kernel behavior.

## Assurance levels

- `kernel_only`: no solver-backed claim
- `solver_backed`: claim derived from SMT solver evidence
- `proof_checked`: reserved for proof-checked backends (Lean roadmap)

SMT outputs are **solver evidence**, not certificates.

## Validator statuses

`ValidatorResult.status` is one of:

- `SAT`
- `UNSAT`
- `UNKNOWN`
- `TIMEOUT`
- `INVALID_REQUEST`
- `ERROR`

Kernel mode mapping:

- `STRICT`: `UNKNOWN`/`TIMEOUT` => `REFUSE`
- `LAX`: `UNKNOWN`/`TIMEOUT` => `WARN`
- `INVALID_REQUEST`: always `ERROR` severity

## Predicate semantics (IR-only)

- `(defined <def_id>)`: closed-world; missing `def_id` evaluates `false`
- `(refers_to_doc "...")`: true iff the string appears in IR-internal doc refs
  (`ProvenanceRef.doc_ref` and `DocRef.doc_ref`)
- no external lookups in v3.0

## Effective norms and conflict checks

1. Kernel computes `EffectiveNorms` from `D_norm.statements` and applicable exceptions.
2. Exceptions modify norms only when conditions are IR-evaluable and true.
3. Conflict checks operate on active effective norms.
4. SMT obligation is batched per IR check for candidate obligation-vs-prohibition overlaps.

Current v3.0 conflict witness encoding:

- `UNSAT` means at least one kernel-derived conflict candidate exists.
- `SAT` means no conflict candidates exist.
- unsat core returns a witness subset of named atoms (`a:<object_id>:<json_path_hash>`).

## Deterministic assertion naming

Each named SMT assertion uses:

`a:<object_id>:<json_path_hash>`

Where:

- `json_path_hash = sha256(json_path).hexdigest()[:12]`
- full `json_path` is preserved in request `atom_map` metadata

## Reproducibility fields

Each validator run records:

- backend name and version
- timeout
- solver options
- `formula_hash`
- `request_hash`
- structured evidence payload (`model` / `unsat_core` / `stats`)
