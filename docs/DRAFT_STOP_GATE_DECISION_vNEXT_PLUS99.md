# Draft Stop-Gate Decision vNext+99

Status: proposed gate for `V45-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS99.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `repo_schema_family_registry@1` and bounded `repo_entity_catalog@1`
  schemas validate and export cleanly with authoritative/mirror parity;
- one deterministic extraction entrypoint materializes the accepted reference fixtures
  from the same bounded repo snapshot on repeated runs;
- both artifacts carry explicit repo snapshot identity, extraction provenance, and stale-
  snapshot posture;
- both artifacts carry immutable classification-policy binding through explicit
  reference plus hash;
- schema registry rows carry:
  - family cluster;
  - primary carrier class;
  - optional secondary role-form tags;
  - lineage overlay;
  - residual flags;
  - classification posture;
  - classification method;
  - typed supporting evidence refs;
- the role-form precedence order is enforced fail-closed:
  - structural signature
  - semantic function
  - governance role
  - lexical naming;
- the representative reconstruction appendix round-trips the bounded subset under
  canonical normalized semantic equivalence rather than byte identity;
- the bounded entity catalog carries explicit scoped-issuance posture such as
  `entity_coverage_mode: bounded_schema_visible_slice`;
- settled posture is accepted only when backed by admissible adjudication support and
  bounded settlement scope for this first slice;
- rejected fixtures prove fail-closed behavior for:
  - missing snapshot identity;
  - unresolved primary carrier class;
  - naming-only role-form classification;
  - settled posture without adjudication support;
  - precedence contradiction between lexical naming and stronger structural or semantic
    evidence;
  - missing entity taxonomy axis;
  - non-round-tripping reconstruction;
- Python tests cover schema/model validation, authoritative/mirror parity, deterministic
  fixture replay, and rejection behavior.

## Do Not Accept If

- the slice claims whole-repo exhaustive entity coverage;
- `classification_policy_ref` points at interpretive air or lacks immutable binding;
- lexical naming becomes primary schema-role authority;
- inferred classifications are emitted as settled without explicit adjudication support;
- the entity catalog does not make its bounded schema-visible coverage mode explicit;
- descriptive diagnostics are treated as mutation, optimization, or recursive-amendment
  entitlement;
- the reconstruction appendix stays prose-only without explicit round-trip checking;
- stale snapshot outputs are presented as current repo truth rather than historical
  snapshot-bound evidence;
- the slice widens into symbol catalog, test-intent matrix, or optimization-register
  release.

## Local Gate

- run `make check`
