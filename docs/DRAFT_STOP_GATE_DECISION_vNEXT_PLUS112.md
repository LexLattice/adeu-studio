# Draft Stop-Gate Decision vNext+112

Status: proposed gate for `V48-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS112.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- one canonical `anm_taskpack_binding_profile@1` validates and exports cleanly;
- the committed reference binding fixture replays deterministically on repeated runs;
- every accepted fixture binds exactly one released `V47-E` policy source, one
  released `V45` scope source, one released `V45-F` scope-binding entry, and one
  worker subject;
- every admitted `V47-E` row resolves to exactly one bound released `D-IR` clause and
  does not self-authorize apart from that clause lineage;
- every admitted `V45-F` entry resolves to the same bound scope surface / binding
  subject posture and remains admission-only rather than execution-authorizing;
- taskpack-category mappings remain explicit and bounded to:
  - allowlist;
  - forbidden;
  - commands;
  - evidence slots;
- command and evidence-slot projections remain kernel-shaped rather than free prose;
- contradictory projections fail closed instead of selecting local precedence;
- prompt/chat/`AGENTS.md` prose remains projection-only and prompt-boundary conflicts
  fail closed;
- stale or unresolved released lineage fails closed for:
  - policy source;
  - scope source;
  - scope-binding entry;
- unsupported policy-to-taskpack mapping requests fail closed;
- Python tests cover:
  - schema/model validation,
  - committed fixture replay,
  - exact starter vocabulary enforcement,
  - single-policy / single-scope / single-worker invariants,
  - prompt-conflict fail-closed behavior,
  - lineage-resolution fail-closed behavior.

## Do Not Accept If

- the first slice quietly invents policy composition, policy precedence, or scope
  union / widening semantics;
- the admitted `V47-E` row is treated as policy authority apart from its bound clause;
- the admitted `V45-F` entry is treated as execution-envelope authority by itself;
- prompt text, chat prose, or `AGENTS.md` can add authority beyond the typed binding
  profile;
- raw repo discovery can widen the bound scope without released `V45` / `V45-F`
  lineage;
- contradictory allowlist / forbidden / command / evidence-slot projections are
  tolerated;
- the slice emits taskpack manifests, bundle hashes, signature envelopes, runner
  results, attestation outputs, or conformance reports as if later `V48` paths had
  already shipped;
- taskpack surface categories widen beyond the released kernel categories in this
  slice;
- multi-worker topology or broader execution authority appears in the first release;
- stale upstream lineage is tolerated as implementation-defined instead of fail
  closed.

## Local Gate

- run `make arc-start-check ARC=112`
