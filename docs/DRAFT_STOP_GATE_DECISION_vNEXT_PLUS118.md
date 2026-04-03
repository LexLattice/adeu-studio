# Draft Stop-Gate Decision vNext+118

Status: proposed gate for `V49-B`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS118.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the repo-owned `adeu_semantic_forms` package remains the only live owner of the
  recovery lane;
- `parser.py` consumes exactly one released `adeu_semantic_parse_profile@1` and emits
  exactly one released `adeu_semantic_parse_result@1`;
- the recovery lane remains bounded to `repo_policy_work` and released `V49-A`
  vocabularies only;
- recovery outcomes are typed exactly to:
  `resolved_singleton`, `typed_alternatives`, `clarification_required`, and
  `rejected_unsupported`;
- the emitted parse-result structure remains frozen to:
  - released result fields only;
  - released candidate fields only;
  - released ambiguity and rejected-diagnostic posture only;
- candidate distinctness is determined only by released
  `normal_form.semantic_hash`;
- dedupe and alternative ordering are deterministic before `candidate_rank`
  assignment;
- `clarification_required` emits zero candidates only and uses typed ambiguity
  diagnostics rather than partial candidate shells;
- alias and anchor resolution follow the frozen precedence law:
  exact anchor or exact phrase before normalized alias, no silent equal-strength
  choice;
- recovery explanations remain support-only and do not affect semantic identity or
  candidate distinctness;
- committed fixtures prove:
  - resolved singleton replay;
  - typed alternatives replay;
  - clarification required replay;
  - rejected unsupported replay;
  - semantic-hash dedupe;
  - deterministic alternative ordering;
- targeted Python tests cover parser behavior and deterministic fixture replay;
- no deterministic lowering, `V48` bridge helper, or product surface appears in the
  same slice.

## Do Not Accept If

- the slice quietly redefines `V49-A` contracts instead of consuming them;
- multiple profiles, multiple domains, or batched inputs are introduced in the first
  recovery release;
- free-form heuristics mint new relations, lanes, object kinds, or domains;
- candidate distinctness depends on evidence or other support-only fields;
- alternative ordering depends on incidental iteration order;
- clarification emits partial candidate shells or unsupported inputs are coerced into
  apparent success;
- unresolved alias or anchor conflicts are silently forced into one winner;
- deterministic lowering or `V48` seed emission appears in the same slice;
- CLI, API, or web consumers appear in the same slice;
- prototype parser code is imported wholesale into live package paths.

## Local Gate

- run `make arc-start-check ARC=118`
