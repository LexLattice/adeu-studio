## Verdict

The first-slice bundle is **substantially improved and directionally ready** for `V66-A`.

I would mark it:

> **Green / amber: architecturally correct, close to lock-ready, but needs a few implementation-precision edits before the first implementation pass should rely on it.**

The bundle now addresses the major problems from the earlier family review:

* it keeps `V66-A` downstream of the released `V47-A` through `V47-F` ANM substrate rather than reopening `D@1`, D-IR, predicate contracts, fact bundles, result sets, or ledgers;
* it separates `doc_class`, `authority_layer`, `source_posture`, `lifecycle_status`, and `classification_status`;
* it distinguishes `discovered_doc_inventory` from `governed_anm_source_set`;
* it allows minimal companion registration while deferring the full migration-binding profile to `V66-B`;
* it defers generated reader views, semantic diffs, and stable compile reports;
* it explicitly rejects silent Markdown supersession and support/planning overpromotion.  

The lock draft is also much stronger than the earlier family-level mapping: it selects only `anm_source_set_manifest@1`, `anm_doc_authority_profile@1`, and `anm_doc_class_policy@1`, and its machine-checkable contract repeats the important non-equivalence rules. 

I would **not** widen the slice. The current scope is the right first implementation slice.

---

## Overall bundle assessment

| Document                                                                         | Review                                                                                                                                                                                                                               |
| -------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `ASSESSMENT_vNEXT_PLUS182_EDGES.md`                                              | Good edge assessment. It names the right risks: reopening `V47`, axis collapse, accidental whole-repo gating, companion supersession, premature reader/diff surfaces, premature compile report, and support overpromotion. Keep it.  |
| `DRAFT_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_V66A_IMPLEMENTATION_MAPPING_v0.md` | Strong support mapping. It contains the right starter surfaces, field direction, governed-source entry rule, and “do not import” list. Needs more exact enum/schema/source-of-truth details.                                         |
| `DRAFT_STOP_GATE_DECISION_vNEXT_PLUS182.md`                                      | Good proposed gate. It has the right accept/reject posture and explicitly blocks `V66-B` / `V66-C` surfaces landing early. Needs separate closeout posture for implementation tests.                                                 |
| `LOCKED_CONTINUATION_vNEXT_PLUS182.md`                                           | Strong starter lock draft. It selects the right artifact set, packages, fail-closed posture, axis split, and non-equivalence laws. Needs a few contract clarifications before it becomes the operative implementation lock.          |

---

## What is working especially well

### 1. `V66-A` is no longer vague family prose

The slice is now concrete:

```text
anm_source_set_manifest@1
anm_doc_authority_profile@1
anm_doc_class_policy@1
```

and the lock correctly says these are **document-governance starter surfaces only**, not runtime behavior, Markdown supersession, generated-reader authority, or `D@1` language widening. 

That is the correct first slice.

### 2. The axis-split problem is fixed

The earlier risk was that `historical`, `generated`, and `unknown` might get mixed into the same enum as `lock`, `architecture`, `planning`, and `support`. The new bundle explicitly keeps the axes separate:

```text
doc_class
authority_layer
source_posture
lifecycle_status
classification_status
```

This appears in the assessment, mapping, stop gate, and lock.    

That was the most important architectural correction.

### 3. The governed source-set boundary is now explicit

The bundle correctly says that repo crawling is not the same thing as turning the whole Markdown corpus into governed ANM source. The mapping says a document enters the governed ANM source set only through `.adeu.md`, registered companion status, recognized ANM authority block presence, explicit manifest listing, or later lock opt-in. 

That prevents `V66-A` from becoming a stealth repo-wide documentation migration.

### 4. Companion mode is properly bounded

The bundle now has the right posture:

```text
minimal companion registration in V66-A
full migration binding deferred to V66-B
supersession without transition law fails closed
```

The stop gate and lock both preserve that distinction.  

This is exactly the anti-drift rule needed during migration.

### 5. `V47` stays closed

The assessment and mapping both explicitly say `V66-A` consumes the released `V47-A` through `V47-F` substrate and does not widen `D@1`, selector/predicate ownership, or policy-consumer doctrine.  

That keeps the implementation family from mutating into `V47-G`.

---

## Required edits before implementation

These are not conceptual objections. They are implementation-precision fixes.

### 1. Resolve “lock draft” versus operative lock status

`LOCKED_CONTINUATION_vNEXT_PLUS182.md` is named as a lock and has `Authority Layer: lock`, but its status says **“Bounded starter lock draft.”** The stop-gate marker also says `all_passed: false`.  

That is fine for review, but before implementation starts the repo should make the authority state unambiguous.

Use one of these postures:

```text
Option A:
  Keep it as draft.
  Do not treat it as implementation authority yet.

Option B:
  After stop-gate acceptance, change status to locked/accepted.
  Treat it as the operative V66-A implementation lock.

Option C:
  Keep this as draft and create a final locked continuation artifact.
```

Do not let a file that says both “lock” and “draft” become implementation authority by implication.

### 2. Add exact enum values for all five axes

The bundle names the axes, but the implementation should not infer enum values from prose.

Add explicit starter enums:

```json
{
  "doc_class_values_for_v66a": [
    "lock",
    "architecture",
    "planning",
    "support",
    "non_governance"
  ],
  "authority_layer_values_for_v66a": [
    "lock",
    "architecture",
    "planning",
    "support",
    "none"
  ],
  "source_posture_values_for_v66a": [
    "legacy_markdown",
    "standalone_anm",
    "companion_anm",
    "generated_projection"
  ],
  "lifecycle_status_values_for_v66a": [
    "living",
    "historical",
    "superseded",
    "draft",
    "generated"
  ],
  "classification_status_values_for_v66a": [
    "classified",
    "unknown_requires_registration",
    "excluded_non_governance"
  ]
}
```

This belongs in the lock contract or in the V66A implementation mapping.

### 3. Add `schema_id` to every starter record

The mapping gives `schema_id` for the source-set manifest direction, but not clearly for `anm_doc_authority_profile@1` or `anm_doc_class_policy@1`. 

All three starter surfaces should require `schema_id`:

```yaml
anm_source_set_manifest@1:
  schema_id: anm_source_set_manifest@1

anm_doc_authority_profile@1:
  schema_id: anm_doc_authority_profile@1

anm_doc_class_policy@1:
  schema_id: anm_doc_class_policy@1
```

Without this, schema export and fixture validation will be weaker than the rest of the ANM lineage.

### 4. Define where document authority profiles come from

The bundle selects `anm_doc_authority_profile@1`, but it does not yet fully specify whether profiles are:

```text
source-authored blocks,
front matter,
manifest-derived records,
compiler-derived records,
or some combination.
```

This must be settled before implementation.

Recommended rule:

```text
For V66-A, an anm_doc_authority_profile@1 may be produced from:
1. an explicit ANM profile block, when present;
2. a source-set manifest entry, when the document is registered there;
3. deterministic compiler classification, only for fields the compiler is allowed
   to infer mechanically, such as file path and source posture.

Front matter may help discovery, but front matter does not mint obligations and
must not override an explicit profile block or manifest entry.
```

Also add:

```text
If multiple profile sources exist, they must agree.
Contradictory profile sources fail closed.
```

This prevents front matter or filename convention from becoming hidden authority.

### 5. Define content hashing and deterministic inventory order

The lock says the source-set manifest must be typed and replayable, and that the same discovered inventory plus same governed inclusion rules plus same frozen policy yields the same outputs. 

To make that real, add deterministic hash and ordering rules:

```text
content_hash:
  sha256 of raw file bytes, repo-relative file as read from disk

doc_ref:
  repo-relative POSIX path

inventory_order:
  sorted by doc_ref ascending

semantic_hash:
  not selected in V66-A unless explicitly added later

timestamps:
  not included in semantic content for V66-A starter records
```

Also specify excluded paths if necessary:

```text
ignored_by_inventory:
  - .git/
  - .venv/
  - node_modules/
  - __pycache__/
  - generated caches not committed as docs
```

Without this, two machines can produce different manifests for the same repo.

### 6. Resolve the CLI / API surface mismatch

The lock requires “one repo-scale inventory/check entrypoint,” but the machine-checkable contract has:

```json
"api_surfaces": []
```

That can be valid if the entrypoint is not considered an API, but the distinction should be explicit. 

Add something like:

```json
{
  "api_surfaces": [],
  "cli_or_validation_entrypoints_for_v66a": [
    "anm-inventory",
    "anm-check"
  ],
  "cli_entrypoints_are_repo_validation_surfaces_not_runtime_api_surfaces": true
}
```

Or remove the entrypoint deliverable from the lock. I recommend keeping the entrypoint and adding the clarification.

### 7. Define “recognized ANM authority block” carefully

The V66A mapping says a doc enters the governed ANM source set if it “contains a recognized ANM authority block.” 

That is correct, but dangerous unless examples are excluded.

A support doc might contain a code-fenced example of `:::D@1`. That should not necessarily make the support doc governed ANM source.

Add this rule:

```text
Only compiler-recognized authority zones count.

Code-fenced examples, quoted examples, escaped examples, or prose discussion of
D@1 do not count as authority blocks and do not opt a document into governed ANM
source by themselves.
```

Add a fixture for it.

### 8. Add a precedence rule over older family drafts

The older family mapping still contains looser language about classifying docs into `lock`, `architecture`, `planning`, `support`, `historical`, `generated`, and `unknown`. 

The V66A bundle fixes this through five independent axes. To avoid accidental regression, add an explicit precedence statement:

```text
For V66-A, the vNext+182 axis split controls over any earlier family-level prose
that treated historical, generated, or unknown as flat document classes.
```

This is especially important because the lock admits the earlier family architecture and mapping as shaping inputs. 

---

## Recommended additions to the lock contract

I would add this small patch to the machine-checkable contract.

```json
{
  "v66a_lock_axis_split_overrides_prior_flat_family_classification_language": true,
  "required_doc_class_values_for_v66a": [
    "lock",
    "architecture",
    "planning",
    "support",
    "non_governance"
  ],
  "required_authority_layer_values_for_v66a": [
    "lock",
    "architecture",
    "planning",
    "support",
    "none"
  ],
  "required_source_posture_values_for_v66a": [
    "legacy_markdown",
    "standalone_anm",
    "companion_anm",
    "generated_projection"
  ],
  "required_lifecycle_status_values_for_v66a": [
    "living",
    "historical",
    "superseded",
    "draft",
    "generated"
  ],
  "required_classification_status_values_for_v66a": [
    "classified",
    "unknown_requires_registration",
    "excluded_non_governance"
  ],
  "required_schema_ids_for_v66a": [
    "anm_source_set_manifest@1",
    "anm_doc_authority_profile@1",
    "anm_doc_class_policy@1"
  ],
  "content_hash_algorithm_for_v66a": "sha256_raw_file_bytes_v1",
  "doc_ref_normalization_for_v66a": "repo_relative_posix_path",
  "source_inventory_order_for_v66a": "doc_ref_ascending",
  "nondeterministic_timestamps_excluded_from_v66a_semantic_outputs": true,
  "recognized_authority_block_examples_do_not_enter_governed_source_set_by_themselves": true,
  "front_matter_may_seed_discovery_but_does_not_mint_obligations": true,
  "contradictory_profile_sources_fail_closed_for_v66a": true,
  "cli_or_validation_entrypoints_for_v66a": [
    "anm-inventory",
    "anm-check"
  ],
  "cli_entrypoints_are_repo_validation_surfaces_not_runtime_api_surfaces": true
}
```

This would close most implementation ambiguity without widening the slice.

---

## Suggested fixture additions

The bundle already requires tests for source-set separation, axis separation, companion failure posture, class-policy overpromotion, and no early `V66-B` / `V66-C` surfaces. 

I would add these exact fixture categories:

```text
packages/adeu_semantic_source/tests/fixtures/v66a/
  standalone_lock_profile.adeu.md
  standalone_planning_profile.adeu.md
  registered_companion_overlay.adeu.md
  reject_orphaned_companion.adeu.md
  reject_supersession_without_transition.adeu.md
  reject_contradictory_profile_sources.adeu.md
  markdown_with_code_fenced_d1_example_not_governed.md
  support_anm_awareness_not_lock_promotion.adeu.md

packages/adeu_commitments_ir/tests/fixtures/v66a/
  reference_anm_source_set_manifest.json
  reference_anm_doc_authority_profile.json
  reference_anm_doc_class_policy.json
  reject_doc_class_lifecycle_status_conflation.json
  reject_forbidden_output_by_doc_class.json
  reject_generated_projection_claims_source_authority.json
```

The code-fenced `D@1` example fixture is important. It protects support/tutorial prose from becoming governed source merely because it explains ANM syntax.

---

## Per-document notes

### `ASSESSMENT_vNEXT_PLUS182_EDGES.md`

Keep it. It is a good pre-lock risk register.

It successfully identifies the right seven edge classes:

1. accidental reopening of `V47`;
2. flattened classification;
3. accidental whole-repo ANM gating;
4. companion drift into silent supersession;
5. early generated reader / semantic diff overpromotion;
6. starter diagnostics becoming stable compile artifacts too early;
7. support-layer awareness drifting into lock/planning promotion. 

Recommended additions:

```text
Edge 8: profile source-of-truth ambiguity
Edge 9: deterministic inventory / hash ambiguity
Edge 10: code-fenced authority-block examples accidentally entering governed source
Edge 11: lock draft status versus operative implementation authority
```

### `DRAFT_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_V66A_IMPLEMENTATION_MAPPING_v0.md`

This is the most useful implementation-shaping document in the bundle.

It now has the right field direction and source-set entry rule, and it explicitly says not to import broader migration binding, reader projection, semantic diff, compile report, `D@1` widening, support overpromotion, repo-wide rename posture, or silent Markdown supersession. 

Recommended revisions:

* add enum values;
* add schema IDs for all three records;
* define profile source precedence;
* define hash/path/order determinism;
* define code-fenced example handling;
* add exact package/module/schema paths.

### `DRAFT_STOP_GATE_DECISION_vNEXT_PLUS182.md`

Good as a proposed gate.

Its “Accept When” and “Do Not Accept If” sections align with the intended first slice and correctly block premature `V66-B` / `V66-C` features. 

One issue: the local gate says the full Python lane is skipped because the bundle is docs-only. That is fine for **starter-draft review**, but not for **implementation closeout**.

Add:

```text
At implementation closeout, V66-A must run the Python/model/schema/fixture lane.
The docs-only skip applies only to pre-start scaffold review.
```

### `LOCKED_CONTINUATION_vNEXT_PLUS182.md`

This is a strong lock draft. It selects the right slice and carries the right anti-laundering boundaries:

* no `D@1` widening;
* no full migration binding profile;
* no generated reader projection;
* no semantic diff report;
* no stable compile report artifact;
* no repo-wide Markdown rename;
* no supersession without transition law;
* no hidden-cognition governance. 

Recommended edits:

1. resolve draft-vs-lock status;
2. add enum values;
3. add schema ID requirements;
4. add deterministic hash/path/order rules;
5. add profile source precedence;
6. add CLI/entrypoint surface clarification;
7. add precedence over older family docs that used flatter classification language.

After those edits, this is a suitable `V66-A` starter lock.

---

## Implementation-readiness judgment

I would approve the following:

```text
Proceed with V66-A implementation planning.
Keep the selected record shapes:
  - anm_source_set_manifest@1
  - anm_doc_authority_profile@1
  - anm_doc_class_policy@1

Keep the package set:
  - adeu_semantic_source
  - adeu_commitments_ir
  - adeu_semantic_compiler

Keep the hard non-goals:
  - no D@1 widening
  - no generated reader views
  - no semantic diffs
  - no full migration binding
  - no stable compile report
  - no implicit markdown supersession
  - no repo-wide .adeu.md rename
```

I would not approve implementation closeout until the precise enum/schema/hash/profile/entrypoint rules are added and tested.

---

## Bottom line

The first-slice bundle now has the right architecture and the right boundaries. It is no longer a generic ANM adoption idea; it is a bounded starter slice with explicit source-set, authority-profile, and class-policy surfaces.

The remaining fixes are mostly **mechanical determinism and authority-state clarity**:

```text
make the lock status unambiguous;
pin enum values;
pin schema IDs;
pin profile source precedence;
pin content hashing and inventory ordering;
clarify CLI surfaces;
protect D@1 examples from accidental authority;
make V66-A override older flat-classification prose.
```

After those amendments, `V66-A` is a good first implementation slice.
