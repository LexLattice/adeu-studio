# Draft ADEU ANM Native Documentation Practice V66 Implementation Mapping v0

Status: support / implementation mapping draft.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned `V66`
family into likely package, schema, CLI, and fixture work so the family is concrete
before a starter lock is drafted.

## 1. Family Intent

`V66` should make ANM a repo-native documentation practice without treating that as:

- a repo-wide rename of all docs to `.adeu.md`
- a reopening of `V47`
- permission to infer obligations from prose
- permission to silently supersede current `.md` authority

So the implementation target is:

- explicit source discovery
- explicit source posture
- explicit document authority profile
- explicit class policy
- later explicit migration binding and reader projections

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_semantic_source`
  - source discovery
  - ANM host / companion loading
  - authority-profile parsing helpers
  - doc-class policy loading helpers
  - source-local diagnostics
- `packages/adeu_commitments_ir`
  - models and schemas for the new `V66` artifact family
- `packages/adeu_semantic_compiler`
  - repo-scale orchestration
  - repo crawling and source-set manifest construction
  - source-set compilation
  - class-policy application
  - cross-document companion validation
  - compile reports and later projection orchestration

Possible secondary surfaces:

- `spec/`
  - mirrored schemas if the repo keeps mirror export parity for the new artifact set
- `docs/generated/anm/`
  - generated reader views if later selected
- `artifacts/anm/`
  - source-set manifests, compile reports, and semantic diffs if emitted as repo
    artifacts

## 3. Candidate `V66` Artifact Set

Planning-level candidate outputs:

| Artifact | Likely slice | Role |
|---|---|---|
| `anm_source_set_manifest@1` | `V66-A` | inventory of governed ANM-bearing sources and source posture |
| `anm_doc_authority_profile@1` | `V66-A` | explicit doc class / authority layer / source posture contract |
| `anm_doc_class_policy@1` | `V66-A` | machine-checkable per-class allowed output and hard-gate policy |
| `anm_migration_binding_profile@1` | `V66-B` | host / overlay / supersession relation |
| `anm_reader_projection_manifest@1` | `V66-B` | generated reader-view metadata and drift state |
| `anm_semantic_diff_report@1` | `V66-B` | semantic additions, removals, and authority-surface drift |
| `anm_compile_report@1` | `V66-C` | repo-scale compile / validation summary |
| `anm_prose_boundary_notice_set@1` | `V66-C` | warning-only prose laundering / normative-tone notices |

## 4. `V66-A` Starter Mapping

### 4.1 Scope

`V66-A` should stay bounded to repo-scale discovery and policy posture only.

Starter outputs:

- `anm_source_set_manifest@1`
- `anm_doc_authority_profile@1`
- `anm_doc_class_policy@1`

Starter checks:

- detect `.adeu.md`
- detect registered companions
- distinguish the starter axes explicitly:
  - `doc_class`
  - `authority_layer`
  - `source_posture`
  - `lifecycle_status`
  - `classification_status`
- keep the source-set boundary explicit:
  - `discovered_doc_inventory`
  - `governed_anm_source_set`
- reject unregistered companions
- reject contradictory host / companion linkage
- reject supersession claim without explicit transition law

Recommended starter enumerations:

- `doc_class`:
  - `lock`
  - `architecture`
  - `planning`
  - `support`
  - `non_governance`
- `authority_layer`:
  - `lock`
  - `architecture`
  - `planning`
  - `support`
  - `none`
- `source_posture`:
  - `legacy_markdown`
  - `standalone_anm`
  - `companion_anm`
  - `generated_projection`
- `lifecycle_status`:
  - `living`
  - `historical`
  - `superseded`
  - `draft`
  - `generated`
- `classification_status`:
  - `classified`
  - `unknown_requires_registration`
  - `excluded_non_governance`

Entry rule for the governed ANM source set:

- a doc enters the governed source set if:
  - it has a `.adeu.md` extension; or
  - it is registered as a companion overlay; or
  - it contains a recognized ANM authority block; or
  - it is listed in the source-set manifest; or
  - a later lock explicitly opts it into `V66` validation

Plain support or historical markdown should not become hard-gated ANM source merely
because it is present in the repo.

`V66-A` companion clarification:

- `V66-A` owns only minimal companion registration fields inside
  `anm_source_set_manifest@1` and `anm_doc_authority_profile@1`
- `V66-A` does not yet emit the full `anm_migration_binding_profile@1`
- `V66-B` later upgrades that registration into the full migration-binding profile

### 4.1.1 Minimum starter field shapes

Minimum `anm_source_set_manifest@1` direction:

- top-level:
  - `schema_id`
  - `manifest_id`
  - `source_entries`
- each source entry:
  - `doc_ref`
  - `doc_id_or_none`
  - `doc_class`
  - `authority_layer`
  - `source_posture`
  - `lifecycle_status`
  - `classification_status`
  - `content_hash`
  - `profile_ref_or_none`
  - `host_doc_ref_or_none`
  - `companion_registration_status_or_none`
  - `generated_from_ref_or_none`

Minimum `anm_doc_authority_profile@1` direction:

- `doc_id`
- `doc_ref`
- `doc_class`
- `authority_layer`
- `source_posture`
- `lifecycle_status`
- `allowed_authority_blocks`
- `allowed_outputs`
- `forbidden_outputs`
- `current_markdown_authority_relation`
- `allowed_consumers`
- `requires_transition_law_for_supersession`

Minimum `anm_doc_class_policy@1` direction:

- one policy row per `doc_class`
- each row should carry:
  - `allowed_authority_layers`
  - `allowed_source_postures`
  - `allowed_authority_blocks`
  - `allowed_outputs`
  - `forbidden_outputs`
  - `hard_gates`
  - `warning_gates`

### 4.1.2 Starter class-policy matrix

Recommended starter matrix:

| Doc class | May be `.adeu.md` | May have companion | May emit `V47` D-IR from explicit D blocks | May emit lock obligation ledger | Must reject overpromotion |
|---|---:|---:|---:|---:|---:|
| `lock` | yes | yes | yes | yes, when explicitly selected | yes |
| `architecture` | yes | yes | yes, sparse / explicit only | no, unless later lock binds it | yes |
| `planning` | yes | yes | yes, scope-guard posture only | no | yes |
| `support` | optional | yes | rare / support-only | no | yes |
| `non_governance` | no by default | no by default | no | no | yes |

### 4.2 Likely Code Surfaces

Likely `adeu_commitments_ir` additions:

- new models in `src/adeu_commitments_ir/anm_models.py`
- authoritative schemas under `schema/`
- mirrored schemas under `spec/` if repo policy still requires mirror parity

Likely `adeu_semantic_source` additions:

- source-set discovery helpers
- companion-registration resolver
- document-class classifier
- authority-profile parser / validator
- source-local diagnostics for malformed authority posture

Likely `adeu_semantic_compiler` additions:

- repo-scale ANM inventory entrypoint
- repo crawling and source-set manifest construction
- compile / check orchestration over the discovered source set
- class-policy application
- cross-document companion validation
- fail-closed diagnostics for contradictory posture

### 4.3 Likely CLI / Make Targets

Planning-level candidate targets:

- `make anm-inventory`
- `make anm-check`
- `make anm-compile`

These do not need to be fully selected in `V66-A`, but the starter slice should be
designed so such entrypoints are natural rather than bolted on later.

`V66-A` compile-report timing clarification:

- `V66-A` may emit ephemeral CLI diagnostics and test assertion outputs
- `V66-A` does not yet commit a stable versioned `anm_compile_report@1` artifact
- the stable schema-governed compile report remains deferred to `V66-C`

### 4.4 Likely Fixture Set

Need at least:

- one standalone `.adeu.md` source fixture
- one registered companion overlay fixture
- one orphaned companion rejection fixture
- one contradictory doc-class posture rejection fixture
- one supersession-without-transition rejection fixture
- one planning doc with explicit ANM boundary fixture
- one support doc that remains non-authoritative even when ANM-aware

## 5. `V66-B` Preview Mapping

`V66-B` should consume the shipped `V66-A` source-set and class-policy basis and add:

- `anm_migration_binding_profile@1`
- `anm_reader_projection_manifest@1`
- `anm_semantic_diff_report@1`

Bounded role:

- make host / overlay relation explicit
- make generated reader views visible and non-authoritative by default
- make semantic drift reviewable in diffs

Deferred from `V66-A`:

- advisory prose-boundary notices
- broader adoption hardening

## 6. `V66-C` Preview Mapping

`V66-C` should remain advisory.

Likely outputs:

- `anm_compile_report@1`
- `anm_prose_boundary_notice_set@1`

Bounded role:

- surface drift
- surface overpromotion
- surface stale generated views
- surface prose that sounds normative but is not compiled

Non-goal:

- no source-of-truth transition by advisory artifact alone

## 7. Document-Class Strategy Carry-Through

The family mapping should keep the class split explicit:

- lock docs
  - highest-density ANM target
- architecture docs
  - sparse authority zones and seam maps
- planning docs
  - structured boundaries first
- support docs
  - mostly plain markdown
- historical docs
  - frozen unless explicitly migrated

This should be visible in:

- the source-set manifest
- each doc authority profile
- class-policy validation

## 8. Non-Goals

`V66` should not be mapped as:

1. wholesale doc rewrite in the starter slice
2. `V47-G`
3. a generic markdown front-matter project
4. permission to compile arbitrary prose
5. support-doc overpromotion into lock authority
6. silent replacement of historical markdown

## 9. Shaping Inputs

Primary shaping inputs for this family:

- `docs/support/anm.adeu.md`
- `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
- `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
- `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md`
- `docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md`
- `docs/DRAFT_D1_DIALECT_SPEC_v0.md`
- `docs/DRAFT_D1_NORMALIZED_IR_SPEC_v0.md`
- `docs/DRAFT_PREDICATE_CONTRACTS_BOOTSTRAP_SPEC_v0.md`
- `docs/DRAFT_CHECKER_FACT_BUNDLE_SPEC_v0.md`
- `docs/DRAFT_POLICY_EVALUATION_RESULT_SET_SPEC_v0.md`
- `docs/DRAFT_POLICY_OBLIGATION_LEDGER_SPEC_v0.md`
- `docs/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v0.md`
- `docs/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v1.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`
