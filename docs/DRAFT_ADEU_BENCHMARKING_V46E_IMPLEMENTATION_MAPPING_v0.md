# Draft ADEU Benchmarking V46E Implementation Mapping v0

Status: support note for the `V46-E` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the broader
benchmarking family and the released `V46-A` through `V46-D` repo-owned surfaces should
shape a live `V46-E` advisory consumer implementation in `packages/adeu_benchmarking`.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS140.md`
- `docs/DRAFT_ADEU_BENCHMARKING_V46_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_BENCHMARKING_V46D_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- the released `V46-D` comparison case, report, and validation artifacts as the only
  authoritative downstream consumer inputs
- the diagnostic-first and non-promotional output posture
- the requirement that later consumer seams stay explicitly subordinate to released
  benchmark artifacts rather than silently promoting them into operational authority

## Re-Author With Repo Alignment

- re-author the live advisory consumer lane under:
  - `packages/adeu_benchmarking/src/adeu_benchmarking/procedural_depth.py`
- keep the live contract ids aligned to the bounded `V46-E` starter set:
  - `adeu_benchmark_consumer_case@1`
  - `adeu_benchmark_consumer_advisory_report@1`
  - `adeu_benchmark_consumer_validation_report@1`
- consume released `V46-D` comparison refs directly
- freeze the starter consumer target to:
  - `architecture_comparison_research`
- keep advisory derivation bounded to one explicit starter mapping over:
  - released comparison status
  - released field-comparison rows
  - released comparison-validation posture
- separate deterministic advisory replay confirmation from the report-level epistemic
  posture:
  - replayable derivation confirms reproducibility only
  - starter consumer posture remains interpretive/advisory
- re-author granular support refs over:
  - released comparison-field entries
  - released comparison-validation entries
- re-author repo-native deterministic fixtures and tests under:
  - `packages/adeu_benchmarking/tests/fixtures/v46e/`
  - `packages/adeu_benchmarking/tests/`
- require deterministic authoritative schema export plus root `spec/` mirrors

## Defer To Later Slice

- routing research consumers
- role-fit research consumers
- training or distillation research consumers
- any API or web surface over benchmark consumers
- any operational promotion bridge from advisory outputs

## Do Not Import

- any consumer artifact that acts like routing authority
- any advisory output that declares a winning model or promotion entitlement
- any direct jump from released comparison evidence to training or orchestration
  decisions
