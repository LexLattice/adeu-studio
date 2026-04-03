# ODEU Sandbox App Alignment

Authority layer: support / maintainer intake note only.

Source lane:

- imported external prototype bundle
- class: `X2`
- precedent status: `non_precedent`

## Artifact Relationship

- narrative ingress note:
  [CLAIMED_SCOPE.md](/home/rose/work/LexLattice/odeu/examples/external_prototypes/odeu-sandbox-app/CLAIMED_SCOPE.md)
- unpacked source payload:
  [source_tree](/home/rose/work/LexLattice/odeu/examples/external_prototypes/odeu-sandbox-app/source_tree)
- in-pack sandbox readme:
  [source_tree/odeu_sandbox/README.md](/home/rose/work/LexLattice/odeu/examples/external_prototypes/odeu-sandbox-app/source_tree/odeu_sandbox/README.md)

The narrative note is explicitly earlier than the built artifact. The unpacked source
tree is therefore the stronger record of what the prototype actually became.

## Claimed Scope

The combined narrative and unpacked payload claim:

- a minimal browser-based ODEU simulation sandbox
- a standalone Python sim kernel plus FastAPI surface
- a no-build static UI
- local tests for the engine and API

## Observed Reachable Surfaces

The unpacked source tree contains:

- standalone sim kernel code under
  [source_tree/odeu_sandbox/sim](/home/rose/work/LexLattice/odeu/examples/external_prototypes/odeu-sandbox-app/source_tree/odeu_sandbox/sim)
- standalone FastAPI entrypoint at
  [source_tree/odeu_sandbox/api.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/odeu-sandbox-app/source_tree/odeu_sandbox/api.py)
- standalone static UI under
  [source_tree/odeu_sandbox/static](/home/rose/work/LexLattice/odeu/examples/external_prototypes/odeu-sandbox-app/source_tree/odeu_sandbox/static)
- local tests under
  [source_tree/odeu_sandbox/tests](/home/rose/work/LexLattice/odeu/examples/external_prototypes/odeu-sandbox-app/source_tree/odeu_sandbox/tests)

## Accepted Shipped Scope

Current accepted shipped scope is intentionally narrow:

- intake pack only
- unpacked source tree only
- no live repo package ownership
- no accepted app surface
- no accepted API route
- no accepted CI/build integration

## Maintainer Alignment Notes

- The prototype is structurally cleaner than the workbench overlay because it is
  already self-contained.
- It is still outside the repo’s internal ADEU lane because it introduces a new
  simulation kernel, API surface, UI surface, and test lane without prior internal
  planning.
- The unpacked tree contained runtime cache artifacts in the zip; those were removed as
  part of intake normalization because they are not source.

## Required Before Internal Integration

- decide whether this belongs as:
  - an example pack only
  - a `packages/` simulation kernel
  - an `apps/` surface
  - or a split kernel-plus-app architecture
- type the semantic objects and diagnostics against repo-owned ADEU doctrine rather
  than only prototype-local interpretation
- wire execution and verification into `.venv`, `make`, and repo CI rather than
  standalone local commands
