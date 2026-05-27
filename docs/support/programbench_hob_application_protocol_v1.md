# ProgramBench HOB Application Protocol v1

Authority layer: support.

This note is a support-layer overlay on
`docs/support/programbench_hob_application_protocol_v0.md`. It keeps the v0
catalog and broker mechanics, but hardens how ProgramBench runs may use
`covered_by_probe_matrix` after the first HOB trdsql run showed that a clean
ledger can still be too shallow.

## Controlling Artifacts

```text
base protocol:
  docs/support/programbench_hob_application_protocol_v0.md

catalog:
  docs/support/programbench_hob_obligation_catalog_v0.json

question cards:
  docs/support/programbench_hob_node_question_cards_v0.md

catalog_id:
  programbench-odeu-meta-program-obligations

catalog_version:
  programbench-hob-v0

catalog_hash:
  sha256:ce171df30a0747750dbc2469a98d44f9b5da87acbc03a4095dd8525965d837e9
```

## V1 Hardening Summary

V0 made inherited obligations deterministic. V1 adds a stricter handoff rule:

```text
An inherited node is not meaningfully probe-covered merely because one probe
touches the family label.
```

Before a node can support official-intended handoff as
`covered_by_probe_matrix`, the worker must produce concrete question-card
coverage for the node.

## Question-Card Gate

For each active HOB node marked `covered_by_probe_matrix`, produce a
`question_card_row` using the shape in
`programbench_hob_node_question_cards_v0.md`.

The status is official-intended invalid if any of these are true:

```text
answered_questions is empty
concrete_probe_refs is empty
negative_or_boundary_probe_refs is empty for a node with failure branches
sibling_coverage_posture = representative_only
closure_effect = blocks_official_intended_eval
the row only restates the HOB node label
the row has no public/reference observation, clean probe, or explicit deferral
```

Representative examples can still support a scoped experiment, but they cannot
support a gold or official-intended readiness posture.

## Public-Schema Re-Entry Rule

When public help, version output, no-args output, debug output, config examples,
or reference observation exposes a behavior-bearing schema item, the item must
be routed through the HOB tree before implementation.

For each schema item:

```text
1. bind it to an existing node,
2. create or update that node's question-card row,
3. terminalize it with probes,
4. prove it pass-through or irrelevant, or
5. record it as catalog-extension pressure.
```

Do not treat help-harvested items as plain notes. If a discovered option, mode,
format, route, renderer, diagnostic, or state behavior changes the program
surface, it is a live descent obligation.

## Lifecycle Activation Trigger

Node `7` (`State, Lifecycle, Mutation, And Side Effects`) must be activated if
public/reference behavior shows any of these:

```text
multiple statements
mutation statements
output-file routing
database files or DSNs
temporary files
caches, locks, or persistent resources
write-back/exporter behavior
cleanup or rollback behavior
```

Leaving node `7` as `candidate_pending` after those observations is a traversal
bug, not a scoped implementation decision.

## Held-Out And Metamorphic Gate

Node `12.4` is a hard pre-official-eval gate for ProgramBench runs that claim
official-intended readiness.

Before official eval, the run must include a held-out/metamorphic probe set
that is distinct from the original reference scout. The set must cover newly
discovered public-schema families and at least one negative or boundary case for
high-risk format, route, renderer, diagnostic, and state nodes.

Allowed postures:

```text
covered_by_probe_matrix:
  concrete held-out/metamorphic probes exist and pass locally

scoped_deferred_with_expected_risk:
  official-intended eval is blocked, scoped experiment may proceed

blocked_pending_observation:
  more reference observation is required

blocked_pending_equivalence:
  candidate/reference or packaged/evaluator equivalence is not established
```

Do not mark `12.4` as future-owned while also treating the candidate as ready
for official-intended eval.

## Broad-Leaf Sibling Gate

Broad nodes with many sibling discriminators need sibling coverage, not just a
single example. This is especially important for ProgramBench classes such as:

```text
input dialect and reader options
resource routing and glob expansion
embedded query language binding
state and mutation lifecycle
output renderers and writer options
diagnostic precedence and stream routing
resource ecology and packaging equivalence
```

A worker may mark a sibling set as scoped-ready only if missing siblings are
explicitly listed with risk. Silent omission blocks readiness.

## First Improvement Loop From A HOB Run

When a HOB run reaches official eval and post-eval pressure shows shallow
probe ownership, do not restart from scratch. Resume from the current run:

```text
1. Read HOB-C delta attribution and remaining failure groups.
2. Reopen activation/status only for nodes implicated by the pressure.
3. Apply the question-card gate to those nodes.
4. Generate additional reference probes from public/reference behavior.
5. Run those probes against reference and candidate with split stdout/stderr/exit.
6. Diagnose pass/fail groups against the question cards.
7. Patch implementation only after the mismatch class is understood.
8. Re-run the targeted probes.
9. Run held-out/metamorphic probes before any next official-intended eval.
```

Official failures may guide where to look, but they remain post-eval pressure.
They do not become clean first-pass evidence unless independently reproduced
through allowed public/reference observation.

## Current Trdsql Repair Batch

For the trdsql HOB run rooted at:

```text
artifacts/manual_runs/programbench_trdsql_hob_gpt55_medium_20260521T192607+0300
```

the v1 continuation should target these areas first:

```text
activation:
  reopen node 7 as applies

input dialects and options:
  nodes 3.7 and 4.1-4.13

output router and renderers:
  nodes 3.9 and 8.1-8.14

CLI, config, and diagnostics:
  nodes 1, 2.2, 2.7, 3.10, and 9

SQL, binding, and lifecycle:
  nodes 5, 6, and 7

official-intended gate:
  node 12.4 held-out/metamorphic probes
```

The first improvement loop should produce question-card coverage, targeted
reference/candidate probes, a candidate patch, and local targeted parity before
requesting another official eval.

