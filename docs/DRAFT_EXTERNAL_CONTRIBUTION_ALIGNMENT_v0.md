# DRAFT External Contribution Alignment v0

## Purpose

This note defines a relaxed contribution lane for external pull requests and a
maintainer-side alignment procedure for integrating accepted work into the repo's
existing ADEU discipline.

The goal is not to weaken the internal ADEU arc model. The goal is to admit useful
outside work without pretending that every outside contribution already carries the
same intent capture, evidence, and closeout structure as repo-native work.

## Two Lanes

### 1. Internal ADEU lane

Use the full repo-native flow for:

- core architectural changes
- new modules or cross-cutting workflow changes
- schema additions or externally visible contract changes
- orchestrated experiments initiated from inside the repo

Default expectation:

- explicit intent capture before implementation
- implementation under the locked scope
- verification with the normal repo gates
- post-doc, closeout, or assessment alignment as appropriate

### 2. External single-PR lane

Use this lane for:

- outside contributors
- imported Codex-generated diffs produced against a different human intent process
- opportunistic fixes or features that arrive as a single PR without ADEU arc scaffolding

This lane is allowed to be structurally lighter, but it is still governed.

## Minimum Bar For External PRs

An external PR should, at minimum:

- state the problem it is solving
- identify touched runtime or product surfaces
- state obvious non-goals or scope bounds
- include tests for changed behavior, or say plainly what was not tested
- state the checks actually run
- avoid silent normalization of malformed model or tool output into success
- avoid claiming a shipped user-facing feature when no reachable surface is wired

These minimums are intentionally lighter than the internal ADEU lane, but they are not
optional if the contribution is going to be evaluated seriously.

## External Contribution Classes

Classify incoming external PRs before deciding how to align them:

- `X0`: local fix or hardening with no new contract surface and no workflow impact
- `X1`: feature or behavior change on an existing surface
- `X2`: new surface, new schema, or cross-cutting workflow/process change

Default handling:

- `X0` may be aligned with a small maintainer note and normal tests
- `X1` usually needs explicit intent capture and a scoped follow-up alignment step
- `X2` should usually be re-authored into repo-native ADEU planning before merge, or
  merged only with an explicit maintainer-owned follow-up bundle already scheduled

## Review Split

Review external PRs on two independent lanes:

### Lane A: code alignment

Ask whether the implementation itself matches repo engineering discipline:

- correct boundaries
- fail-closed validation
- truthful product wiring
- tests proportional to behavior
- bounded scope

### Lane B: meta-sequence alignment

Ask whether the contribution arrived through the repo's expected process:

- was intent captured before coding
- were the relevant docs updated
- were tests and evidence produced
- is there a closeout or alignment artifact

Lane B may fail even when Lane A is partly or mostly acceptable. That is normal for the
external lane and should be recorded, not hand-waved away.

## Scope And Precedent Discipline

When maintainers normalize an accepted external PR, preserve three separate scope layers:

- `claimed_scope`: what the imported contribution presented itself as shipping
- `observed_reachable_surfaces`: what the diff actually wires or makes reachable
- `accepted_shipped_scope`: the truthful maintainer judgment about what is actually accepted

Do not collapse observed surfaces into judgment, and do not let imported work become
process precedent by silence. External work remains `non_precedent` unless a maintainer
explicitly grants precedent-bearing status with a reason.

## Maintainer Alignment Post-Processing

If an external PR is accepted in principle, a maintainer should perform alignment
post-processing before merge or in an immediate follow-up maintainer PR.

Recommended sequence:

1. Classify the PR as `X0`, `X1`, or `X2`.
2. Write a short maintainer intent note capturing the accepted scope truthfully.
3. Separate code-quality findings from meta-sequence findings.
4. Add or request missing tests, evidence, or product-surface wiring.
5. If the PR title or description over-claims the shipped behavior, either shrink the
   claim or complete the missing wiring.
6. Preserve the three-layer scope model:
   - claimed scope
   - observed reachable surfaces
   - accepted shipped scope
7. Record precedent status explicitly and default it to `non_precedent` unless a
   maintainer grants precedent with a reason.
8. Decide what repo-native artifacts are needed:
   - none beyond PR notes for `X0`
   - a scoped continuation or decision note for most `X1`
   - proper internal ADEU planning docs for `X2`
9. Merge only when the accepted behavior and the recorded scope agree.
10. If merge happens before full alignment, immediately open a maintainer-owned follow-up
   PR and do not treat the imported work as completed precedent until that PR lands.

## Integration Principle

Accepted external work becomes part of repo history only after maintainers translate it
into the repo's own intelligible structure. The imported diff may be the starting point,
but the repo remains responsible for the final ADEU alignment of intent, evidence, and
governance.
