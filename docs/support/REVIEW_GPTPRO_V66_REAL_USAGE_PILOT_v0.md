## Verdict

The pilot output is **substantively useful**. It no longer looks like a system that only survives fixtures. On this small live-doc cohort, `V66` did the important real-world things: it separated discovered docs from governed ANM sources, classified lock / architecture / planning / support posture sanely, preserved companion non-supersession, excluded generated reader views from source authority, detected a stale reader projection, and produced a bounded advisory result instead of laundering prose into policy.

But it is **not maintainer-workflow ready yet**. The strongest next move is a **maintainer-facing runner with a compact human review projection**, not another schema family and not a broad migration expansion.

The practical status is:

```text
Core architecture: passed pilot.
Anti-laundering posture: passed pilot.
Replayable artifact chain: mostly passed pilot.
Maintainer usability: still the bottleneck.
```

This is aligned with the shipped family design: `V66-A` owns source-set / authority-profile / class-policy posture, `V66-B` owns migration / reader projection / semantic diff, and `V66-C` owns advisory compile/prose-boundary hardening only, without generating new authority.   

---

## What the actual pilot proves

### 1. `V66-A` behaved like a real adoption layer

Observed from the pilot bundle:

```text
discovered_doc_inventory: 7 docs
governed_anm_source_set: 5 docs
generated reader docs discovered but excluded from governed source
doc classes: lock / architecture / planning / support
source postures: legacy_markdown / companion_anm / standalone_anm
```

That is a meaningful result. The system did not collapse “everything seen by the crawler” into “everything governed.” That was one of the main risks `V66-A` was meant to prevent: discovered inventory must stay distinct from governed ANM source, and plain docs should not become hard-gated merely by existing. 

The classification also looks right:

```text
LOCKED_CONTINUATION_vNEXT_PLUS184.md -> lock / legacy_markdown
ARCHITECTURE_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_FAMILY_v0.md -> architecture / legacy_markdown
DRAFT_NEXT_ARC_OPTIONS_v51.md -> planning / legacy_markdown
docs/support/anm.adeu.md -> support / standalone_anm
overlay -> lock / companion_anm
```

That is not just fixture behavior. It is the document-class strategy operating on a live-looking cohort.

### 2. `V66-B` produced useful migration/projection evidence

The pilot emitted:

```text
binding_count: 1
projection rows: 2
LOCKED_CONTINUATION_vNEXT_PLUS184 reader projection: current / in_sync
support anm reader projection: stale / source_changed_projection_stale
semantic diff rows: 18
```

The companion binding is properly non-overriding:

```text
binding_posture: registered_non_overriding_companion
current_markdown_authority_relation: current_markdown_controlling
supersession_claim_status: none
explicit_transition_law_ref_or_none: null
```

That is exactly the desired migration posture. A companion exists, but it does not silently supersede the current Markdown host. `V66-B` was supposed to make host/overlay relation, reader projection, and semantic drift visible without minting generated-reader or semantic-diff authority. 

### 3. `V66-C` gave a specific advisory result

The pilot’s advisory result was:

```text
report_status: valid
recommended_adoption_posture: needs_projection_refresh
reason_codes:
  - ANM_V66C_NEEDS_PROJECTION_REFRESH
notice_kinds:
  - normative_tone_without_compiled_authority_block
  - projection_staleness_visible
```

This is useful. It did not emit a generic “something is wrong” result. It gave a maintainer-actionable primary answer: refresh the stale generated reader projection.

It also preserved the anti-laundering line: the normative-tone warning remained advisory; example and quoted text did not become compiled authority. That is the key `V66-C` constraint: compile reports and prose-boundary notices are advisory-only, non-entitling, and not transition law. 

---

## Where the output is still awkward

### 1. The semantic diff is correct but too verbose for human review

The semantic diff has 18 rows and appears to be an initial-baseline report:

```text
baseline_kind: none_initial_report
change_kind: initial
surface counts:
  doc_class_policy: 5
  doc_authority_profile: 5
  source_set_entry: 5
  migration_binding: 1
  reader_projection_manifest: 2
```

That is deterministic and useful for replay. It is not yet a good PR review surface. A maintainer needs:

```text
Changed:
  - support reader projection stale
  - one non-overriding lock companion registered
  - no supersession claims
  - no generated projection authority
  - no semantic-diff authority

Full JSON:
  artifacts/...
```

The machine artifact can stay verbose. The review projection should not be.

### 2. The prose-boundary notice is too weakly located

The notice row is structurally bounded, but not maintainer-friendly:

```text
notice_id: notice:normative_tone:sample:plain-prose
source_doc_ref: docs/support/anm.adeu.md
subject_ref: sample:plain-prose
evidence_refs:
  - sample:plain-prose
```

That proves the detector can distinguish prose from authority, but it does not yet tell a maintainer where to look. It needs at least:

```text
file
line range
short excerpt hash
optional short excerpt
why it was noticed
what action is recommended
whether no action is also acceptable
```

Right now, the projection-staleness notice is actionable; the normative-tone notice is more like a proof-of-boundary than a useful maintenance task.

### 3. `recommended_adoption_posture` hides secondary findings

The compile report has two diagnostics:

```text
normative_tone_without_compiled_authority_block
projection_staleness_visible
```

but only one reason code:

```text
ANM_V66C_NEEDS_PROJECTION_REFRESH
```

That primary recommendation is reasonable, but the report should also carry secondary reason codes or secondary advisory actions. Otherwise, the maintainer may miss that there was also a prose-boundary notice.

Recommended shape:

```json
{
  "primary_advisory_posture": "needs_projection_refresh",
  "primary_reason_codes": ["ANM_V66C_NEEDS_PROJECTION_REFRESH"],
  "secondary_advisory_items": [
    {
      "posture": "needs_more_registration",
      "reason_code": "ANM_V66C_NORMATIVE_TONE_REVIEW",
      "severity": "warning"
    }
  ]
}
```

The primary result should remain one value. The review surface should not bury secondary signals.

### 4. The official artifacts do not show the excluded inventory clearly enough

The pilot summary shows seven discovered docs and five governed docs, but the `anm_source_set_manifest.json` only lists the governed entries. That is acceptable for a source-set manifest, but it weakens maintainer explainability.

For daily use, the runner should display:

```text
Discovered but excluded:
  docs/generated/anm_reader/LOCKED_CONTINUATION_vNEXT_PLUS184.reader.md
    reason: generated_projection_non_authoritative
  docs/generated/anm_reader/anm.reader.md
    reason: generated_projection_non_authoritative
```

This matters because generated reader projections are precisely the place where authority overread can creep back in. `V66-C` explicitly requires generated projections and semantic diff to remain shaping-only and non-authoritative. 

### 5. The hash basis is not obvious to a maintainer

The artifacts carry many hash fields, which is good. But from the bundle alone, the hash recipe is not obvious enough for a human reviewer to verify. Raw file hashes and sorted JSON hashes did not obviously correspond to the carried hashes I checked, which may be expected if these are semantic/model hashes, but the output should say so.

Add one field or banner:

```json
"hashing_policy": {
  "algorithm": "sha256",
  "canonicalization": "adeu_model_canonical_json_v1",
  "excludes": ["..."],
  "includes": ["..."]
}
```

This is not a conceptual failure. It is a replayability presentation gap.

### 6. The pilot is still narrow and partly scaffolded

The cohort is real enough to be meaningful, but still small:

```text
4 real docs
1 added companion overlay
2 added generated reader projections
```

That is a good first real-usage pilot, not a production proof. It verifies the family’s behavior on a live-shaped path. It does not yet prove that the system stays low-noise across a larger set of support, planning, architecture, generated, historical, and companion docs.

---

## Is `V66-C` good enough to guide maintainer action?

**Yes, for projection refresh.**

The advisory result `needs_projection_refresh` is exactly the kind of actionable signal `V66-C` should produce. The stale support reader projection is visible, bounded, and non-authoritative. That is a successful advisory outcome.

**Not yet, for prose-boundary maintenance.**

The normative-tone notice is safe, but not sufficiently actionable. It proves the anti-laundering boundary; it does not yet give a maintainer enough context to decide whether to rewrite prose, add an explicit authority block, ignore the notice, or register a doc/profile change.

So the current `V66-C` signal is:

```text
Actionable for projection drift.
Safe but underdeveloped for prose-boundary review.
Good enough for pilot.
Not enough for daily workflow without a review projection.
```

---

## What is good enough now

The following should be retained as successful:

```text
- generated reader projections are discovered but not governed source
- current Markdown remains controlling
- companion overlay is registered and non-overriding
- no transition law is inferred from proximity
- semantic diff is review-only
- advisory output does not promote source authority
- examples and quoted text do not become compiled authority
- V66-C emits a specific, allowed advisory posture
```

That means the family’s core anti-laundering design survived contact with live docs.

---

## What is awkward but acceptable

These are acceptable for now, but should not become the maintainer UX:

```text
- verbose initial semantic diff rows
- JSON-first artifact review
- sample-based prose-boundary notices
- one primary advisory result hiding secondary warnings
- hash refs that are not human-verifiable from the emitted bundle
- direct library execution instead of a repo-facing command
- known Pydantic schema-shadow warnings during direct execution
```

None of these invalidate the pilot. They explain why the next move should be workflow/productization rather than more abstract architecture.

---

## The real next bottleneck

The bottleneck is **maintainer usability**, not the V66 model.

A maintainer should not have to inspect eight JSON files to answer:

```text
What changed?
What is stale?
Is anything trying to supersede Markdown?
Did generated reader text become source?
Are there prose-boundary warnings?
What do I need to do before merging?
```

The model already answers those questions internally. The output needs a human review layer.

---

## Strongest next move

The next move should be:

> **Build a maintainer-facing `anm-review` runner that emits both the existing machine artifacts and one compact Markdown review report.**

Not just a CLI, and not just a better reader projection. The right next step is a runner that combines both:

```text
1. runs V66-A / V66-B / V66-C over a selected repo cohort;
2. emits the existing JSON artifacts unchanged or near-unchanged;
3. emits a concise human review projection;
4. exits with clear status codes;
5. points maintainers to exact refresh / registration / transition-law actions.
```

Recommended command shape:

```bash
make anm-review
```

or:

```bash
python -m adeu_semantic_compiler.anm_review \
  --source-root . \
  --emit artifacts/anm/current \
  --review-md artifacts/anm/current/ANM_REVIEW.md
```

The generated human report should look roughly like:

```markdown
# ANM Review

Status: advisory-valid
Primary posture: needs_projection_refresh

## Required maintainer action

- Refresh generated reader projection:
  - source: docs/support/anm.adeu.md
  - projection: docs/generated/anm_reader/anm.reader.md
  - drift: source_changed_projection_stale

## Authority safety

- Markdown supersession: none
- Companion overlays: 1 registered, non-overriding
- Generated projections as source authority: none
- Semantic diff as authority: none
- Prose-to-policy inference: none

## Notices

- Normative-tone prose warning:
  - file: docs/support/anm.adeu.md
  - location: line/col needed
  - action: review whether this should remain prose or become an explicit block

## Full artifacts

- anm_source_set_manifest.json
- anm_doc_authority_profiles.json
- anm_doc_class_policy.json
- anm_migration_binding_profile.json
- anm_reader_projection_manifest.json
- anm_semantic_diff_report.json
- anm_prose_boundary_notice_set.json
- anm_compile_report.json
```

This would turn V66 from a closed implementation family into a practical maintainer workflow.

---

## Smaller follow-ups

### Add span-aware prose notices

Prose-boundary notice rows should include:

```text
source_span
matched_text_hash
short excerpt
authority block context
notice reason
recommended maintainer action
```

The current notice row is safe but not actionable enough.

### Add a semantic diff summary layer

Keep the 18-row JSON diff, but add a compressed summary:

```text
added source-set entries: 5
added profiles: 5
added class-policy rows: 5
registered migration bindings: 1
projection rows: 2
authority minted: no
supersession claimed: no
```

### Add secondary advisory items

Keep one primary posture, but expose secondary signals.

For this pilot:

```text
primary: needs_projection_refresh
secondary: normative-tone review warning
```

### Add excluded-inventory visibility

Show discovered-but-excluded generated docs in the human review report, with the reason they did not enter governed source.

### Clean up routine warnings

The known Pydantic `schema` shadow warnings should be suppressed or resolved before this becomes normal maintainer tooling. They do not break correctness, but they will erode trust in routine runs.

---

## Final recommendation

Treat the pilot as a **successful first real-usage validation**.

Do not reopen `V66`. Do not redesign the schemas first. Do not expand aggressively across the entire doc corpus yet.

The next implementation move should be:

```text
V66-D, if named at all:
  maintainer-facing ANM review runner + compact human review projection
```

with these acceptance criteria:

```text
- runs the shipped V66-A/B/C chain
- emits existing machine artifacts
- emits one concise Markdown review
- gives exact maintainer actions
- shows source/projection drift
- shows companion non-override posture
- shows excluded generated projections
- shows prose notices with file spans
- keeps all advisory output non-authoritative
- does not infer policy from prose
- does not supersede Markdown
```

The actual pilot shows the model is viable. The next question is no longer “does V66 work?” It is “can maintainers use V66 without reading eight JSON files?”
