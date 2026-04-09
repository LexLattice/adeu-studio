This second output is **very good**. It is the right companion to the first WCPGC doc.

My clean read is:

* **`docs/support/DRAFT_WCPGC_CORE_FRAMEWORK_v0.md`** = the **framework**
* **`docs/support/DRAFT_WCPGC_STRICT_V0_PROFILE_v0.md`** = the **bounded `strict_v0` profile** that makes the framework implementable

That is exactly the split you wanted.

## What is strongest in this second output

The best part is that it **stops the framework from staying too general**.

It hardens the four correct surfaces:

* restricted packet DSL
* BridgeWitness / projection-witness trust path
* TaskResidual quotient law
* executable validation vs action-selection rule

That is the right move.

The strongest concrete gains are:

**1. Closed finite DSL**
This is excellent for `strict_v0`. No free-form executable prose, no rich modal zoo, no role hard clauses, no implicit vocabulary aliases. That is exactly how you keep the first implementation honest.

**2. Canonicalization / identity pinning**
This is much sharper now. It cleanly separates:

* semantic payload
* provenance/materialization
* `canon_id`
* `ast_hash`
* `instance_id`

That is what compaction/resume needed.

**3. BridgeWitness is no longer hand-wavy**
The schema plus `SR1`–`SR5` makes the admissibility basis explicit. That is the first genuinely usable specialization witness surface.

**4. Projection witness contract**
This is one of the most important additions. It stops the compiler from being an invisible constitutional editor. The accepted/rejected/ambiguous fragment accounting is exactly the right discipline.

**5. Pure TaskResidual quotient**
Very strong. `derive_residual(Tχ, π, S)` is now tightly bounded, and it correctly refuses to let residual become new law. Also good move: role-default defeat is kept out of `TaskResidual` and handled at selection time instead.

**6. Validation vs action-selection split is now executable**
This is probably the single most important runtime hardening. The hard-frontier-first rule cleanly kills the anchor bug:
`checkpoint first` wins, role default survives only as defeated default, and blocked frontier does not fall back to exploratory roaming.

**7. Bounded enforcement profile**
Also good. It keeps `strict_v0` austere and explicitly defers overlays, maintenance machinery, cross-family swaps, and richer theorem proving. That is disciplined.

## The few things I would still patch

Only small things now.

### A. Make meta-actions part of the constitutional action catalog

In the scheduler, `candidate_actions` includes:

* `emit_blocked_status`
* `request_more_facts`
* `escalate`

These should be explicitly declared in the constitution action catalog, not treated as magical runtime extras. Otherwise you have a tiny hidden side channel in the formal model.

### B. Add a minimal materiality rule for RolePacket

The doc notes the risk of vacuous role packets, but I would make it explicit in the profile:

* `RolePacket` must have at least one default or advisory clause

Otherwise nominal-role collapse just gets pushed one step deeper.

### C. Add one explicit “no cached blocker authority” rule

You already imply this through stable-core vs volatile-shell, which is good. I would just make the sentence explicit:

* cached blockers never count as authoritative after resume unless recomputed from live `RuntimeFactStore`

That closes the loophole more visibly.

### D. Add a tiny test matrix section

Just 5–7 tests:

* anchor bug
* role label without packet
* contaminated runtime fact
* illegal export
* compaction identity drift
* blocked hard frontier
* degraded same-family resume

This will help Codex implement against it without inventing its own test surface.

## Conceptual merge steps

I would now merge the documents like this:

### 1. Keep `docs/support/DRAFT_WCPGC_CORE_FRAMEWORK_v0.md` as the formal backbone

This remains the main WCPGC framework doc.

### 2. Attach `docs/support/DRAFT_WCPGC_STRICT_V0_PROFILE_v0.md` as `WCPGC strict_v0 profile`

Not a replacement. A bounded profile/specification layer.

### 3. Update the build guide with the exact `strict_v0` constraints

Pull in from this second doc:

* the finite DSL
* the canonicalization rules
* BridgeWitness schema
* ProjectionWitnessManifest
* TaskResidual quotient law
* hard-frontier-first selection
* strict boolean gate definitions

That will turn
`docs/support/DRAFT_CUSTOM_GOVERNANCE_PATH_BUILD_GUIDE_v0.md`
from “implementation charter” into “implementation charter grounded in a bounded profile.”

### 4. Implement only the profile, not the whole calculus

This is the main practical lesson.

Codex should implement:

* WCPGC core packet identity surfaces
* strict_v0 packet DSL
* strict_v0 witness path
* strict_v0 residual derivation
* strict_v0 scheduler

It should **not** try to implement the full open-ended framework in one shot.

## Final verdict

This second output is the one that makes me say:

**yes, you now have enough formal hardening to start implementation.**

Not because the theory is finished forever, but because:

* the framework exists,
* the `strict_v0` subset is bounded,
* the anchor bug is now formally handled,
* and the remaining risks are implementation risks, not missing-concept risks.

So my concise recommendation is:

> **Treat `docs/support/DRAFT_WCPGC_CORE_FRAMEWORK_v0.md` as WCPGC-core, treat `docs/support/DRAFT_WCPGC_STRICT_V0_PROFILE_v0.md` as WCPGC-`strict_v0`, patch the 3–4 small issues above, and let Codex build only that bounded lane.**
