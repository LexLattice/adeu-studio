# Approval Flow Brief v77

Design a trust-sensitive approval flow for internal requests.

Constraints:

- the requester must never approve their own request;
- the approval decision must be policy-backed and auditable;
- required evidence must be visible before an authoritative decision is taken;
- high-impact ambiguity about auto-approval thresholds must fail closed.

Desired outcomes:

- lower standard-case turnaround time;
- preserve trust-boundary clarity;
- make auditability explicit.

Non-goals:

- no direct UI-to-authority minting;
- no automatic code generation from prose alone.
