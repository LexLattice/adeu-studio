# adeu_semantic_forms_v0

Minimal prototype for a bounded ADEU-native semantic language layer over the `repo_policy_work` domain.

This prototype demonstrates:

- a profile-relative semantic parse profile over released V45 / V47 / V48-adjacent anchors;
- `natural_language -> adeu_semantic_normal_form@1` recovery with typed ambiguity and unsupported rejection;
- deterministic canonical hashing only after semantic normalization;
- deterministic `adeu_semantic_normal_form@1 -> adeu_taskpack_binding_spec_seed@1` transformation.

The prototype is intentionally narrow and only supports:

- one starter domain: policy-bound repo work intent;
- read-only mutation posture;
- scope/policy/worker binding plus allow-path and forbid-effect constraints;
- released anchor resolution through a fixed parse profile.
