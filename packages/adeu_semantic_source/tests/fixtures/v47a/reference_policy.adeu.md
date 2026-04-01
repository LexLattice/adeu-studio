# Reference ANM Policy

This prose is explanatory only.
It must not become compiled policy by implication.

:::D@1 id=artifact_governance
ON artifact.emitted[*]
NOTE "bounded V47-A reference chain"
@identity MUST REQUIRED snapshot.identity
@identity_explicit MUST EXPLICIT snapshot.identity
@carrier MUST EXACTLY_ONE primary_carrier_class
@no_override MUST_NOT lexical_naming.override_higher_precedence == true
@guarded MUST REQUIRED release.label ONLY_IF present(gate.enabled)
:::
