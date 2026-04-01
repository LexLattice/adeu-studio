:::D@1 id=release_envelope
ON artifact.emitted[*]
@owner MUST REQUIRED metadata.owner
@owner_binding MUST bind_to(metadata.owner)
@owner_explicit MUST EXPLICIT metadata.owner
@runtime_guard MUST REQUIRED metadata.owner ONLY_IF present(runtime.enabled)
:::
