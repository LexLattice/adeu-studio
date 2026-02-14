from .checker import ValidatorRunRecord, check, check_with_validator_runs
from .mode import KernelMode
from .patching import (
    PatchValidationError,
    apply_ambiguity_option,
    apply_ambiguity_option_patch,
    apply_json_patch,
)
from .proof import (
    DEFAULT_LEAN_TIMEOUT_MS,
    LeanCliProofBackend,
    MockProofBackend,
    ProofBackend,
    build_adeu_core_proof_requests,
    build_proof_backend,
    build_trivial_theorem_source,
)
from .proof_evidence import (
    PROOF_EVIDENCE_HASH_EXCLUDED_FIELD_LIST,
    PROOF_EVIDENCE_HASH_EXCLUDED_FIELDS,
    PROOF_EVIDENCE_SCHEMA,
    build_proof_evidence_packet,
    proof_evidence_hash,
    strip_nonsemantic_proof_fields,
)
from .semantics_diagnostics import (
    SEMANTICS_DIAGNOSTICS_SCHEMA,
    build_semantics_diagnostics,
    derive_semantics_assurance,
)
from .validator import (
    DEFAULT_Z3_TIMEOUT_MS,
    MockValidator,
    ValidatorBackend,
    Z3Validator,
    build_validator_backend,
)
from .validator_evidence import (
    VALIDATOR_EVIDENCE_HASH_EXCLUDED_FIELDS,
    VALIDATOR_EVIDENCE_PACKET_SCHEMA,
    build_validator_evidence_packet,
    strip_nonsemantic_validator_fields,
)

__all__ = [
    "KernelMode",
    "PatchValidationError",
    "DEFAULT_Z3_TIMEOUT_MS",
    "DEFAULT_LEAN_TIMEOUT_MS",
    "LeanCliProofBackend",
    "MockValidator",
    "MockProofBackend",
    "ProofBackend",
    "ValidatorBackend",
    "ValidatorRunRecord",
    "Z3Validator",
    "VALIDATOR_EVIDENCE_PACKET_SCHEMA",
    "PROOF_EVIDENCE_SCHEMA",
    "SEMANTICS_DIAGNOSTICS_SCHEMA",
    "derive_semantics_assurance",
    "VALIDATOR_EVIDENCE_HASH_EXCLUDED_FIELDS",
    "PROOF_EVIDENCE_HASH_EXCLUDED_FIELDS",
    "PROOF_EVIDENCE_HASH_EXCLUDED_FIELD_LIST",
    "strip_nonsemantic_validator_fields",
    "strip_nonsemantic_proof_fields",
    "apply_ambiguity_option",
    "apply_ambiguity_option_patch",
    "apply_json_patch",
    "build_adeu_core_proof_requests",
    "build_validator_backend",
    "build_semantics_diagnostics",
    "build_proof_backend",
    "build_proof_evidence_packet",
    "proof_evidence_hash",
    "build_validator_evidence_packet",
    "build_trivial_theorem_source",
    "check",
    "check_with_validator_runs",
]

__version__ = "0.0.0"
