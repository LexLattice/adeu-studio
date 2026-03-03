from __future__ import annotations

import re
from types import MappingProxyType

REASON_CODE_PATTERN = r"^ASC-CIR-[0-9]{4}$"
_REASON_CODE_RE = re.compile(REASON_CODE_PATTERN)

ASC_CIR_0001_SCHEMA_INVALID = "ASC-CIR-0001"
ASC_CIR_0002_UNSUPPORTED_SCHEMA_VERSION = "ASC-CIR-0002"
ASC_CIR_0003_MODULE_ID_DUPLICATE = "ASC-CIR-0003"
ASC_CIR_0004_MODULE_KIND_INVALID = "ASC-CIR-0004"
ASC_CIR_0005_MODULE_PAYLOAD_INVALID = "ASC-CIR-0005"
ASC_CIR_0006_LOCK_CONTRACT_INVALID = "ASC-CIR-0006"
ASC_CIR_0007_SURFACE_CONTRACT_INVALID = "ASC-CIR-0007"
ASC_CIR_0008_ASSERTION_CONTRACT_INVALID = "ASC-CIR-0008"
ASC_CIR_0009_EVIDENCE_REQUIREMENT_INVALID = "ASC-CIR-0009"

_REASON_CODE_REGISTRY_RAW = {
    ASC_CIR_0001_SCHEMA_INVALID: "Commitments IR payload is schema-invalid.",
    ASC_CIR_0002_UNSUPPORTED_SCHEMA_VERSION: "Commitments IR schema version is unsupported.",
    ASC_CIR_0003_MODULE_ID_DUPLICATE: "Commitments IR module IDs must be unique.",
    ASC_CIR_0004_MODULE_KIND_INVALID: "Commitments IR module_kind is invalid.",
    ASC_CIR_0005_MODULE_PAYLOAD_INVALID: "Commitments IR module payload is invalid.",
    ASC_CIR_0006_LOCK_CONTRACT_INVALID: "Commitments IR lock contract is invalid.",
    ASC_CIR_0007_SURFACE_CONTRACT_INVALID: "Commitments IR surface declaration is invalid.",
    ASC_CIR_0008_ASSERTION_CONTRACT_INVALID: "Commitments IR assertion contract is invalid.",
    ASC_CIR_0009_EVIDENCE_REQUIREMENT_INVALID: "Commitments IR evidence requirement is invalid.",
}

REASON_CODE_REGISTRY = MappingProxyType(dict(sorted(_REASON_CODE_REGISTRY_RAW.items())))
REASON_CODES = tuple(REASON_CODE_REGISTRY.keys())


def validate_reason_code(value: str) -> str:
    if value not in REASON_CODE_REGISTRY:
        raise ValueError(f"unsupported commitments reason code: {value}")
    if _REASON_CODE_RE.match(value) is None:
        raise ValueError(f"commitments reason code has invalid format: {value}")
    return value


__all__ = [
    "REASON_CODE_PATTERN",
    "ASC_CIR_0001_SCHEMA_INVALID",
    "ASC_CIR_0002_UNSUPPORTED_SCHEMA_VERSION",
    "ASC_CIR_0003_MODULE_ID_DUPLICATE",
    "ASC_CIR_0004_MODULE_KIND_INVALID",
    "ASC_CIR_0005_MODULE_PAYLOAD_INVALID",
    "ASC_CIR_0006_LOCK_CONTRACT_INVALID",
    "ASC_CIR_0007_SURFACE_CONTRACT_INVALID",
    "ASC_CIR_0008_ASSERTION_CONTRACT_INVALID",
    "ASC_CIR_0009_EVIDENCE_REQUIREMENT_INVALID",
    "REASON_CODE_REGISTRY",
    "REASON_CODES",
    "validate_reason_code",
]
