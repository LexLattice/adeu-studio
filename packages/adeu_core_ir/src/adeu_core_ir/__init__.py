from .ids import stable_core_node_id
from .integrity_dangling_reference import (
    AdeuIntegrityDanglingReference,
    AdeuIntegrityDanglingReferenceIssue,
    AdeuIntegrityDanglingReferenceSummary,
    build_integrity_dangling_reference_diagnostics,
    canonicalize_integrity_dangling_reference_payload,
)
from .lane_report import (
    CANONICAL_LANE_ORDER,
    AdeuLaneReport,
    build_lane_report,
    canonicalize_lane_report_payload,
)
from .ledger import (
    LEDGER_VERSION_V0_1,
    apply_claim_ledger_scores,
    assert_claim_ledger_recompute_match,
)
from .models import (
    AdeuCoreIR,
    CoreDNode,
    CoreEdge,
    CoreENode,
    CoreONode,
    CoreUNode,
    canonical_edge_sort_key,
    canonical_node_sort_key,
    canonicalize_core_ir,
    canonicalize_core_ir_payload,
)
from .pipeline import (
    NormalizedCoreSourceText,
    build_core_ir_from_source_text,
    canonicalize_core_ir_candidates,
    harvest_core_ir_candidates,
    normalize_core_source_text,
)
from .projection_alignment import (
    AdeuProjectionAlignment,
    AdeuProjectionAlignmentIssue,
    AdeuProjectionAlignmentSummary,
    build_projection_alignment,
    canonicalize_projection_alignment_payload,
)

__all__ = [
    "AdeuCoreIR",
    "CoreDNode",
    "CoreENode",
    "CoreEdge",
    "CoreONode",
    "CoreUNode",
    "canonical_edge_sort_key",
    "canonical_node_sort_key",
    "canonicalize_core_ir",
    "canonicalize_core_ir_payload",
    "canonicalize_core_ir_candidates",
    "build_core_ir_from_source_text",
    "harvest_core_ir_candidates",
    "normalize_core_source_text",
    "NormalizedCoreSourceText",
    "LEDGER_VERSION_V0_1",
    "apply_claim_ledger_scores",
    "assert_claim_ledger_recompute_match",
    "stable_core_node_id",
    "AdeuIntegrityDanglingReference",
    "AdeuIntegrityDanglingReferenceIssue",
    "AdeuIntegrityDanglingReferenceSummary",
    "build_integrity_dangling_reference_diagnostics",
    "canonicalize_integrity_dangling_reference_payload",
    "AdeuLaneReport",
    "build_lane_report",
    "canonicalize_lane_report_payload",
    "CANONICAL_LANE_ORDER",
    "AdeuProjectionAlignment",
    "AdeuProjectionAlignmentIssue",
    "AdeuProjectionAlignmentSummary",
    "build_projection_alignment",
    "canonicalize_projection_alignment_payload",
]

__version__ = "0.0.0"
