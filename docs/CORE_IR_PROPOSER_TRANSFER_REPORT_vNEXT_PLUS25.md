# Core-IR Proposer Transfer Report vNext+25

Deterministic transfer summary generated from fixture-backed vNext+25 core-ir proposer request/response/packet artifacts.

```json
{
  "schema": "core_ir_proposer_transfer_report.vnext_plus25@1",
  "vnext_plus25_manifest_hash": "a4c9942930025425047d3de95b8f431446bdf3017bcd97d7ea8d4a6c54ac0d1f",
  "provider_matrix_hash": "f2b4b6d27c8587717ccddde07983e1287ae77a4db9b4ff7e9d65967dd2f3593c",
  "coverage_summary": {
    "coverage_pct": 100.0,
    "covered_surface_count": 1,
    "surface_count": 1,
    "surfaces": [
      {
        "fixture_count": 2,
        "fixture_ids": [
          "core_ir_proposer.contract.case_a",
          "core_ir_proposer.parity.case_a"
        ],
        "surface_id": "adeu_core_ir.propose"
      }
    ],
    "providers_covered": [
      "codex",
      "mock",
      "openai"
    ],
    "valid": true
  },
  "core_ir_proposer_contract_summary": {
    "core_ir_proposer_contract_fixture_count": 1,
    "core_ir_proposer_contract_run_count": 3,
    "artifact_core_ir_proposer_contract_valid_pct": 100.0,
    "providers": [
      "codex",
      "mock",
      "openai"
    ],
    "response_schema": "adeu_core_ir_proposer_response@0.1",
    "proposal_packet_schema": "adeu_core_ir_proposal@0.1",
    "summary_invariants": {
      "assertion_node_count": 11,
      "candidate_count": 0,
      "integrity_ref_count": 6,
      "lane_ref_count": 1,
      "logic_tree_max_depth": 1,
      "relation_edge_count": 10
    },
    "valid": true
  },
  "core_ir_proposer_parity_summary": {
    "core_ir_proposer_parity_fixture_count": 1,
    "core_ir_proposer_parity_run_count": 3,
    "artifact_core_ir_proposer_provider_parity_pct": 100.0,
    "parity_fingerprint_hashes_by_provider": {
      "codex": "9d6e9ee635fc26d29a0277a6204f5b8725f536ee860670a198ed25a5b739316f",
      "mock": "9d6e9ee635fc26d29a0277a6204f5b8725f536ee860670a198ed25a5b739316f",
      "openai": "9d6e9ee635fc26d29a0277a6204f5b8725f536ee860670a198ed25a5b739316f"
    },
    "parity_fingerprint_hash_match": true,
    "valid": true
  },
  "replay_summary": {
    "all_passed": true,
    "determinism_pct": {
      "artifact_core_ir_proposer_contract_valid_pct": 100.0,
      "artifact_core_ir_proposer_provider_parity_pct": 100.0
    },
    "fixture_counts": {
      "core_ir_proposer_contract_valid": 1,
      "core_ir_proposer_provider_parity": 1
    },
    "provider_run_counts": {
      "core_ir_proposer_contract_valid": 3,
      "core_ir_proposer_provider_parity": 3
    },
    "replay_count": 3,
    "runtime_observability": {
      "elapsed_ms": 48,
      "total_fixtures": 18,
      "total_replays": 66,
      "bytes_hashed_per_replay": 31930,
      "bytes_hashed_total": 95790
    },
    "valid": true
  }
}
```
