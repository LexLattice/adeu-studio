__all__ = [
    "PIPELINE_PROFILE_SCHEMA",
    "TASKPACK_PROFILE_REGISTRY_SCHEMA",
    "ANM_TASKPACK_BINDING_PROFILE_SCHEMA",
    "COMPILED_POLICY_TASKPACK_BINDING_SCHEMA",
    "TASK_RUN_BOUNDARY_INSTANCE_SCHEMA",
    "WORKER_EXECUTION_ATTESTATION_SCHEMA",
    "WORKER_EXECUTION_PROVENANCE_SCHEMA",
    "WORKER_BOUNDARY_CONFORMANCE_REPORT_SCHEMA",
    "WORKER_DELEGATION_TOPOLOGY_SCHEMA",
    "AnmTaskpackBindingProfile",
    "CompiledPolicyTaskpackBinding",
    "TaskRunBoundaryInstance",
    "WorkerExecutionAttestation",
    "WorkerExecutionProvenance",
    "WorkerBoundaryConformanceReport",
    "WorkerDelegationTopology",
    "build_v48a_taskpack_binding_profile",
    "build_v48c_worker_execution_envelope",
    "build_v48d_worker_boundary_conformance_report",
    "build_v48e_worker_delegation_topology",
    "compile_v48b_taskpack_binding",
    "compile_taskpack",
    "verify_taskpack_bundle",
]


def __getattr__(name: str) -> object:
    if name in {
        "PIPELINE_PROFILE_SCHEMA",
        "TASKPACK_PROFILE_REGISTRY_SCHEMA",
        "compile_taskpack",
        "verify_taskpack_bundle",
    }:
        from . import compile as compile_module

        return getattr(compile_module, name)
    if name in {
        "ANM_TASKPACK_BINDING_PROFILE_SCHEMA",
        "AnmTaskpackBindingProfile",
        "build_v48a_taskpack_binding_profile",
    }:
        from . import taskpack_binding as binding_module

        return getattr(binding_module, name)
    if name in {
        "COMPILED_POLICY_TASKPACK_BINDING_SCHEMA",
        "CompiledPolicyTaskpackBinding",
        "compile_v48b_taskpack_binding",
    }:
        from . import compiled_taskpack_binding as compiled_binding_module

        return getattr(compiled_binding_module, name)
    if name in {
        "TASK_RUN_BOUNDARY_INSTANCE_SCHEMA",
        "WORKER_EXECUTION_ATTESTATION_SCHEMA",
        "WORKER_EXECUTION_PROVENANCE_SCHEMA",
        "TaskRunBoundaryInstance",
        "WorkerExecutionAttestation",
        "WorkerExecutionProvenance",
        "build_v48c_worker_execution_envelope",
    }:
        from . import worker_execution_envelope as worker_envelope_module

        return getattr(worker_envelope_module, name)
    if name in {
        "WORKER_BOUNDARY_CONFORMANCE_REPORT_SCHEMA",
        "WorkerBoundaryConformanceReport",
        "build_v48d_worker_boundary_conformance_report",
    }:
        from . import worker_boundary_conformance as worker_conformance_module

        return getattr(worker_conformance_module, name)
    if name in {
        "WORKER_DELEGATION_TOPOLOGY_SCHEMA",
        "WorkerDelegationTopology",
        "build_v48e_worker_delegation_topology",
    }:
        from . import worker_delegation_topology as worker_topology_module

        return getattr(worker_topology_module, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
