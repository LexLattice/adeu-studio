__all__ = [
    "PIPELINE_PROFILE_SCHEMA",
    "TASKPACK_PROFILE_REGISTRY_SCHEMA",
    "compile_taskpack",
    "verify_taskpack_bundle",
]


def __getattr__(name: str) -> object:
    if name in __all__:
        from . import compile as compile_module

        return getattr(compile_module, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
