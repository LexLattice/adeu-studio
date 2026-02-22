from __future__ import annotations

from contextlib import AbstractContextManager, ExitStack
from types import TracebackType
from typing import Any
from unittest.mock import patch

_PROVIDER_ENTRYPOINT_TARGETS: tuple[str, ...] = (
    "adeu_api.main.propose_concept_openai",
    "adeu_api.main.propose_concept_codex",
    "adeu_api.openai_provider.propose_openai",
    "adeu_api.openai_provider.propose_codex",
    "adeu_api.openai_concept_provider.propose_concept_openai",
    "adeu_api.openai_concept_provider.propose_concept_codex",
    "adeu_api.openai_puzzle_provider.propose_puzzle_openai",
    "adeu_api.openai_puzzle_provider.propose_puzzle_codex",
    "adeu_api.openai_backends.build_openai_backend",
    "adeu_api.openai_backends.build_codex_exec_backend",
    "adeu_api.mock_provider.load_fixture_bundles",
    "adeu_api.concept_mock_provider.get_concept_fixture_bundle",
    "adeu_api.puzzle_mock_provider.get_puzzle_fixture_bundle",
)

_OUTBOUND_NETWORK_TARGETS: tuple[str, ...] = (
    "socket.create_connection",
    "socket.socket.connect",
    "socket.socket.connect_ex",
)


def _raise_provider_entrypoint_call(*, target: str) -> Any:
    def _fail(*args: Any, **kwargs: Any) -> Any:
        raise AssertionError(
            f"NoProviderCallsGuard fail-closed: provider client entrypoint invoked: {target}"
        )

    return _fail


def _raise_outbound_network_call(*, target: str) -> Any:
    def _fail(*args: Any, **kwargs: Any) -> Any:
        raise AssertionError(
            f"NoProviderCallsGuard fail-closed: outbound network call denied: {target}"
        )

    return _fail


class NoProviderCallsGuard(AbstractContextManager["NoProviderCallsGuard"]):
    """Fail-closed guard for read-surface tests.

    The guard blocks known provider entrypoints and, when enabled, outbound socket-level calls.
    """

    def __init__(self, *, deny_outbound_network: bool = True) -> None:
        self._deny_outbound_network = deny_outbound_network
        self._stack: ExitStack | None = None

    def __enter__(self) -> NoProviderCallsGuard:
        stack = ExitStack()
        for target in _PROVIDER_ENTRYPOINT_TARGETS:
            stack.enter_context(patch(target, new=_raise_provider_entrypoint_call(target=target)))
        if self._deny_outbound_network:
            for target in _OUTBOUND_NETWORK_TARGETS:
                stack.enter_context(
                    patch(target, new=_raise_outbound_network_call(target=target))
                )
        self._stack = stack
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc: BaseException | None,
        tb: TracebackType | None,
    ) -> bool | None:
        if self._stack is None:
            return None
        return self._stack.__exit__(exc_type, exc, tb)
