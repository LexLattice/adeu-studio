from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal, Protocol

from .errors import URMError

WarrantTag = Literal["observed", "derived", "checked", "hypothesis", "unknown"]


class DomainToolPack(Protocol):
    domain_pack_id: str
    domain_pack_version: str

    def supports_tool(self, *, tool_name: str) -> bool: ...

    def call_tool(self, *, tool_name: str, arguments: dict[str, Any]) -> tuple[Any, WarrantTag]: ...


@dataclass(frozen=True)
class DomainToolRegistry:
    tool_packs: tuple[DomainToolPack, ...]

    @classmethod
    def build(cls, *, tool_packs: list[DomainToolPack]) -> "DomainToolRegistry":
        ordered = tuple(
            sorted(
                tool_packs,
                key=lambda pack: (pack.domain_pack_id, pack.domain_pack_version),
            )
        )
        if not ordered:
            raise URMError(
                code="URM_POLICY_DENIED",
                message="no domain tool packs registered",
                context={},
            )
        return cls(tool_packs=ordered)

    def resolve_pack(self, *, tool_name: str) -> DomainToolPack:
        for pack in self.tool_packs:
            if pack.supports_tool(tool_name=tool_name):
                return pack
        raise URMError(
            code="URM_POLICY_DENIED",
            message="unsupported tool name",
            context={"tool_name": tool_name},
        )

    def call_tool(self, *, tool_name: str, arguments: dict[str, Any]) -> tuple[Any, WarrantTag]:
        pack = self.resolve_pack(tool_name=tool_name)
        return pack.call_tool(tool_name=tool_name, arguments=arguments)
