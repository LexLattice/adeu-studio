from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Literal, Protocol

from .errors import URMError

WarrantTag = Literal["observed", "derived", "checked", "hypothesis", "unknown"]


class DomainToolPack(Protocol):
    domain_pack_id: str
    domain_pack_version: str

    def list_tools(self) -> list[str]: ...

    def supports_tool(self, *, tool_name: str) -> bool: ...

    def call_tool(self, *, tool_name: str, arguments: dict[str, Any]) -> tuple[Any, WarrantTag]: ...


@dataclass(frozen=True)
class DomainPackMetadata:
    domain_pack_id: str
    domain_pack_version: str
    tool_names: tuple[str, ...]


@dataclass(frozen=True)
class DomainToolMetadata:
    tool_name: str
    domain_pack_id: str
    domain_pack_version: str


@dataclass(frozen=True)
class DomainToolRegistry:
    tool_packs: tuple[DomainToolPack, ...]
    pack_index: tuple[DomainPackMetadata, ...]
    tool_index: tuple[DomainToolMetadata, ...]
    _tool_to_pack: dict[str, DomainToolPack] = field(repr=False)

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
        pack_index: list[DomainPackMetadata] = []
        tool_index: list[DomainToolMetadata] = []
        tool_to_pack: dict[str, DomainToolPack] = {}

        for pack in ordered:
            tool_names = tuple(sorted(pack.list_tools()))
            if len(set(tool_names)) != len(tool_names):
                seen: set[str] = set()
                duplicate_tools: set[str] = set()
                for tool_name in tool_names:
                    if tool_name in seen:
                        duplicate_tools.add(tool_name)
                    else:
                        seen.add(tool_name)
                raise URMError(
                    code="URM_POLICY_DENIED",
                    message="duplicate tool names inside domain pack",
                    context={
                        "domain_pack_id": pack.domain_pack_id,
                        "domain_pack_version": pack.domain_pack_version,
                        "duplicate_tools": sorted(duplicate_tools),
                    },
                )
            for tool_name in tool_names:
                if not pack.supports_tool(tool_name=tool_name):
                    raise URMError(
                        code="URM_POLICY_DENIED",
                        message="domain pack listed unsupported tool name",
                        context={
                            "tool_name": tool_name,
                            "domain_pack_id": pack.domain_pack_id,
                            "domain_pack_version": pack.domain_pack_version,
                        },
                    )
                existing = tool_to_pack.get(tool_name)
                if existing is not None:
                    raise URMError(
                        code="URM_POLICY_DENIED",
                        message="duplicate tool name across domain packs",
                        context={
                            "tool_name": tool_name,
                            "domain_pack_id": pack.domain_pack_id,
                            "domain_pack_version": pack.domain_pack_version,
                            "existing_domain_pack_id": existing.domain_pack_id,
                            "existing_domain_pack_version": existing.domain_pack_version,
                        },
                    )
                tool_to_pack[tool_name] = pack
                tool_index.append(
                    DomainToolMetadata(
                        tool_name=tool_name,
                        domain_pack_id=pack.domain_pack_id,
                        domain_pack_version=pack.domain_pack_version,
                    )
                )
            pack_index.append(
                DomainPackMetadata(
                    domain_pack_id=pack.domain_pack_id,
                    domain_pack_version=pack.domain_pack_version,
                    tool_names=tool_names,
                )
            )

        return cls(
            tool_packs=ordered,
            pack_index=tuple(pack_index),
            tool_index=tuple(sorted(tool_index, key=lambda item: item.tool_name)),
            _tool_to_pack=tool_to_pack,
        )

    def list_pack_metadata(self) -> list[DomainPackMetadata]:
        return list(self.pack_index)

    def list_tool_metadata(self) -> list[DomainToolMetadata]:
        return list(self.tool_index)

    def resolve_pack(self, *, tool_name: str) -> DomainToolPack:
        pack = self._tool_to_pack.get(tool_name)
        if pack is not None:
            return pack
        raise URMError(
            code="URM_POLICY_DENIED",
            message="unsupported tool name",
            context={"tool_name": tool_name},
        )

    def call_tool(self, *, tool_name: str, arguments: dict[str, Any]) -> tuple[Any, WarrantTag]:
        pack = self.resolve_pack(tool_name=tool_name)
        return pack.call_tool(tool_name=tool_name, arguments=arguments)
