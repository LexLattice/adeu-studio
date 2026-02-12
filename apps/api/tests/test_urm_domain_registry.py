from __future__ import annotations

from dataclasses import dataclass
from typing import Any

import pytest
from urm_runtime.domain_registry import DomainToolRegistry
from urm_runtime.errors import URMError


@dataclass
class _FakePack:
    domain_pack_id: str
    domain_pack_version: str
    tools: list[str]

    def list_tools(self) -> list[str]:
        return list(self.tools)

    def supports_tool(self, *, tool_name: str) -> bool:
        return tool_name in self.tools

    def call_tool(self, *, tool_name: str, arguments: dict[str, Any]) -> tuple[Any, str]:
        if tool_name not in self.tools:
            raise URMError(
                code="URM_POLICY_DENIED",
                message="unsupported tool name",
                context={"tool_name": tool_name},
            )
        return ({"tool_name": tool_name, "arguments": arguments}, "observed")


def test_domain_registry_metadata_and_tool_listing_are_deterministic() -> None:
    pack_b = _FakePack(
        domain_pack_id="z_pack",
        domain_pack_version="1.0.0",
        tools=["tool.z", "tool.m"],
    )
    pack_a = _FakePack(
        domain_pack_id="a_pack",
        domain_pack_version="2.0.0",
        tools=["tool.b", "tool.a"],
    )

    registry = DomainToolRegistry.build(tool_packs=[pack_b, pack_a])

    packs = registry.list_pack_metadata()
    assert [(meta.domain_pack_id, meta.domain_pack_version) for meta in packs] == [
        ("a_pack", "2.0.0"),
        ("z_pack", "1.0.0"),
    ]
    assert [meta.tool_names for meta in packs] == [
        ("tool.a", "tool.b"),
        ("tool.m", "tool.z"),
    ]

    tools = registry.list_tool_metadata()
    assert [meta.tool_name for meta in tools] == [
        "tool.a",
        "tool.b",
        "tool.m",
        "tool.z",
    ]
    assert tools[0].domain_pack_id == "a_pack"
    assert tools[-1].domain_pack_id == "z_pack"

    result, warrant = registry.call_tool(tool_name="tool.m", arguments={"k": "v"})
    assert warrant == "observed"
    assert result == {"tool_name": "tool.m", "arguments": {"k": "v"}}


def test_domain_registry_rejects_duplicate_tool_name_across_packs() -> None:
    pack_a = _FakePack(
        domain_pack_id="a_pack",
        domain_pack_version="1.0.0",
        tools=["tool.shared"],
    )
    pack_b = _FakePack(
        domain_pack_id="b_pack",
        domain_pack_version="1.0.0",
        tools=["tool.shared"],
    )

    with pytest.raises(URMError) as exc_info:
        DomainToolRegistry.build(tool_packs=[pack_a, pack_b])

    assert exc_info.value.detail.code == "URM_POLICY_DENIED"
    assert exc_info.value.detail.context["tool_name"] == "tool.shared"


def test_domain_registry_rejects_duplicate_tool_name_inside_pack() -> None:
    duplicate_pack = _FakePack(
        domain_pack_id="dup_pack",
        domain_pack_version="1.0.0",
        tools=["tool.one", "tool.one"],
    )

    with pytest.raises(URMError) as exc_info:
        DomainToolRegistry.build(tool_packs=[duplicate_pack])

    assert exc_info.value.detail.code == "URM_POLICY_DENIED"
    assert exc_info.value.detail.context["domain_pack_id"] == "dup_pack"
