"""Internal LLM-backed poem artifact utilities."""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from typing import Any, Literal, cast

from .openai_backends import (
    OpenAIBackend,
    build_codex_exec_backend,
    build_openai_backend,
)
from .openai_config import (
    codex_bin,
    codex_model,
    openai_api,
    openai_api_key,
    openai_base_url,
    openai_model,
    openai_temperature,
)

PoemForm = Literal["free", "haiku", "sonnet"]
PoemProvider = Literal["auto", "openai", "codex", "template"]


@dataclass(frozen=True)
class PoemArtifact:
    """Container for one generated poem."""

    title: str
    theme: str
    mood: str
    form: str
    seed: int | None
    lines: tuple[str, ...]
    devices: tuple[str, ...]
    source: str | None = None
    provider_request: str | None = None

    def to_text(self) -> str:
        body = "\n".join(self.lines)
        return f"{self.title}\n{body}" if self.title else body

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": "adeu.poem@1",
            "title": self.title,
            "theme": self.theme,
            "mood": self.mood,
            "form": self.form,
            "seed": self.seed,
            "lines": list(self.lines),
            "devices": list(self.devices),
            "line_count": len(self.lines),
            "source": self.source,
            "provider_request": self.provider_request,
        }


_MOOD_DIRECTIVES = {
    "wistful": [
        "ground the poem in gentle loss without sentimentality",
        "use reflective and precise imagery",
    ],
    "bright": [
        "keep tone luminous and affirmative",
        "favor concrete scenes and motion",
    ],
    "stormy": [
        "use energetic line breaks and compressed intensity",
        "let sound and rhythm drive the emotional pressure",
    ],
    "reverent": [
        "use ceremonial diction with restraint",
        "preserve humility and moral clarity",
    ],
}

_DEFAULT_DEVICES = (
    "metaphor",
    "imagery",
    "rhythmic cadence",
)

_FORM_LINE_GUIDES = {
    "free": "line_count varies by user input",
    "haiku": "3 lines with compact, reflective movement",
    "sonnet": "14 lines with a controlled volta around line 9",
}


def _normalize_prompt_text(value: str) -> str:
    return re.sub(r"\s+", " ", value).strip()


def _expected_line_count(form: PoemForm, line_count: int | None) -> int:
    if form == "haiku":
        return 3
    if form == "sonnet":
        return 14
    if line_count is None:
        raise ValueError("line_count is required for free-form poems")
    if line_count < 3:
        raise ValueError("line_count must be at least 3")
    return line_count


def _build_output_schema(expected_lines: int) -> dict[str, Any]:
    return {
        "type": "object",
        "properties": {
            "title": {
                "type": "string",
                "description": "short poem title",
            },
            "lines": {
                "type": "array",
                "items": {"type": "string"},
                "minItems": expected_lines,
                "maxItems": expected_lines,
            },
            "devices": {
                "type": "array",
                "items": {"type": "string"},
            },
            "notes": {
                "type": "string",
            },
        },
        "required": ["lines"],
        "additionalProperties": False,
    }


def _coerce_fallback_lines(
    raw_lines: list[str] | tuple[str, ...],
    expected_lines: int,
) -> list[str]:
    lines = [str(line).strip() for line in raw_lines if str(line).strip()]
    if len(lines) == expected_lines:
        return lines
    if len(lines) > expected_lines:
        return lines[:expected_lines]
    while len(lines) < expected_lines:
        if lines:
            lines.append(lines[-1])
        else:
            lines.append("")
    return lines


def _validate_output_lines(
    raw_lines: list[str] | tuple[str, ...],
    expected_lines: int,
) -> list[str]:
    lines = [str(line).strip() for line in raw_lines]
    if any(not line for line in lines):
        raise ValueError("`lines` entries must be non-empty strings")
    if len(lines) != expected_lines:
        raise ValueError(f"`lines` must contain exactly {expected_lines} entries")
    return lines


def _build_system_prompt() -> str:
    return _normalize_prompt_text(
        "You are an accomplished poet. "
        "Return ONLY valid JSON that matches the requested output schema."
    )


def _build_user_prompt(
    *,
    theme: str,
    mood: str,
    form: PoemForm,
    expected_lines: int,
    include_title: bool,
    include_devices: bool,
    seed: int | None,
) -> str:
    mood_lower = mood.lower().strip() or "wistful"
    mood_instructions = _MOOD_DIRECTIVES.get(mood_lower)
    if not mood_instructions:
        mood_instructions = [
            "keep language human, concrete, and image-driven",
            "avoid clichés and avoid over-explanation",
        ]

    title_request = (
        "Include a short title in `title`."
        if include_title
        else "Return an empty string for `title`."
    )
    device_request = (
        "Include `devices` as 3-5 short craft descriptors "
        "such as ['metaphor', ...]."
        if include_devices
        else "Return an empty `devices` array."
    )
    seed_clause = (
        f"Use this seed reference for stylistic consistency: {seed}."
        if seed is not None
        else "Use coherent internal variation; no external randomness constraints."
    )

    return _normalize_prompt_text(
        f"Theme: {theme}. Mood: {mood}. Form: {form}. "
        f"{_FORM_LINE_GUIDES[form]}. Exactly {expected_lines} lines are required. "
        "Each line should be a separate array entry in `lines`. "
        f"Use plain text only, no markdown, no numbering. {title_request} "
        f"{device_request} {seed_clause} "
        f"Form guidance: {'; '.join(mood_instructions)}."
    )


def _parse_llm_output(
    payload: dict[str, Any],
    *,
    expected_lines: int,
) -> tuple[str, list[str], tuple[str, ...]]:
    if not isinstance(payload, dict):
        raise ValueError("llm output must be a JSON object")

    raw_title = payload.get("title")
    title = "" if raw_title is None else str(raw_title)

    raw_lines = payload.get("lines")
    if isinstance(raw_lines, str):
        raw_lines = [line.strip() for line in raw_lines.splitlines() if line.strip()]
    if not isinstance(raw_lines, list):
        raise ValueError("`lines` must be a list of strings")

    lines = _validate_output_lines(
        tuple(str(item) for item in raw_lines),
        expected_lines=expected_lines,
    )
    raw_devices = payload.get("devices", [])
    if isinstance(raw_devices, str):
        devices = (str(raw_devices),)
    elif isinstance(raw_devices, list):
        devices = tuple(str(item) for item in raw_devices if str(item).strip())
    else:
        devices = ()
    if not devices and all(line.strip() for line in lines):
        devices = _DEFAULT_DEVICES

    return title, lines, devices


def _build_fallback_poem(*, theme: str, mood: str, form: PoemForm, line_count: int) -> PoemArtifact:
    fallback_lines = [
        f"{theme.title()}, spoken in the hush of {mood} thought.",
        "The room keeps its shape from memory and breath.",
        "I set one small sentence down in quiet light.",
        "The morning arrives with both mercy and warning.",
        "Nothing is fixed, and still we hold what we can.",
    ]
    if form == "sonnet":
        fallback_lines.extend(
            [
                "The line expands into one more season of care.",
                "The line breaks open where the older self returns.",
                "A question stays, and the answer keeps its promise.",
                "What end is this, if every end is also a door?",
                "Then we cross.",
            ]
        )
    if len(fallback_lines) < line_count:
        fallback_lines.extend(["..."] * (line_count - len(fallback_lines)))

    return PoemArtifact(
        title=f"{theme.title()} / {mood.title()}",
        theme=theme,
        mood=mood,
        form=form,
        seed=None,
        lines=tuple(_coerce_fallback_lines(fallback_lines, line_count)),
        devices=_DEFAULT_DEVICES,
        source="template",
        provider_request="fallback",
    )


def write_poem(
    *,
    theme: str = "memory",
    mood: str = "wistful",
    form: PoemForm = "free",
    line_count: int = 8,
    include_title: bool = True,
    seed: int | None = None,
    include_devices: bool = True,
    provider: PoemProvider = "auto",
    api: str | None = None,
    model: str | None = None,
    api_key: str | None = None,
    base_url: str | None = None,
    temperature: float | None = None,
    include_raw_output: bool = False,
    skip_git_repo_check: bool = False,
) -> PoemArtifact:
    """
    Build a poem using an LLM backend.

    provider:
    - auto: use OpenAI config (env defaults), fallback to template on miss
    - openai: force OpenAI backend
    - codex: use ADEU codex exec backend
    - template: deterministic fallback without LLM
    """
    expected_lines = _expected_line_count(form=form, line_count=line_count)
    normalized_mood = mood.lower().strip() or "wistful"

    if provider == "template":
        artifact = _build_fallback_poem(
            theme=theme,
            mood=normalized_mood,
            form=form,
            line_count=expected_lines,
        )
        return artifact

    schema = _build_output_schema(expected_lines=expected_lines)
    system_prompt = _build_system_prompt()
    user_prompt = _build_user_prompt(
        theme=theme,
        mood=normalized_mood,
        form=form,
        expected_lines=expected_lines,
        include_title=include_title,
        include_devices=include_devices,
        seed=seed,
    )

    backend: OpenAIBackend | None = None
    resolved_api: str | None = None
    resolved_model = model or (codex_model() if provider == "codex" else openai_model())
    resolved_key = api_key
    resolved_base_url = base_url
    if temperature is None and provider != "codex":
        temperature = openai_temperature()

    if provider == "openai" or provider == "auto":
        resolved_api = api or cast(str, openai_api())
        resolved_key = api_key or openai_api_key()
        resolved_base_url = base_url or openai_base_url()
        if not resolved_key:
            if provider == "openai":
                raise RuntimeError(
                    "OPENAI_API_KEY / ADEU_OPENAI_API_KEY must be set for provider='openai'"
                )
            return _build_fallback_poem(
                theme=theme,
                mood=normalized_mood,
                form=form,
                line_count=expected_lines,
            )
        backend = build_openai_backend(
            api=cast("str", resolved_api),
            api_key=resolved_key,
            base_url=resolved_base_url,
        )
    elif provider == "codex":
        backend = build_codex_exec_backend(
            codex_bin=codex_bin(),
            skip_git_repo_check=skip_git_repo_check,
        )
    else:
        raise ValueError("provider must be one of: auto, openai, codex, template")

    if backend is None:
        raise RuntimeError("Unable to build a poem generation backend")

    result = backend.generate_ir_json(
        system_prompt=system_prompt,
        user_prompt=user_prompt,
        json_schema=schema,
        model=resolved_model,
        temperature=temperature,
        extra=None,
    )
    if result.error is not None or result.parsed_json is None:
        if provider == "auto":
            return _build_fallback_poem(
                theme=theme,
                mood=normalized_mood,
                form=form,
                line_count=expected_lines,
            )
        raise RuntimeError(f"LLM poem generation failed: {result.error}")

    try:
        title, lines, devices = _parse_llm_output(
            result.parsed_json,
            expected_lines=expected_lines,
        )
    except ValueError as exc:
        if provider == "auto":
            return _build_fallback_poem(
                theme=theme,
                mood=normalized_mood,
                form=form,
                line_count=expected_lines,
            )
        raise RuntimeError(f"LLM poem output was malformed: {exc}") from exc

    return PoemArtifact(
        title=title if include_title else "",
        theme=theme,
        mood=normalized_mood,
        form=form,
        seed=seed,
        lines=tuple(lines),
        devices=devices if include_devices else (),
        source="llm",
        provider_request=json.dumps(
            {
                "api": result.provider_meta.api,
                "model": result.provider_meta.model,
            },
            sort_keys=True,
        )
        if include_raw_output
        else None,
    )


__all__ = ["PoemArtifact", "write_poem"]
