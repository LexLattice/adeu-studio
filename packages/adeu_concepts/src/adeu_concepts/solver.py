from __future__ import annotations

import hashlib

from adeu_ir import ValidatorAtomRef, ValidatorOrigin, ValidatorPayload, ValidatorRequest

from .models import ConceptIR


def _sanitize_symbol(value: str) -> str:
    cleaned = "".join(ch if (ch.isalnum() or ch == "_") else "_" for ch in value).strip("_")
    if not cleaned:
        cleaned = "sense"
    if cleaned[0].isdigit():
        cleaned = f"s_{cleaned}"
    return cleaned


def _smt_quote_symbol(value: str) -> str:
    sanitized = value.replace("|", "_").replace("\\", "_")
    return f"|{sanitized}|"


def _assertion_name(*, object_id: str, json_path: str) -> str:
    path_hash = hashlib.sha256(json_path.encode("utf-8")).hexdigest()[:12]
    return f"a:{object_id}:{path_hash}"


def build_concept_coherence_request(concept: ConceptIR) -> ValidatorRequest:
    lines: list[str] = [
        "(set-logic QF_UF)",
        "(set-option :produce-models true)",
        "(set-option :produce-unsat-cores true)",
    ]
    atom_map: list[ValidatorAtomRef] = []
    origin: list[ValidatorOrigin] = []

    sense_symbol: dict[str, str] = {}
    for idx, sense in enumerate(concept.senses):
        symbol = f"s_{_sanitize_symbol(sense.id)}_{idx}"
        sense_symbol[sense.id] = symbol
        lines.append(f"(declare-fun {symbol} () Bool)")

    ambiguous_sense_ids: set[str] = set()
    for ambiguity in concept.ambiguity:
        ambiguous_sense_ids.update(ambiguity.options)

    for idx, sense in enumerate(concept.senses):
        if sense.id in ambiguous_sense_ids:
            continue
        object_id = sense.id
        json_path = f"/senses/{idx}"
        assertion_name = _assertion_name(object_id=object_id, json_path=json_path)
        symbol = sense_symbol[sense.id]
        lines.append(f"(assert (! {symbol} :named {_smt_quote_symbol(assertion_name)}))")
        atom_map.append(
            ValidatorAtomRef(
                assertion_name=assertion_name,
                object_id=object_id,
                json_path=json_path,
            )
        )
        origin.append(ValidatorOrigin(object_id=object_id, json_path=json_path))

    for idx, ambiguity in enumerate(concept.ambiguity):
        opts = [
            sense_symbol[sense_id] for sense_id in ambiguity.options if sense_id in sense_symbol
        ]
        if not opts:
            continue
        at_least_one_path = f"/ambiguity/{idx}/exactly_one"
        at_least_one_name = _assertion_name(object_id=ambiguity.id, json_path=at_least_one_path)
        lines.append(
            f"(assert (! (or {' '.join(opts)}) :named {_smt_quote_symbol(at_least_one_name)}))"
        )
        atom_map.append(
            ValidatorAtomRef(
                assertion_name=at_least_one_name,
                object_id=ambiguity.id,
                json_path=at_least_one_path,
            )
        )
        origin.append(ValidatorOrigin(object_id=ambiguity.id, json_path=at_least_one_path))

        for left in range(len(opts)):
            for right in range(left + 1, len(opts)):
                pair_path = f"/ambiguity/{idx}/exactly_one/{left}_{right}"
                pair_name = _assertion_name(object_id=ambiguity.id, json_path=pair_path)
                lines.append(
                    "(assert (! "
                    f"(or (not {opts[left]}) (not {opts[right]}))"
                    f" :named {_smt_quote_symbol(pair_name)}))"
                )
                atom_map.append(
                    ValidatorAtomRef(
                        assertion_name=pair_name,
                        object_id=ambiguity.id,
                        json_path=pair_path,
                    )
                )
                origin.append(ValidatorOrigin(object_id=ambiguity.id, json_path=pair_path))

    for idx, link in enumerate(concept.links):
        left = sense_symbol.get(link.src_sense_id)
        right = sense_symbol.get(link.dst_sense_id)
        if left is None or right is None:
            continue
        json_path = f"/links/{idx}"
        assertion_name = _assertion_name(object_id=link.id, json_path=json_path)
        if link.kind in {"commitment", "presupposition"}:
            expr = f"(=> {left} {right})"
        else:
            expr = f"(not (and {left} {right}))"
        lines.append(f"(assert (! {expr} :named {_smt_quote_symbol(assertion_name)}))")
        atom_map.append(
            ValidatorAtomRef(
                assertion_name=assertion_name,
                object_id=link.id,
                json_path=json_path,
            )
        )
        origin.append(ValidatorOrigin(object_id=link.id, json_path=json_path))

    payload = ValidatorPayload(
        formula_smt2="\n".join(lines) + "\n",
        atom_map=atom_map,
        metadata={
            "family": "concept_composition",
            "sense_symbols": sense_symbol,
            "assertion_name_format": "a:<object_id>:<json_path_hash>",
        },
    )
    return ValidatorRequest(
        kind="smt_check",
        logic="QF_UF",
        payload=payload,
        origin=origin,
    )
