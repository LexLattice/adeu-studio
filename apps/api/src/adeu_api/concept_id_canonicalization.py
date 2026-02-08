from __future__ import annotations

from adeu_concepts import ConceptIR


def _remap_patch_value(
    *,
    path: str,
    value: object,
    term_map: dict[str, str],
    sense_map: dict[str, str],
) -> object:
    if not isinstance(value, str):
        return value

    if path.endswith("/term_id"):
        return term_map.get(value, value)

    if (
        path.endswith("/sense_id")
        or path.endswith("/src_sense_id")
        or path.endswith("/dst_sense_id")
        or "/options/" in path
    ):
        return sense_map.get(value, value)

    return value


def _remap_patch_op_ids(
    *,
    patch_op: dict[str, object],
    term_map: dict[str, str],
    sense_map: dict[str, str],
) -> dict[str, object]:
    op = dict(patch_op)
    path = op.get("path")
    value = op.get("value")
    if isinstance(path, str):
        op["value"] = _remap_patch_value(
            path=path,
            value=value,
            term_map=term_map,
            sense_map=sense_map,
        )
    return op


def canonicalize_concept_ids(concept: ConceptIR) -> ConceptIR:
    payload = concept.model_dump(mode="json", exclude_none=True)

    terms = payload.get("terms", [])
    term_map: dict[str, str] = {}
    for idx, term in enumerate(terms):
        old_id = str(term.get("id") or "")
        new_id = f"term_{idx + 1}"
        term["id"] = new_id
        if old_id:
            term_map[old_id] = new_id

    senses = payload.get("senses", [])
    sense_map: dict[str, str] = {}
    for idx, sense in enumerate(senses):
        old_id = str(sense.get("id") or "")
        new_id = f"sense_{idx + 1}"
        sense["id"] = new_id
        term_id = sense.get("term_id")
        if isinstance(term_id, str):
            sense["term_id"] = term_map.get(term_id, term_id)
        if old_id:
            sense_map[old_id] = new_id

    claims = payload.get("claims", [])
    for idx, claim in enumerate(claims):
        claim["id"] = f"claim_{idx + 1}"
        sense_id = claim.get("sense_id")
        if isinstance(sense_id, str):
            claim["sense_id"] = sense_map.get(sense_id, sense_id)

    links = payload.get("links", [])
    for idx, link in enumerate(links):
        link["id"] = f"link_{idx + 1}"
        src = link.get("src_sense_id")
        dst = link.get("dst_sense_id")
        if isinstance(src, str):
            link["src_sense_id"] = sense_map.get(src, src)
        if isinstance(dst, str):
            link["dst_sense_id"] = sense_map.get(dst, dst)

    ambiguities = payload.get("ambiguity", [])
    for idx, ambiguity in enumerate(ambiguities):
        ambiguity["id"] = f"amb_{idx + 1}"
        term_id = ambiguity.get("term_id")
        if isinstance(term_id, str):
            ambiguity["term_id"] = term_map.get(term_id, term_id)
        options = ambiguity.get("options")
        if isinstance(options, list):
            ambiguity["options"] = [
                sense_map.get(item, item) if isinstance(item, str) else item for item in options
            ]
        option_labels = ambiguity.get("option_labels_by_id")
        if isinstance(option_labels, dict):
            remapped_labels: dict[str, str] = {}
            for option_id in sorted(option_labels.keys()):
                label = option_labels[option_id]
                if not isinstance(label, str):
                    continue
                remapped_labels[sense_map.get(option_id, option_id)] = label
            ambiguity["option_labels_by_id"] = remapped_labels

        option_details = ambiguity.get("option_details_by_id")
        if isinstance(option_details, dict):
            remapped_details: dict[str, dict[str, object]] = {}
            for option_id in sorted(option_details.keys()):
                detail = option_details[option_id]
                if not isinstance(detail, dict):
                    continue
                remapped_option_id = sense_map.get(option_id, option_id)
                detail_copy = dict(detail)
                detail_copy["option_id"] = remapped_option_id
                patch_ops = detail_copy.get("patch")
                if isinstance(patch_ops, list):
                    remapped_patch_ops = [
                        _remap_patch_op_ids(
                            patch_op=patch_op,
                            term_map=term_map,
                            sense_map=sense_map,
                        )
                        if isinstance(patch_op, dict)
                        else patch_op
                        for patch_op in patch_ops
                    ]
                    detail_copy["patch"] = remapped_patch_ops
                remapped_details[remapped_option_id] = detail_copy
            ambiguity["option_details_by_id"] = remapped_details

    return ConceptIR.model_validate(payload)
