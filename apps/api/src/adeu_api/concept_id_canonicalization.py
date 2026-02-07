from __future__ import annotations

from adeu_concepts import ConceptIR


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

    return ConceptIR.model_validate(payload)
