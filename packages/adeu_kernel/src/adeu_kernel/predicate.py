from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Union


class PredicateParseError(ValueError):
    pass


@dataclass(frozen=True)
class PredAnd:
    args: tuple["Predicate", ...]


@dataclass(frozen=True)
class PredOr:
    args: tuple["Predicate", ...]


@dataclass(frozen=True)
class PredNot:
    arg: "Predicate"


@dataclass(frozen=True)
class PredDefined:
    def_id: str


@dataclass(frozen=True)
class PredRefersToDoc:
    doc_ref: str


Predicate = Union[PredAnd, PredOr, PredNot, PredDefined, PredRefersToDoc]

_PREDICATE_NODE_TYPES = (PredAnd, PredOr, PredNot, PredDefined, PredRefersToDoc)


@dataclass(frozen=True)
class _Token:
    kind: Literal["LPAREN", "RPAREN", "SYMBOL", "STRING"]
    value: str
    pos: int


def _tokenize(source: str) -> list[_Token]:
    tokens: list[_Token] = []
    i = 0
    while i < len(source):
        ch = source[i]
        if ch.isspace():
            i += 1
            continue
        if ch == "(":
            tokens.append(_Token(kind="LPAREN", value="(", pos=i))
            i += 1
            continue
        if ch == ")":
            tokens.append(_Token(kind="RPAREN", value=")", pos=i))
            i += 1
            continue
        if ch == '"':
            start = i
            i += 1
            out: list[str] = []
            while i < len(source):
                ch = source[i]
                if ch == '"':
                    i += 1
                    tokens.append(_Token(kind="STRING", value="".join(out), pos=start))
                    break
                if ch == "\\":
                    i += 1
                    if i >= len(source):
                        raise PredicateParseError(f"unterminated escape at pos {i}")
                    esc = source[i]
                    if esc == '"' or esc == "\\":
                        out.append(esc)
                        i += 1
                        continue
                    if esc == "n":
                        out.append("\n")
                        i += 1
                        continue
                    raise PredicateParseError(f"unsupported escape '\\\\{esc}' at pos {i}")
                out.append(ch)
                i += 1
            else:
                raise PredicateParseError(f"unterminated string at pos {start}")
            continue

        start = i
        while i < len(source) and (not source[i].isspace()) and source[i] not in "()":
            i += 1
        tokens.append(_Token(kind="SYMBOL", value=source[start:i], pos=start))

    return tokens


def parse_predicate(source: str) -> Predicate:
    tokens = _tokenize(source)
    if not tokens:
        raise PredicateParseError("empty predicate")

    expr, idx = _parse_expr(tokens, 0)
    if idx != len(tokens):
        tok = tokens[idx]
        raise PredicateParseError(f"unexpected token {tok.value!r} at pos {tok.pos}")
    return expr


def _parse_expr(tokens: list[_Token], idx: int) -> tuple[Predicate, int]:
    if idx >= len(tokens):
        raise PredicateParseError("unexpected end of input")
    if tokens[idx].kind != "LPAREN":
        tok = tokens[idx]
        raise PredicateParseError(f"expected '(' at pos {tok.pos}")

    idx += 1
    if idx >= len(tokens) or tokens[idx].kind != "SYMBOL":
        pos = tokens[idx].pos if idx < len(tokens) else len(tokens)
        raise PredicateParseError(f"expected operator symbol at pos {pos}")

    head = tokens[idx].value
    head_pos = tokens[idx].pos
    idx += 1

    raw_args: list[object] = []
    while idx < len(tokens) and tokens[idx].kind != "RPAREN":
        if tokens[idx].kind == "LPAREN":
            child, idx = _parse_expr(tokens, idx)
            raw_args.append(child)
            continue
        raw_args.append(tokens[idx])
        idx += 1

    if idx >= len(tokens) or tokens[idx].kind != "RPAREN":
        raise PredicateParseError(f"expected ')' to close list opened at pos {head_pos}")
    idx += 1

    return _build_node(head, raw_args, head_pos), idx


def _build_node(head: str, raw_args: list[object], pos: int) -> Predicate:
    if head in ("and", "or"):
        if len(raw_args) < 2:
            raise PredicateParseError(f"{head} requires at least 2 args (pos {pos})")
        if not all(isinstance(a, _PREDICATE_NODE_TYPES) for a in raw_args):
            raise PredicateParseError(f"{head} args must be predicates (pos {pos})")
        args = tuple(raw_args)  # type: ignore[assignment]
        return PredAnd(args=args) if head == "and" else PredOr(args=args)

    if head == "not":
        if len(raw_args) != 1:
            raise PredicateParseError(f"not requires exactly 1 arg (pos {pos})")
        arg = raw_args[0]
        if not isinstance(arg, _PREDICATE_NODE_TYPES):
            raise PredicateParseError(f"not arg must be a predicate (pos {pos})")
        return PredNot(arg=arg)

    if head == "defined":
        if len(raw_args) != 1:
            raise PredicateParseError(f"defined requires exactly 1 arg (pos {pos})")
        tok = raw_args[0]
        if not isinstance(tok, _Token) or tok.kind != "SYMBOL":
            raise PredicateParseError(f"defined arg must be a symbol def_id (pos {pos})")
        if not tok.value.strip():
            raise PredicateParseError(f"defined def_id must be non-empty (pos {tok.pos})")
        return PredDefined(def_id=tok.value)

    if head == "refers_to_doc":
        if len(raw_args) != 1:
            raise PredicateParseError(f"refers_to_doc requires exactly 1 arg (pos {pos})")
        tok = raw_args[0]
        if not isinstance(tok, _Token) or tok.kind != "STRING":
            raise PredicateParseError(f"refers_to_doc arg must be a quoted string (pos {pos})")
        if not tok.value.strip():
            raise PredicateParseError(f"refers_to_doc doc_ref must be non-empty (pos {tok.pos})")
        return PredRefersToDoc(doc_ref=tok.value)

    raise PredicateParseError(f"unsupported operator {head!r} (pos {pos})")


def referenced_def_ids(predicate: Predicate) -> set[str]:
    out: set[str] = set()

    def walk(node: Predicate) -> None:
        if isinstance(node, PredDefined):
            out.add(node.def_id)
            return
        if isinstance(node, PredNot):
            walk(node.arg)
            return
        if isinstance(node, (PredAnd, PredOr)):
            for a in node.args:
                walk(a)
            return
        if isinstance(node, PredRefersToDoc):
            return
        raise AssertionError(f"unknown predicate node: {node!r}")

    walk(predicate)
    return out


def evaluate_predicate(
    predicate: Predicate,
    *,
    def_ids: set[str],
    doc_refs: set[str],
) -> bool | None:
    """
    Evaluates a predicate with IR-only semantics.

    Returns:
      - True/False when evaluatable
      - None when unevaluatable (e.g., unknown def_id references)
    """

    if isinstance(predicate, PredDefined):
        if predicate.def_id in def_ids:
            return True
        return None

    if isinstance(predicate, PredRefersToDoc):
        return predicate.doc_ref in doc_refs

    if isinstance(predicate, PredNot):
        inner = evaluate_predicate(predicate.arg, def_ids=def_ids, doc_refs=doc_refs)
        if inner is None:
            return None
        return not inner

    if isinstance(predicate, PredAnd):
        saw_none = False
        for arg in predicate.args:
            value = evaluate_predicate(arg, def_ids=def_ids, doc_refs=doc_refs)
            if value is False:
                return False
            if value is None:
                saw_none = True
        return None if saw_none else True

    if isinstance(predicate, PredOr):
        saw_none = False
        for arg in predicate.args:
            value = evaluate_predicate(arg, def_ids=def_ids, doc_refs=doc_refs)
            if value is True:
                return True
            if value is None:
                saw_none = True
        return None if saw_none else False

    raise AssertionError(f"unknown predicate node: {predicate!r}")
