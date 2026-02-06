from __future__ import annotations

from typing import Annotated, Literal, Union

from adeu_ir import ValidatorResult
from pydantic import BaseModel, ConfigDict, Field, model_validator

PuzzleSchemaVersion = Literal["adeu.puzzle.v0"]
PuzzleFamily = Literal["knights_knaves"]
PuzzleRole = Literal["knight", "knave", "unknown"]


class PuzzlePerson(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    name: str


class ExprIsRole(BaseModel):
    model_config = ConfigDict(extra="forbid")
    op: Literal["is_role"] = "is_role"
    person_id: str
    role: Literal["knight", "knave"]


class ExprNot(BaseModel):
    model_config = ConfigDict(extra="forbid")
    op: Literal["not"] = "not"
    arg: "PuzzleExpr"


class ExprAnd(BaseModel):
    model_config = ConfigDict(extra="forbid")
    op: Literal["and"] = "and"
    args: list["PuzzleExpr"] = Field(min_length=2)


class ExprOr(BaseModel):
    model_config = ConfigDict(extra="forbid")
    op: Literal["or"] = "or"
    args: list["PuzzleExpr"] = Field(min_length=2)


PuzzleExpr = Annotated[Union[ExprIsRole, ExprNot, ExprAnd, ExprOr], Field(discriminator="op")]


class PuzzleStatement(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    speaker_id: str
    text: str | None = None
    claim: PuzzleExpr


class PuzzleAssumption(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    text: str | None = None
    claim: PuzzleExpr


class KnightsKnavesPuzzle(BaseModel):
    model_config = ConfigDict(extra="forbid")
    schema_version: PuzzleSchemaVersion = "adeu.puzzle.v0"
    puzzle_id: str
    family: PuzzleFamily = "knights_knaves"
    people: list[PuzzlePerson] = Field(min_length=1)
    statements: list[PuzzleStatement] = Field(default_factory=list)
    assumptions: list[PuzzleAssumption] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_references(self) -> "KnightsKnavesPuzzle":
        person_ids = [person.id for person in self.people]
        if len(set(person_ids)) != len(person_ids):
            raise ValueError("people[].id must be unique")

        statement_ids = [statement.id for statement in self.statements]
        if len(set(statement_ids)) != len(statement_ids):
            raise ValueError("statements[].id must be unique")

        assumption_ids = [assumption.id for assumption in self.assumptions]
        if len(set(assumption_ids)) != len(assumption_ids):
            raise ValueError("assumptions[].id must be unique")

        known_people = set(person_ids)
        for statement in self.statements:
            if statement.speaker_id not in known_people:
                raise ValueError(
                    f"statement {statement.id!r} references unknown speaker_id "
                    f"{statement.speaker_id!r}"
                )
            _validate_expr_people(expr=statement.claim, known_people=known_people)

        for assumption in self.assumptions:
            _validate_expr_people(expr=assumption.claim, known_people=known_people)

        return self


class PuzzleAssignment(BaseModel):
    model_config = ConfigDict(extra="forbid")
    person_id: str
    role: PuzzleRole
    symbol: str


class PuzzleSolveResult(BaseModel):
    model_config = ConfigDict(extra="forbid")
    puzzle_id: str
    validator_result: ValidatorResult
    assignments: list[PuzzleAssignment] = Field(default_factory=list)


def _iter_expr_person_ids(expr: PuzzleExpr):
    if expr.op == "is_role":
        yield expr.person_id
        return
    if expr.op == "not":
        yield from _iter_expr_person_ids(expr.arg)
        return
    for nested in expr.args:
        yield from _iter_expr_person_ids(nested)


def _validate_expr_people(*, known_people: set[str], expr: PuzzleExpr) -> None:
    for person_id in _iter_expr_person_ids(expr):
        if person_id not in known_people:
            raise ValueError(f"expression references unknown person_id {person_id!r}")


ExprNot.model_rebuild()
ExprAnd.model_rebuild()
ExprOr.model_rebuild()
