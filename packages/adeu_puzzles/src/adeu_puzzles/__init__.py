from .models import (
    KnightsKnavesPuzzle,
    PuzzleAssignment,
    PuzzleAssumption,
    PuzzleExpr,
    PuzzlePerson,
    PuzzleSolveResult,
    PuzzleStatement,
)
from .solver import build_knights_knaves_request, solve_knights_knaves

__all__ = [
    "KnightsKnavesPuzzle",
    "PuzzleAssignment",
    "PuzzleAssumption",
    "PuzzleExpr",
    "PuzzlePerson",
    "PuzzleSolveResult",
    "PuzzleStatement",
    "build_knights_knaves_request",
    "solve_knights_knaves",
]

__version__ = "0.0.0"
