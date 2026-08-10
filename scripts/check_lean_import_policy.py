#!/usr/bin/env python3
"""Reject broad imports in production LastLib modules."""

from __future__ import annotations

import re
import sys
from pathlib import Path

FORBIDDEN_UMBRELLAS = {"Mathlib", "LastLib"}
BOOK_AGGREGATOR = re.compile(r"LastLib\.Book\d[^.]*$")
CHAPTER_AGGREGATOR = re.compile(
    r"LastLib\.Book02FiniteExtensionsOfLocalFields\.Chapter\d+$"
)


def is_leaf(path: Path) -> bool:
    return any(part.startswith("Chapter") and part[7:].isdigit() for part in path.parts[:-1])


def violations(path: Path) -> list[str]:
    if path.suffix != ".lean" or "LastLib" not in path.parts or not path.exists():
        return []
    found: list[str] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.startswith("import "):
            continue
        module = line.removeprefix("import ").strip()
        if module in FORBIDDEN_UMBRELLAS:
            found.append(f"{path}:{line_number}: forbidden umbrella import `{module}`")
        elif is_leaf(path) and (
            BOOK_AGGREGATOR.fullmatch(module) or CHAPTER_AGGREGATOR.fullmatch(module)
        ):
            found.append(
                f"{path}:{line_number}: leaf module imports aggregator `{module}`; "
                "import a focused API or section module"
            )
    return found


def main() -> int:
    errors = [error for name in sys.argv[1:] for error in violations(Path(name))]
    if errors:
        print("\n".join(errors), file=sys.stderr)
        print(
            "Add the focused Mathlib/LastLib modules used by the file; focused imports "
            "do not need to be minimized.",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
