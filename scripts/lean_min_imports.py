#!/usr/bin/env python3
"""Run Mathlib's whole-file minImports linter without editing the source file."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

IMPORT_BLOCK = re.compile(r"\A((?:import [^\n]+\n)+)")
UNNEEDED_IMPORT = re.compile(r"unneeded import '([^']+)'")
MISSING_IMPORTS = re.compile(r"-- missing imports\n((?:import [^\n]+\n?)+)")


def instrument(source: str) -> str:
    match = IMPORT_BLOCK.match(source)
    if match is None:
        raise ValueError("Lean file has no leading import block")
    probe = "import Mathlib.Tactic.Linter.MinImports\n\n#import_bumps\n"
    return source[: match.end()] + probe + source[match.end() :]


def recommendations(output: str) -> tuple[set[str], set[str]]:
    unneeded = set(UNNEEDED_IMPORT.findall(output))
    blocks = MISSING_IMPORTS.findall(output)
    missing = {
        line.removeprefix("import ").strip()
        for line in (blocks[-1].splitlines() if blocks else [])
        if line.startswith("import ")
    }
    unneeded.discard("Mathlib.Tactic.Linter.MinImports")
    return unneeded, missing


def rewrite_imports(path: Path, source: str, unneeded: set[str], missing: set[str]) -> None:
    match = IMPORT_BLOCK.match(source)
    assert match is not None
    current = [line.removeprefix("import ") for line in match.group(1).splitlines()]
    retained = [module for module in current if module not in unneeded]
    modules = sorted(
        set(retained) | missing,
        key=lambda module: (module.startswith("LastLib"), module),
    )
    replacement = "".join(f"import {module}\n" for module in modules)
    path.write_text(replacement + source[match.end() :], encoding="utf-8")


def audit(path: Path, project: Path, *, fix: bool, quiet: bool) -> int:
    source = path.read_text(encoding="utf-8")
    try:
        probe = instrument(source)
    except ValueError as exc:
        print(f"{path}: {exc}", file=sys.stderr)
        return 2

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix=f"{path.stem}-min-imports-", encoding="utf-8"
    ) as handle:
        handle.write(probe)
        handle.flush()
        result = subprocess.run(
            ["lake", "env", "lean", handle.name],
            cwd=project,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )

    output = result.stdout.replace("import Mathlib.Tactic.Linter.MinImports\n", "")
    unneeded, missing = recommendations(output)
    if fix and result.returncode == 0:
        rewrite_imports(path, source, unneeded, missing)
        print(
            f"fixed {path}: removed {sorted(unneeded)!r}; added {sorted(missing)!r}",
            file=sys.stderr,
        )
    if not quiet:
        print(f"## {path}")
        print(output.rstrip())
    return result.returncode


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Audit Lean files with Mathlib's whole-file minImports linter"
    )
    parser.add_argument("files", nargs="+", type=Path)
    parser.add_argument(
        "--fix",
        action="store_true",
        help="replace the leading import block with the linter's recommendations",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="suppress compiler output (fix summaries are still printed)",
    )
    parser.add_argument(
        "--project",
        type=Path,
        default=Path("lean"),
        help="Lake project directory (default: lean)",
    )
    args = parser.parse_args()
    project = args.project.resolve()
    status = 0
    for raw_path in args.files:
        path = raw_path.resolve()
        status = max(status, audit(path, project, fix=args.fix, quiet=args.quiet))
    return status


if __name__ == "__main__":
    raise SystemExit(main())
