#!/usr/bin/env python3
"""Topologically concatenate a HedonicGrouping .lean file with all its
HedonicGrouping dependencies, for piping to AXLE (which only supports
`import Mathlib`).

Usage:
    python scripts/concat_imports.py HedonicGrouping/Correctness/GS_SMP.lean
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

IMPORT_RE = re.compile(r"^\s*import\s+(\S+)")
ROOT = Path("HedonicGrouping")


def module_to_path(module: str) -> Path:
    return Path(module.replace(".", "/") + ".lean")


def hedonic_imports(path: Path) -> list[Path]:
    out: list[Path] = []
    for line in path.read_text().splitlines():
        m = IMPORT_RE.match(line)
        if m and m.group(1).startswith("HedonicGrouping"):
            out.append(module_to_path(m.group(1)))
    return out


def visit(path: Path, visited: set[Path], order: list[Path]) -> None:
    if path in visited:
        return
    visited.add(path)
    for dep in hedonic_imports(path):
        visit(dep, visited, order)
    order.append(path)


def emit(path: Path) -> None:
    for line in path.read_text().splitlines():
        if IMPORT_RE.match(line):
            continue
        print(line)
    print()


def main() -> None:
    target = Path(sys.argv[1])
    order: list[Path] = []
    visit(target, set(), order)
    print("import Mathlib")
    print()
    for p in order:
        emit(p)


if __name__ == "__main__":
    main()
