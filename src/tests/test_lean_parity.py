"""Differential parity: the Lean HCF executable vs the Python oracle.

The Lean `hedonic-grouping` binary (built by `make build`) runs the same
formalized algorithm; on every instance it must agree with `src/hedonic.py`
on solvability and produce an identical, core-stable grouping. Skipped when
the binary is absent, so the pure-Python suite still runs without a Lean
build. Set `LEAN_PARITY_EXHAUSTIVE=1` for the full n=3 sweep.
"""

import json
import os
import subprocess
from pathlib import Path

import pytest

from ..common import Coalition, is_stable_hedonic
from ..generators import (
    HedonicProfile,
    profiles_hedonic,
    random_hedonic,
    random_rmp,
    rmp_to_hedonic,
)
from ..hedonic import solve

_EXE = Path(__file__).resolve().parents[2] / ".lake/build/bin/hedonic-grouping"

pytestmark = pytest.mark.skipif(
    not _EXE.exists(), reason="Lean executable not built (run `make build`)"
)


def _payload(prefs: HedonicProfile) -> dict:
    agents = list(prefs)
    return {"agents": agents, "prefs": {a: [list(c) for c in prefs[a]] for a in agents}}


def _run_lean(prefs: HedonicProfile) -> dict[str, Coalition] | None:
    out = subprocess.run(
        [str(_EXE)], input=json.dumps(_payload(prefs)), capture_output=True, text=True
    )
    assert out.returncode == 0, out.stderr
    parsed = json.loads(out.stdout)
    return None if parsed is None else {a: frozenset(v) for a, v in parsed.items()}


def _canon(sol: dict[str, Coalition] | None) -> dict | None:
    return None if sol is None else {a: sorted(c) for a, c in sol.items()}


def _assert_parity(prefs: HedonicProfile) -> None:
    py = solve(prefs)
    lean = _run_lean(prefs)
    assert (py is None) == (lean is None), prefs
    if lean is not None:
        assert is_stable_hedonic(prefs, lean), (prefs, _canon(lean))
        assert _canon(py) == _canon(lean), prefs


def test_parity_example5(hedonic_example5: HedonicProfile) -> None:
    _assert_parity(hedonic_example5)


@pytest.mark.parametrize("n,seed", [(n, s) for n in (3, 4, 5) for s in range(4)])
def test_parity_hedonic_random(n: int, seed: int) -> None:
    _assert_parity(random_hedonic(n, seed))


@pytest.mark.parametrize("n,seed", [(n, s) for n in (4, 5, 6) for s in range(4)])
def test_parity_roommates_embedding(n: int, seed: int) -> None:
    """Size-2 (stable-roommates) instances — the unification regime."""
    _assert_parity(rmp_to_hedonic(random_rmp(n, seed)))


@pytest.mark.skipif(
    not os.environ.get("LEAN_PARITY_EXHAUSTIVE"),
    reason="set LEAN_PARITY_EXHAUSTIVE=1 for the full n=3 sweep",
)
def test_parity_hedonic_exhaustive_n3() -> None:
    for prefs in profiles_hedonic(3):
        _assert_parity(prefs)
