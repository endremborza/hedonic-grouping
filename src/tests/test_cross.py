"""Cross-algorithm tests: SMP/RMP embed into HCP via size-2 coalitions."""

from itertools import combinations

import pytest

from ..common import (
    Coalition,
    is_stable_hedonic,
    is_stable_marriage,
    is_stable_roommates,
)
from ..gale_shapley import gale_shapley
from ..generators import (
    HedonicProfile,
    profiles_rmp,
    random_rmp,
    random_smp,
    smp_agents,
)
from ..hedonic import solve as hedonic_solve
from ..irving import irving


def _smp_to_hedonic(
    mp: dict[str, list[str]], wp: dict[str, list[str]]
) -> HedonicProfile:
    out: HedonicProfile = {}
    for m, pref in mp.items():
        out[m] = [frozenset({m, w}) for w in pref]
    for w, pref in wp.items():
        out[w] = [frozenset({w, m}) for m in pref]
    return out


def _rmp_to_hedonic(prefs: dict[str, list[str]]) -> HedonicProfile:
    return {a: [frozenset({a, b}) for b in p] for a, p in prefs.items()}


@pytest.mark.parametrize("n,seed", [(n, s) for n in (3, 4) for s in range(30)])
def test_marriage_to_hedonic(n: int, seed: int) -> None:
    """GS and hedonic both produce stable marriages (possibly different ones)."""
    mp, wp = random_smp(n, seed)
    gs_match = gale_shapley(mp, wp)
    assert is_stable_marriage(mp, wp, gs_match)

    h_prefs = _smp_to_hedonic(mp, wp)
    h_sol = hedonic_solve(h_prefs)
    assert h_sol is not None
    assert is_stable_hedonic(h_prefs, h_sol)

    men, women = smp_agents(n)
    h_match = {a: next(iter(coal - {a})) for a, coal in h_sol.items()}
    assert is_stable_marriage(mp, wp, h_match)
    assert set(h_match) == set(men) | set(women)


@pytest.mark.parametrize("n", [4])
def test_roommates_to_hedonic_exhaustive(n: int) -> None:
    """Irving and hedonic agree on solvability for every n=4 RMP instance."""
    for prefs in profiles_rmp(n):
        irv = irving(prefs)
        h_sol = hedonic_solve(_rmp_to_hedonic(prefs))
        assert (irv is None) == (h_sol is None), prefs
        if irv is not None:
            assert is_stable_roommates(prefs, irv)
            assert h_sol is not None
            h_match = {a: next(iter(h_sol[a] - {a})) for a in prefs}
            assert is_stable_roommates(prefs, h_match), (prefs, h_match)


@pytest.mark.parametrize("n,seed", [(n, s) for n in (5, 6) for s in range(30)])
def test_roommates_to_hedonic_random(n: int, seed: int) -> None:
    prefs = random_rmp(n, seed)
    irv = irving(prefs)
    h_sol = hedonic_solve(_rmp_to_hedonic(prefs))
    assert (irv is None) == (h_sol is None)
    if irv is not None:
        assert is_stable_roommates(prefs, irv)
        assert h_sol is not None
        h_match = {a: next(iter(h_sol[a] - {a})) for a in prefs}
        assert is_stable_roommates(prefs, h_match)


def test_college_admissions() -> None:
    """Many-to-one CAP embedded in HCP via responsive preferences.

    Each student-college coalition includes the college, the student, and any
    classmates allowed by the quota. Generates sum_k C(n,k) coalitions per
    college; only viable for tiny instances.
    """
    colleges = {"C1": 2, "C2": 1}
    students = ["S1", "S2", "S3"]

    s_prefs = {
        "S1": ["C1", "C2"],
        "S2": ["C2", "C1"],
        "S3": ["C1", "C2"],
    }
    c_prefs = {
        "C1": ["S1", "S2", "S3"],
        "C2": ["S1", "S2", "S3"],
    }

    h_prefs: HedonicProfile = {}
    for s, pref in s_prefs.items():
        entries: list[Coalition] = []
        for c in pref:
            others = [o for o in students if o != s]
            for r in range(colleges[c]):
                for combo in combinations(others, r):
                    entries.append(frozenset({s, c, *combo}))
        h_prefs[s] = entries
    for c, pref in c_prefs.items():
        entries = []
        for r in range(colleges[c], 0, -1):
            for combo in combinations(pref, r):
                entries.append(frozenset({c, *combo}))
        h_prefs[c] = entries

    sol = hedonic_solve(h_prefs)
    assert sol is not None
    assert is_stable_hedonic(h_prefs, sol)
