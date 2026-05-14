"""Shared types and stability verifiers."""

from typing import TypeAlias

Agent: TypeAlias = str
Coalition: TypeAlias = frozenset[str]


def is_stable_marriage(
    men_prefs: dict[Agent, list[Agent]],
    women_prefs: dict[Agent, list[Agent]],
    matching: dict[Agent, Agent],
) -> bool:
    """Verify stability of a marriage matching: no blocking pair exists."""
    for m, m_pref in men_prefs.items():
        w_m = matching[m]
        for w in m_pref:
            if w == w_m:
                break
            m_w = matching[w]
            if women_prefs[w].index(m) < women_prefs[w].index(m_w):
                return False
    return True


def is_stable_roommates(
    prefs: dict[Agent, list[Agent]],
    matching: dict[Agent, Agent],
) -> bool:
    """Verify stability of a roommate matching: no blocking pair exists."""
    for a, a_pref in prefs.items():
        partner = matching[a]
        rank_partner = a_pref.index(partner)
        for b in a_pref[:rank_partner]:
            if a in prefs[b] and prefs[b].index(a) < prefs[b].index(matching[b]):
                return False
    return True


def is_stable_hedonic(
    prefs: dict[Agent, list[Coalition]],
    solution: dict[Agent, Coalition],
) -> bool:
    """Verify core stability: no blocking coalition exists."""
    for a, a_pref in prefs.items():
        assigned = solution[a]
        if assigned not in a_pref:
            return False
        rank = a_pref.index(assigned)
        for better in a_pref[:rank]:
            if all(
                better in prefs[b]
                and solution[b] in prefs[b]
                and prefs[b].index(better) < prefs[b].index(solution[b])
                for b in better
                if b != a
            ):
                return False
    return True
