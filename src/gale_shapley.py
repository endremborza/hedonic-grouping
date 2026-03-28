"""Gale-Shapley algorithm for the stable marriage problem.

Proposer-optimal stable matching for bipartite instances. Men propose in
preference order; women hold the best proposal and reject the rest.
Terminates in O(n^2) with a matching that is optimal for the proposing side.

This is the size-2 bipartite special case of the hedonic grouping algorithm.
Lemma 1 proves that the hedonic "considerable" condition reduces to GS's
"holds" relation on pairs.
"""

from .common import Agent


def gale_shapley(
    men_prefs: dict[Agent, list[Agent]],
    women_prefs: dict[Agent, list[Agent]],
) -> dict[Agent, Agent]:
    """Compute the men-proposing stable matching.

    Returns a dict mapping each agent (man or woman) to their partner.
    Always succeeds for complete bipartite preference lists.
    """
    women_rank: dict[Agent, dict[Agent, int]] = {
        w: {m: i for i, m in enumerate(wp)} for w, wp in women_prefs.items()
    }

    next_proposal = {m: 0 for m in men_prefs}
    woman_partner: dict[Agent, Agent | None] = {w: None for w in women_prefs}
    free = list(men_prefs)

    while free:
        m = free.pop()
        w = men_prefs[m][next_proposal[m]]
        next_proposal[m] += 1

        current = woman_partner[w]
        if current is None or women_rank[w][m] < women_rank[w][current]:
            woman_partner[w] = m
            if current is not None:
                free.append(current)
        else:
            free.append(m)

    matching: dict[Agent, Agent] = {}
    for w, m in woman_partner.items():
        assert m is not None
        matching[m] = w
        matching[w] = m
    return matching
