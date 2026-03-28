"""Irving's algorithm for the stable roommates problem.

Two-phase algorithm for finding a stable matching among n agents with
arbitrary (non-bipartite) preferences over partners:

  Phase 1 (Proposal round): Each agent proposes in preference order.
    Recipients hold the best proposal, reject others. Rejected agents
    remove the rejector and re-propose. Reduces preference lists while
    maintaining symmetry. O(n^2).

  Phase 2 (Rotation elimination): Detects cycles in the second-to-last
    chain of the reduced table and eliminates them until each agent has
    exactly one partner, or determines no stable matching exists.

Overall O(n^2). Returns None when no stable matching exists (possible
for non-bipartite instances; bipartite always has a solution).

This is the size-2 non-bipartite special case of the hedonic grouping
algorithm. Lemma 2 proves that the hedonic cascade produces the same
rotation eliminations as Irving's Phase 2.
"""

from .common import Agent


def irving(prefs: dict[Agent, list[Agent]]) -> dict[Agent, Agent] | None:
    """Find a stable roommate matching, or None if none exists."""
    agents = list(prefs)
    table = {a: list(p) for a, p in prefs.items()}

    if not _phase1(agents, table):
        return None
    return _phase2(agents, table)


def _phase1(agents: list[Agent], table: dict[Agent, list[Agent]]) -> bool:
    """Proposal round. Modifies table in-place. Returns False if no stable matching."""
    held_by: dict[Agent, Agent | None] = {a: None for a in agents}
    free = list(agents)

    while free:
        a = free.pop()
        while table[a]:
            b = table[a][0]
            current = held_by[b]
            if current is None:
                held_by[b] = a
                break
            if table[b].index(a) < table[b].index(current):
                held_by[b] = a
                table[current].remove(b)
                table[b].remove(current)
                free.append(current)
                break
            table[a].remove(b)
            table[b].remove(a)
        else:
            return False

    # Post-reduction: truncate each list after the held agent
    for b in agents:
        holder = held_by[b]
        if holder is not None and holder in table[b]:
            idx = table[b].index(holder)
            for c in table[b][idx + 1 :]:
                if b in table[c]:
                    table[c].remove(b)
            table[b] = table[b][: idx + 1]

    _cascade(agents, table)
    return True


def _cascade(agents: list[Agent], table: dict[Agent, list[Agent]]) -> None:
    """Propagate forced matches: when a list has length 1, ensure the partner's
    list also reduces to just this agent. Repeats until stable."""
    changed = True
    while changed:
        changed = False
        for a in agents:
            if len(table[a]) == 1:
                b = table[a][0]
                to_remove = [c for c in table[b] if c != a]
                if to_remove:
                    for c in to_remove:
                        table[b].remove(c)
                        if b in table[c]:
                            table[c].remove(b)
                    changed = True


def _find_rotation(
    agents: list[Agent], table: dict[Agent, list[Agent]]
) -> list[tuple[Agent, Agent]] | None:
    """Find a rotation in the reduced table, or None if all lists have length 1."""
    start = next((a for a in agents if len(table[a]) > 1), None)
    if start is None:
        return None

    chain: list[tuple[Agent, Agent]] = []
    p = start
    seen: dict[Agent, int] = {}
    while p not in seen:
        seen[p] = len(chain)
        q = table[p][1]
        chain.append((p, q))
        p = table[q][-1]

    return chain[seen[p] :]


def _eliminate_rotation(
    table: dict[Agent, list[Agent]], rotation: list[tuple[Agent, Agent]]
) -> None:
    """Eliminate a rotation: remove {q_i, p_{i+1 mod r}} pairs."""
    r = len(rotation)
    pairs = [(rotation[i][1], rotation[(i + 1) % r][0]) for i in range(r)]
    for q_i, p_next in pairs:
        if p_next in table[q_i]:
            table[q_i].remove(p_next)
        if q_i in table[p_next]:
            table[p_next].remove(q_i)


def _phase2(
    agents: list[Agent], table: dict[Agent, list[Agent]]
) -> dict[Agent, Agent] | None:
    """Rotation elimination phase. Returns stable matching or None."""
    while True:
        _cascade(agents, table)
        if any(len(table[a]) == 0 for a in agents):
            return None
        rotation = _find_rotation(agents, table)
        if rotation is None:
            return {a: table[a][0] for a in agents}
        _eliminate_rotation(table, rotation)
