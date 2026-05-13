"""Iterative HCF — same semantics as `hedonic.py`, explicit stack.

The recursive form in `hedonic.py` calls itself on `deepcopy(problem)` whenever
Phase 1 quiesces without a stable solution. Each recursive call adds one
coalition to `forced_moves`. This module replaces the call stack with an
explicit `list[_Frame]`, which is the shape the Lean port will follow:
recursion needs well-founded-recursion proofs; an explicit stack collapses to
a single iterated step over a measurable state.

Termination measure (the same as the recursive version, made explicit here):
`(|forced_moves|, Σ_a |preferences[a]|)` decreases lexicographically across
the stack — `_eliminate` strictly shrinks the second component and pushing a
child strictly grows the first.

`solve` is observationally equivalent to `hedonic.solve` on every input; the
test harness cross-checks this on the Monte-Carlo suite.
"""

from copy import deepcopy
from dataclasses import dataclass, field
from enum import Enum
from functools import reduce

from .common import Agent, Coalition, is_stable_hedonic


class _Stage(Enum):
    INIT = 0
    PHASE1 = 1
    AWAITING_CHILD = 2


@dataclass
class _Proposal:
    coalition: Coalition
    proposers: set[Agent]


@dataclass
class _Problem:
    agents: list[Agent]
    preferences: dict[Agent, list[Coalition]]
    out_proposals: dict[Agent, list[Coalition]] = field(default_factory=dict)
    in_proposals: dict[Agent, list[_Proposal]] = field(default_factory=dict)
    forced_moves: set[Coalition] = field(default_factory=set)

    @staticmethod
    def create(agents: list[Agent], prefs: dict[Agent, list[Coalition]]) -> "_Problem":
        return _Problem(
            agents=agents,
            preferences=deepcopy(prefs),
            out_proposals={a: [] for a in agents},
            in_proposals={a: [] for a in agents},
        )

    def solution(self) -> dict[Agent, Coalition] | None:
        result: dict[Agent, Coalition] = {}
        for a in self.agents:
            if not self.out_proposals[a]:
                return None
            result[a] = self.out_proposals[a][-1]
        for a, g in result.items():
            for member in g:
                if result.get(member) != g:
                    return None
        return result

    def has_valid_proposal(self, a: Agent) -> bool:
        return any(g not in self.forced_moves for g in self.out_proposals[a])

    def top_unproposed(self, a: Agent) -> Coalition | None:
        for g in self.preferences[a]:
            if g not in self.out_proposals[a]:
                return g
        return None

    def remaining_prefs(self, a: Agent) -> list[Coalition]:
        return [g for g in self.preferences[a] if g not in self.out_proposals[a]]


@dataclass
class _Frame:
    problem: _Problem
    exception: Coalition
    stage: _Stage = _Stage.INIT
    pending_remaining: list[Coalition] = field(default_factory=list)


def solve(prefs: dict[Agent, list[Coalition]]) -> dict[Agent, Coalition] | None:
    agents = list(prefs)
    initial = _Problem.create(agents, prefs)
    stack: list[_Frame] = [_Frame(problem=initial, exception=frozenset())]
    last: _Problem | None = None

    while stack:
        frame = stack[-1]

        if frame.stage is _Stage.INIT:
            frame.problem.forced_moves.add(frame.exception)
            frame.stage = _Stage.PHASE1

        if frame.stage is _Stage.PHASE1:
            if not _phase1(frame.problem):
                stack.pop()
                last = None
                continue

            sol = frame.problem.solution()
            if sol is not None and is_stable_hedonic(prefs, sol):
                for a in frame.problem.agents:
                    frame.problem.preferences[a] = [sol[a]]
                stack.pop()
                last = frame.problem
                continue

            pivot: Agent | None = None
            for a in frame.problem.agents:
                if frame.problem.remaining_prefs(a):
                    pivot = a
                    break

            if pivot is None:
                stack.pop()
                last = frame.problem
                continue

            frame.pending_remaining = frame.problem.remaining_prefs(pivot)
            k = frame.problem.out_proposals[pivot][-1]
            stack.append(_Frame(problem=deepcopy(frame.problem), exception=k))
            frame.stage = _Stage.AWAITING_CHILD
            continue

        if frame.stage is _Stage.AWAITING_CHILD:
            if last is None:
                _eliminate(frame.problem, frame.pending_remaining)
                frame.stage = _Stage.PHASE1
                continue
            stack.pop()

    return last.solution() if last is not None else None


def _eliminate(problem: _Problem, coalitions: list[Coalition]) -> None:
    removal = set(coalitions)
    if not removal:
        return
    affected: frozenset[Agent] = reduce(frozenset.union, removal)
    for a in affected:
        problem.preferences[a] = [g for g in problem.preferences[a] if g not in removal]
        problem.out_proposals[a] = [
            g for g in problem.out_proposals[a] if g not in removal
        ]
        problem.in_proposals[a] = [
            p for p in problem.in_proposals[a] if p.coalition not in removal
        ]


def _receive_proposal(
    problem: _Problem, receiver: Agent, coalition: Coalition, proposer: Agent
) -> None:
    existing = next(
        (p for p in problem.in_proposals[receiver] if p.coalition == coalition), None
    )
    if existing is None:
        existing = _Proposal(coalition=coalition, proposers={proposer})
        problem.in_proposals[receiver].append(existing)
    else:
        existing.proposers.add(proposer)

    if (
        len(existing.proposers) >= len(coalition) - 1
        and coalition in problem.preferences[receiver]
    ):
        rank = problem.preferences[receiver].index(coalition)
        for p in problem.in_proposals[receiver]:
            if p.coalition == coalition:
                continue
            if (
                len(p.proposers) >= len(p.coalition) - 1
                and p.coalition in problem.preferences[receiver]
                and problem.preferences[receiver].index(p.coalition) < rank
            ):
                _eliminate(problem, [coalition])
                return

        worse = problem.preferences[receiver][rank + 1 :]
        if worse:
            _eliminate(problem, worse)


def _phase1(problem: _Problem) -> bool:
    """Run proposal-rejection to quiescence. Returns False iff exhausted."""
    progress = True
    while progress:
        progress = False
        for a in problem.agents:
            if problem.has_valid_proposal(a):
                continue
            progress = True
            top = problem.top_unproposed(a)
            if top is None:
                return False
            problem.out_proposals[a].append(top)
            for b in top - {a}:
                _receive_proposal(problem, b, top, a)
    return True
