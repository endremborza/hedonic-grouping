```markdown
# A Unifying Recursive Algorithm for Core-Stable Partitions in Generalized Matching

## Abstract
[cite_start]Simple algorithms matching two agents pairwise have had a wide range of applications, from assigning residents to hospitals to matching kidney donors[cite: 8, 9]. [cite_start]However, stability is traditionally difficult to achieve or guarantee in highly generalized grouping problems where agents have preferences over arbitrary subsets of the population[cite: 13, 14, 41]. [cite_start]This paper outlines a heavily generalized stable matching problem—modernly framed as a Hedonic Game—and provides a recursive algorithm to find a group-stable matching or prove none exists[cite: 4, 6]. Crucially, this algorithm acts as a unifying mechanism: by simply applying structural constraints on the preference profiles, it elegantly collapses to solve both the bipartite Stable Marriage Problem and the non-bipartite Stable Roommates Problem.

## 1. Introduction
Historically, stability in matching has been defined and solved within strict constraints. [cite_start]In the Stable Marriage problem, matching sets must have a cardinality of two, drawn from two distinct categories[cite: 56, 57]. [cite_start]In the Stable Roommates problem, the bipartite constraint is relaxed, but the cardinality constraint remains[cite: 83]. 

[cite_start]When these constraints are eliminated, an agent in a population of $p$ agents evaluates $2^{p}-1$ possible reconnections[cite: 14]. [cite_start]This introduces massive complexity, as an agent evaluates a total order on the powerset of the population excluding themselves[cite: 41].

**[TODO 1: Insert modern Literature Review here. Define this as a Hedonic Coalition Formation Game. Cite recent works on Core-Stability to replace the older "Group Stability" terminology.]**

## 2. Framework and Stability
[cite_start]In our generalized grouping problem, an $A$ set of agents needs to be organized into groups[cite: 39]. [cite_start]Each agent $\alpha_{i}$ has a preference profile $\Omega_{i}$, which is a total order on the powerset of $A$ without $\alpha_{i}$[cite: 40, 41]. 

We define stability as follows:
[cite_start]**Definition (Core/Group Stability):** A grouping is stable if there does not exist a set of agents who all prefer being in a group consisting only of themselves to their current assignment[cite: 93].

**[TODO 2: The "Reduction to Classical Matching" Section. Explicitly demonstrate mathematically how restricting $\Omega_{i}$ to bipartite size-2 sets mirrors Gale-Shapley, and restricting to complete graph size-2 sets mirrors Irving's algorithm.]**

## 3. The Algorithm
The generalized algorithm operates through a multi-phase process of reduction and recursion.

### 3.1 Simplified Reduction
[cite_start]Agents are only allowed to use a proposal to reject another proposal if it is "considerable"—meaning all other members in the proposed group also propose it[cite: 126, 127]. [cite_start]If an agent holds a considerable proposal for group $F$, no group can form in a stable grouping which is less desirable for that agent than $F$[cite: 148]. 

```python
# Simplified Reduction Algorithm 
while for some a in A no one holds the proposal of a do
  for a_i in A \ {agents someone holds a proposal for} do
    if M(a_i) != empty then
      H = the agent(s) a_i ranks highest from M(a_i)
      a_i proposes to agent(s) in H
      for a_j in H do
        a_j holds a_i's proposal
        if a_j is allowed to consider a_i's proposal then
          M gets reduced to matchings where groups a_j desires less than H cannot form
        else
          Halt

```

*[Adapted from Simplified Reduction: cite: 152]*

### 3.2 Recursion and "Moving On"

To resolve deadlocks (analogous to rings in the roommate problem), the algorithm forces an arbitrary agent to "move on" to their next available choice, systematically tracking these exceptions. If forcing an agent to move on results in all stable solutions being discarded, the algorithm recognizes this and restores the necessary path.

```python
# Recursive Grouping Function
Function grouping(A, M, Omega, J):
  all agents who most prefer to be in J move on
  
  while some a in A has a group left to propose to do
    while {agents someone holds a proposal for} != A do
      # ... [Simplified Reduction Logic applied here] ...
      
    for a_i in A do
      if a_i has a group left to propose to then
        K = a_i's 1st preference of the groups left to propose to
        if grouping(A, M, Omega, K) == 0 then
          M gets reduced to matchings where groups a_i desires less than K cannot form
        else
          M = grouping(A, M, Omega, K)
          break
          
  Return M

```

*[Adapted from Algorithm 4: cite: 228, 229]*

If the algorithm returns $M$, it is a stable solution. If it returns 0, no stable solution was available. Because the possibilities are finite, the recursive function is guaranteed to halt.

**[TODO 3: Formal Big-O Complexity Analysis. Define the worst-case runtime for the recursion tree and the reduction phase.]**

## 4. Conclusion

While the grouping problem is a strong generalization of previously discussed stable matching problems, it can still be solved in a similar fashion. The recursive algorithm successfully provides a stable solution if there is one, and signals if there isn't one.

**[TODO 4: Add future work regarding weak preferences and fractional/additively separable hedonic games.]**

```
