# Two finite interfaces and their overlap

| Interface | Inputs it requires | What it supplies |
|---|---|---|
| `BlockSignCount` | Nonzero real polynomial, arbitrary finite family of disjoint open intervals, strict endpoint signs and a degree budget | Interior distinct roots, exact real-root multiset, exact degree and finite labeled-block counts |
| `RhCountingAudit` ordered prefixes | n+1 indexed entries and n common separators with strict local interleaving in any linear order | Inclusive prefix counts within one, including n = 0 |
| `RhCountingAudit` root helpers | Nonzero real polynomial, supplied injective witnesses or witnesses in monotone-boundary open cells, root equations and degree at most d | Exact real-root multiset, including d = 0 |

The degree-exhaustion step is shared classical Mathlib infrastructure. Retaining
the accepted companion file preserves both helpers without advertising them as
another root-finding mechanism. Its distinct interface is the finite ordered
prefix comparison, which needs no polynomial or analytic limit.

The arbitrary finite index type in `BlockSignCount` does not by itself provide
a natural-number ordering or shared separator sequence for the prefix theorems.
Conversely, interleaving arrays need not be roots of a polynomial. No compiled
bridge between these interfaces is included. A future application must establish
the exact indexing, order, root equations and common-cell hypotheses it uses.

The companion's open-cell inequalities prove injectivity. Merely placing
witnesses in closed cells would allow duplicates at a shared endpoint.
`prefixCount` counts indices; identifying it with a root-multiset threshold
count needs the witness/exhaustion dictionary, not a change in terminology.

Both sources have separate historical acceptance at the same pinned baseline.
Adding a second library/default target creates a new uncompiled project
configuration. This companion adds no fresh replay or current-upstream duplicate
or absence determination. No mathematical priority is claimed.
