# Ordered prefixes and complete root witnesses

The interleaving interface separates finite order bookkeeping from polynomial root construction. Its counting results work in any linearly ordered type. They use only the displayed finite prefixes of indexed sequences, not a limit or an analytic approximation.

Suppose n separators lie strictly between n+1 entries:

$$
r_i<c_i<r_{i+1}\qquad(0\leq i<n).
$$

At every threshold t, the number of separator entries at or below t is no greater than the corresponding entry count, and that entry count is at most one larger. The threshold convention is inclusive: `prefixCount` tests `r i ≤ t`. It counts indices, not distinct values by definition. The interleaving assumptions provide the ordering of these finite prefixes.

If two lists interleave with the same separators, both counts lie between the separator count and that count plus one. Their prefix counts therefore differ by at most one. This conclusion does not require either list to be a polynomial root list.

## Small exact example

These are the relevant finite prefixes, with n = 2:

```text
r = [0, 3, 6]
b = [1, 4, 7]
c = [2, 5]

threshold t       0   2   4   6
count(r ≤ t)      1   1   2   3
count(b ≤ t)      0   1   2   2
count(c ≤ t)      0   1   1   2
```

The inequalities are `0 < 2 < 3`, `3 < 5 < 6`, `1 < 2 < 4`, and `4 < 5 < 7`. Values outside these finite prefixes are unused. The table is a hand-computed illustration, not a compiled Lean example or a new numerical certificate.

## Polynomial layer

The other two theorems start with a nonzero real polynomial and supplied real-root witnesses. If d witnesses are injective and the polynomial's natural degree is at most d, they exhaust `P.roots` as a **multiset**. Thus no additional real root or spare multiplicity remains.

A companion theorem obtains injectivity from ordered open cells. It assumes a monotone boundary sequence b and

$$
b_i<x_i<b_{i+1}.
$$

The boundary sequence need not be declared strictly monotone. The strict occupied-cell inequalities supply the separation needed for distinct witnesses. Open cells matter: adjacent closed cells could share a boundary witness.

The empty cases are retained. With n = 0 there are no separators and one entry, whose inclusive count is zero or one. With d = 0, the nonzero-polynomial and degree hypotheses force an empty real-root multiset.

## Relationship to the sign-witness API

The package's existing sign-change interface constructs witnesses by the intermediate value theorem and counts them in arbitrary disjoint blocks. This companion instead assumes witnesses and adds ordered-prefix bookkeeping. Its degree-exhaustion layer reuses classical Mathlib infrastructure.

No compiled interoperability theorem is supplied here that converts arbitrary sign-witness data into the common-separator hypotheses. Applications must establish their own signs, root witnesses, indexing, ordering and degree budget as required. See [INTERLEAVING-API.md](INTERLEAVING-API.md) for exact types and [FiniteCellCount.lean](FiniteCellCount.lean) for the unchanged source. This is a reusable finite interface, with no current-upstream absence or mathematical novelty claim.
