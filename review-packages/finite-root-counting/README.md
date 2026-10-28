# Finite root witnesses and interleaved prefix counts

The first Lean interface packages a classical finite argument: disjoint strict sign
changes construct distinct real roots, and a degree budget exhausts the complete
root multiset. It also transfers finite endpoint approximation margins to actual
polynomial signs and counts the resulting roots in nonuniform blocks.

The proof uses the intermediate value theorem to place a root strictly inside
each selected open interval. Disjointness makes the roots distinct. When the
polynomial degree is no greater than the number of witnesses, the root multiset
has no additional elements or spare multiplicities. Assigning witness intervals
to disjoint blocks then gives exact block counts. No covering of the real line
by blocks is needed.

The interface permits arbitrary finite witness types, nonuniform interval
lengths, shared interval endpoints, gaps and zero-capacity blocks. Strict signs
keep roots away from shared endpoints. The block-label type need not be finite.
The approximation theorem uses only finite endpoint errors and margins: the
approximating functions themselves need no continuity.

See [API.md](API.md) for its exact three theorems and two definitions, and
[BlockSignCount.lean](BlockSignCount.lean) for the unchanged accepted proof.
Applications must prove their own sign and degree hypotheses.

## Ordered-counting companion

[FiniteCellCount.lean](FiniteCellCount.lean) adds a separate finite interface in any
linear order. If n separators strictly interleave n+1 entries, their inclusive
threshold counts differ by zero or one. Two arrays interleaving with the same
separators therefore have counts within one of each other. These counts are
counts of indices satisfying an inequality, not polynomial root counts by
definition. The cases n = 0 and an empty separator prefix are included.

The same unchanged companion source retains two classical degree-exhaustion
helpers: supplied injective real-root witnesses, or witnesses in ordered open
cells, exhaust a nonzero polynomial's real-root multiset when their number meets
the degree budget. This overlaps the first interface's exhaustion step. Its
distinct contribution is the ordered-prefix API; it does not construct the
analytic or polynomial witnesses needed by an application.

Read the [counting essay and example](INTERLEAVING.md),
[four exact companion contracts](INTERLEAVING-API.md) and
[interface comparison](COMPARISON.md). The two modules do not import each other.
No compiled bridge automatically supplies a shared ordered-cell indexing from
the arbitrary finite sign-witness interface.

[Verification](VERIFICATION.md) records two separate historical Lean 4.35.0
acceptances under the standard axiom baseline: three reports for the sign/block
module and four for the companion. The new two-module project configuration,
combined importing consumer, standalone build and Lean 4.36 port have not been
verified. [Build guidance](BUILD.md), [dependency information](DEPENDENCIES.json),
[original evidence](EVIDENCE.json) and [companion evidence](FINITE-CELL-EVIDENCE.json)
keep those boundaries explicit.

This is a classical formal interface, not a mathematical novelty claim or a
current-upstream absence claim. Naming, placement and contribution notices remain
subject to review; see [ATTRIBUTION.md](ATTRIBUTION.md).
