# Finite sign witnesses and exact polynomial root counts

This Lean interface packages a classical finite argument: disjoint strict sign
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

See [API.md](API.md) for the exact three theorems and two definitions, and
[BlockSignCount.lean](BlockSignCount.lean) for the unchanged accepted proof.
These are reusable finite implications, not claims about signs or root locations
of a particular analytic family. Applications must prove their own hypotheses.

[Verification](VERIFICATION.md) records historical Lean 4.35.0 acceptance under
the standard axiom baseline. A new standalone build, Lean 4.36 port and downstream
replay have not run. [Build guidance](BUILD.md), [dependency information](DEPENDENCIES.json)
and the [evidence summary](EVIDENCE.json) are separate from that historical result.

This is a classical formal interface, not a mathematical novelty claim or a
current-upstream absence claim. Naming, placement and contribution notices remain
subject to review; see [ATTRIBUTION.md](ATTRIBUTION.md).
