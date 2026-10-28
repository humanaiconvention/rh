# Attribution and review status

The proof combines existing Mathlib intermediate-value and polynomial root/degree
infrastructure into the finite interface described in [API.md](API.md).
Its direct imports are:

- `Mathlib.Algebra.Polynomial.Roots`;
- `Mathlib.Topology.Algebra.Polynomial`;
- `Mathlib.Topology.Order.IntermediateValue`.

The historically inspected dependency headers credit Chris Hughes and
collaborators for polynomial root theory, Robert Y. Lewis for polynomial topology,
and Yury Kudryashov and collaborators for intermediate-value infrastructure.
These are dependency acknowledgments, not coauthor assignments. The source does
not reimplement those underlying classical theorems.

The unchanged local contribution has no finalized author/copyright/license
header. Exact human contribution credits and historical model identities for
generation, modifications, verification and editorial work remain unverified.
They are not inferred from the current preparer or from dependency headers.
General AI-assistance disclosure is distinct from authenticated model identity
or an authorship assignment.

Preparation supplies no new rights clearance. Repository MIT intent does not
relicense Apache-licensed dependencies. Applicable dependency notices and the
contribution header require review before submission or release. No new copyright
or license assertion is made by this document.

The open API decision is whether the three theorems and two definitions belong
together under the current namespace and names, or should be integrated nearer
the existing polynomial APIs. Existing overlap observations concern a dated,
pinned environment; no present-upstream absence or mathematical novelty is
claimed. Compatibility and publication decisions are separate from the saved
historical acceptance in [VERIFICATION.md](VERIFICATION.md).
