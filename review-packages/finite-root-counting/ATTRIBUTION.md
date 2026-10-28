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

The companion adds elementary finite-index inclusions and reuses Mathlib's
`Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero` for the supplied-witness
exhaustion helpers. Its imports are `Mathlib.Algebra.Polynomial.Roots` and
`Mathlib.Data.Real.Basic`. Dependency acknowledgment is distinct from assigning
authorship of the local wrapper or of the comparison interface.

Both unchanged local contributions have no finalized author/copyright/license
headers. Exact human contribution credits and historical model identities for
generation, modifications, verification and editorial work remain unverified.
They are not inferred from the current preparer or from dependency headers.
General AI-assistance disclosure is distinct from authenticated model identity
or an authorship assignment.

Preparation supplies no new rights clearance. Repository MIT intent does not
relicense Apache-licensed dependencies. Applicable dependency notices and the
contribution header require review before submission or release. No new copyright
or license assertion is made by this document.

The open API decision is where the seven theorems and three definitions belong:
the generic ordered-prefix layer may fit nearer finite-order counting, while
the sign and degree helpers concern polynomial APIs. The modules retain their
original separate namespaces and no proof was refactored. Existing overlap observations concern a dated,
pinned environment; no present-upstream absence or mathematical novelty is
claimed. Compatibility and publication decisions are separate from the saved
historical acceptance in [VERIFICATION.md](VERIFICATION.md).
