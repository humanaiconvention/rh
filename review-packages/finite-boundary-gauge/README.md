# Finite mixed differences and boundary values

This package proves reconstruction identities for finite rectangular arrays with entries in any commutative ring, including the real or complex numbers. Two arrays have the same mixed differences precisely when their difference is determined by a row term and a column term. Their final row and column determine that remaining ambiguity.

For an array on the nodes $0\le i\le n$, $0\le j\le m$, the mixed difference on a cell $i<n$, $j<m$ is

$$
\Delta_{12}A(i,j)=A(i+1,j+1)-A(i,j+1)-A(i+1,j)+A(i,j).
$$

It measures how a change in one direction varies along the other.

## Reconstruction

Two arrays $A$ and $B$ have equal mixed differences exactly when, throughout the closed rectangle,

$$
\begin{aligned}
A(i,j)-B(i,j)={}&[A(i,m)-B(i,m)]\\
&+[A(n,j)-B(n,j)]-[A(n,m)-B(n,m)].
\end{aligned}
$$

Equal mixed differences and equal final rows and columns therefore imply equality everywhere. Both boundary requirements are retained, the shared corner is subtracted once, and zero side lengths are allowed.

Boundary values serve as a chart's reference marks: local differences describe changes, while the edges fix the remaining reference.

## Weighted sums

Adding a row term, a column term or a constant leaves every mixed difference unchanged. This freedom is called a boundary gauge.

The companion summation identities retain the edge and corner contributions. Two arrays with equal mixed differences have equal bilinear sums whenever **both** coefficient totals vanish:

$$
\sum_{i=0}^{n}u_i=0,\qquad \sum_{j=0}^{m}v_j=0.
$$

These are sufficient hypotheses for the stated corollary; no necessity claim is made. The proofs use finite induction and rectangular summation by parts. This is a formal implementation of classical finite algebra with its boundary terms retained.

## Lean statements and use

The sources are [CumulativeBoundary.lean](CumulativeBoundary.lean) and its sole local dependency [CumulativeQuadratic.lean](CumulativeQuadratic.lean). They use natural-indexed functions restricted to the finite rectangle; this is not a `Fin n` array API. [Exact statements and conventions](THEOREM-STATEMENTS.md) and the [claim map](evidence/claim-map.json) identify the hypotheses.

The principal declarations in namespace `CumulativeQuadratic` are:

- `mixedDifference_eq_iff_boundary_difference`
- `eq_of_mixedDifference_eq_of_boundary_eq`
- `bilinear_eq_of_mixedDifference_eq_of_mass_zero`

## Verification status

These exact source bytes have saved passing checks with **Lean 4.36.0-rc1** and **Mathlib c85646e3ac7d3ca39468f114b2d95d62e1611533**. The saved structural reports use only `propext`; the bilinear reports stay within `propext`, `Classical.choice`, and `Quot.sound`. [Saved evidence and check status](VERIFICATION.md).

**The newly assembled standalone package has not been built or replayed.** Its root lock is a statically checked proposal, and human review and release approval are pending. [Build prerequisites and recipe](BUILD.md), [review checklist](HUMAN-REVIEW.md).

Preparation was AI-assisted. Exact historical model identities remain unverified; roles are separated in [attribution](ATTRIBUTION.md). The [license and notice status](LICENSE-STATUS.md) retains existing notices without making a new grant or asserting completed rights clearance.
