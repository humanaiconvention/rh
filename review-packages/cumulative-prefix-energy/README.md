# Finite cumulative-prefix energy

This package formalizes an exact integral identity for two weighted running totals.

Let $s$ be a finite index set and $p_i>0$ its real sites, with arbitrary real coefficients $c_i$ and $e_i$. For $t>0$, define the inclusive prefixes

$$
M_c(t)=\sum_{\substack{i\in s\\p_i\le t}}c_i,\qquad
g_c(t)=\sum_{\substack{i\in s\\p_i\le t}}\frac{c_i}{p_i},\qquad
\gamma_c(t)=g_c(t)-\frac{M_c(t)}{t},
$$

and define $M_e,g_e,\gamma_e$ in the same way.

The prefix $M_c$ is a running total. The weighted prefix $g_c$ divides each entry by its site. In $\gamma_c$, the matching jumps of $g_c$ and $M_c(t)/t$ cancel at each site.

## The identity

For $0<a\le b$,

$$
\begin{aligned}
\int_a^b g_c(t)g_e(t)\,dt
={}&b\gamma_c(b)\gamma_e(b)-a\gamma_c(a)\gamma_e(a)\\
&+\int_a^b\frac{M_c(t)M_e(t)}{t^2}\,dt.
\end{aligned}
$$

The formula keeps both endpoint contributions and the full interaction between the two coefficient families.

It resembles reconciling two voyage logs. The accumulated entries along the route must be reconciled with the recorded balances at departure and arrival. Those endpoint balances are part of the calculation.

Sites may repeat, coefficients may have either sign, and neither coefficient total needs to vanish. Endpoints may coincide with sites. The empty family and $a=b$ are included.

## How the proof works

The square-energy identity comes first. Its proof uses a continuous compensated primitive and its right derivative, including at jump locations. The bilinear identity then follows by polarization: expanding the square identity for $c+e$ and subtracting the identities for $c$ and $e$ isolates the cross product.

The required integrability is proved.

## Formal results and verification

The principal declarations are `CumulativeSquareEnergy.finite_prefix_square_energy` in the [square-energy source](CumulativeSquareEnergy.lean) and `CumulativePrefixBilinear.finite_prefix_bilinear_energy` in the [bilinear source](FinitePrefixBilinear.lean). Their [exact statements](THEOREM-STATEMENTS.md) use one common finite index set and real site and coefficient functions.

These exact source bytes have saved passing checks with **Lean 4.36.0-rc1** and **Mathlib c85646e3ac7d3ca39468f114b2d95d62e1611533**. Ten saved terminal axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. Eighteen public theorems and four definitions are documented; the ten reports are not a separate audit print for every helper. [Verification and evidence](VERIFICATION.md).

**The newly assembled standalone package has not been built or replayed.** Its root lock is a statically checked proposal. [Build prerequisites and recipe](BUILD.md), [human review and blockers](HUMAN-REVIEW.md).

This is a formal implementation of finite cumulative-sum calculus, the right-sided fundamental theorem of calculus and polarization. The useful feature is the explicit signed coefficients, jump convention, proved integrability and retained endpoints. No new arithmetic cancellation estimate or global novelty claim is made.

Preparation was AI-assisted. Historical generating, editing, checking and editorial model identities remain unverified. [Attribution by role](ATTRIBUTION.md) and [existing notices and release status](LICENSE-STATUS.md). Human review and approval remain pending.
