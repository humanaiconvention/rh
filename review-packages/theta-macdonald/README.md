# Theta and Macdonald density order

This development formalizes a comparison between two specific probability densities on the positive half-line. It proves their unique crossing, the strict order of their cumulative integrals, and the order of every positive integer moment.

The densities are

$$
m(u)=\frac{\Phi(u)}{\gamma_0},\qquad
n(u)=\frac{2e^{-2\pi\cosh(2u)}}{K_0(2\pi)},
$$

where $\Phi$ is the [complete theta-shell series](SOURCE-DEFINITIONS.md), $\gamma_0=\xi(1/2)>0$, and

$$
K_0(x)=\int_0^\infty e^{-x\cosh t}\,dt\qquad(x>0).
$$

Both densities have proved total mass one. Their normalization and integrability are part of the accepted dependency chain.

## One crossing determines cumulative order

There is a unique $c>0$ where the densities agree. Before that point, $m(u)<n(u)$. After it, $n(u)<m(u)$.

Consequently, for every $u>0$,

$$
\int_0^u m(t)\,dt<\int_0^u n(t)\,dt.
$$

These cumulative integrals measure how much mass lies before a chosen point. The comparison resembles two equal cargo loads spread along a pier: the theta load has less cargo before every finite marker, while both loads have the same total weight.

Before the crossing, the inequality follows directly from the density order. After the crossing, the remaining theta tail is larger. Equal total masses then determine the order of the preceding integrals.

## Moment order

A moment weights mass by its distance from the origin. For every positive natural number $j$,

$$
\int_0^\infty u^j n(u)\,du<\int_0^\infty u^j m(u)\,du.
$$

The required weighted integrability is proved. The zeroth moments are equal.

A further comparison theorem handles a real weight $w$ that is nondecreasing on $(0,\infty)$, for which both $wm$ and $wn$ are Lebesgue integrable there, and which satisfies

$$
\forall c>0,\quad \exists b>c:\quad w(c)<w(b).
$$

## Formal results and verification

The principal declarations are `ThetaMacdonald.Crossing.actual_density_crossing`, `ThetaMacdonald.Cumulative.actual_CDF_strict_order` and `ThetaMacdonald.Moment.actual_power_moment_order`. The [exact statements](THEOREM-STATEMENTS.md), [definitions](SOURCE-DEFINITIONS.md) and [included dependency chain](DEPENDENCY-HANDOFF.md) retain actual normalization, complete-series convergence and weighted integrability.

All 27 unchanged local sources have saved acceptance with **Lean 4.36.0-rc1** and **Mathlib c85646e3ac7d3ca39468f114b2d95d62e1611533**. The 157 saved terminal reports stay within `propext`, `Classical.choice` and `Quot.sound`. Full declaration and report coverage is explicit. [Verification](VERIFICATION.md).

**The newly assembled standalone package has not been built or replayed.** Its root lock is a statically checked proposal; fresh aggregate replay is distinct from the saved individual checks. [Build prerequisites](BUILD.md), [human review](HUMAN-REVIEW.md).

Preparation was AI-assisted. Exact historical model identities remain unverified; human mathematical, API, editorial, source-rights and release review remain pending. [Provenance](PROVENANCE.md), [attribution](ATTRIBUTION.md), [notice status](LICENSE-STATUS.md).
