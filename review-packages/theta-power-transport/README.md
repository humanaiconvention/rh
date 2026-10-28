# Sharp power-coordinate budgets for theta and Macdonald densities

Let p and q be the complete normalized theta and Macdonald densities on (0,∞). In this package,

$$
p(u)=\frac{\sum_{n\geq0}(8z_n(u)^2-12z_n(u))e^{u/2-z_n(u)}}{\xi(1/2)},
\qquad z_n(u)=\pi n^2e^{2u},
$$

and

$$
q(u)=\frac{2e^{-2\pi\cosh(2u)}}{K_0(2\pi)},
\qquad K_0(x)=\int_0^\infty e^{-x\cosh t}\,dt.
$$

The theta normalizer uses its proved real/complex identification with ξ(1/2). Both densities have unit mass. [SOURCE-DEFINITIONS.md](SOURCE-DEFINITIONS.md) gives the exact Lean definitions and normalization dictionary.

For a natural exponent k, define the moment gap

$$
\Delta_k=\int_0^\infty u^kp(u)\,du-\int_0^\infty u^kq(u)\,du.
$$

For every nonnegative Lipschitz constant K and every real K-Lipschitz function φ, both weighted integrals exist and

$$
\left|\int_0^\infty\phi(u^k)p(u)\,du-
\int_0^\infty\phi(u^k)q(u)\,du\right|\leq K\Delta_k.
$$

For k > 0, the gap is strictly positive and is the sharp unit-Lipschitz budget: φ(x)=x attains it. The final theorem states the corresponding equivalence for every real proposed budget B.

The proof instantiates a classical signed single-crossing comparison. The actual density crossing supplies a threshold c; on the positive half-line, u ↦ u^k preserves its sign orientation with threshold c^k. Imported source theorems establish normalization, crossing and every required natural-power integrability condition. They are not extra assumptions in the final actual-source statements.

Lipschitzness concerns φ in its coordinate argument. The physical function u ↦ φ(u^k) need not be Lipschitz in u. This is one family quantified over natural k, including zero for the general bound, not a numerical bound independent of k or an extension to real exponents.

## Verification and reuse

[ThetaPowerCoordinate.lean](ThetaPowerCoordinate.lean) is the unchanged seven-contract source with historical acceptance under Lean **4.36.0-rc1** and Mathlib **c85646e3ac7d3ca39468f114b2d95d62e1611533**. All seven saved terminal axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The accompanying provider sources make the dependency statements inspectable. The extracted configuration, standalone build and importing-consumer replay have not been verified afresh. See [exact statements](THEOREM-STATEMENTS.md), [verification scope](VERIFICATION.md), [evidence](EVIDENCE.json), [dependency map](DEPS.json), and [build guidance](BUILD.md).

The contribution presented for review is an actual-source instantiation of a classical mechanism. No new duality or current-upstream absence claim is made. [COMPARISON.md](COMPARISON.md) separates it from the generic coordinate interface and the existing cumulative/moment results; [ATTRIBUTION.md](ATTRIBUTION.md) records the remaining review gates.
