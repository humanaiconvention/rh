# Jensen approximation of a paired-measure transform

This development formalizes a cosine-type transform built from two positive measures. It expresses the transform as a convergent moment series and gives an explicit error bound for finite polynomial approximations.

Let $\mu_+$ and $\mu_-$ be positive Borel measures on $[0,\infty)$, and put $\theta=\mu_++\mu_-$. Assume that $u\mapsto e^{bu^2}$ is integrable with respect to $\theta$ for some $b>0$, and define

$$
M_b=\int_0^\infty e^{bu^2}\,d\theta(u).
$$

This Gaussian integrability condition controls how much mass can lie far from the origin. It requires the rapidly growing weight $e^{bu^2}$ to have a finite integral; the measures themselves need not be Gaussian distributions. Origin atoms, zero measures and zeroth moments are included.

## The transform and its moments

Define

$$
C(w)=\sum_{j\ge0}\frac{(-w)^j}{(2j)!},\qquad
F(z)=\int C(zu^2)\,d\mu_+-\int C(zu^2)\,d\mu_-.
$$

For nonnegative real $w$, the kernel equals $\cos(\sqrt w)$. Its series definition also works throughout the complex plane.

Writing

$$
m_j=\int u^{2j}\,d\mu_+-\int u^{2j}\,d\mu_-,
$$

the development proves

$$
F(z)=\sum_{j\ge0}\frac{(-1)^jm_jz^j}{(2j)!}.
$$

It also proves that $F$ is entire, meaning complex differentiable at every complex point. The proof establishes integrability and absolute convergence before exchanging the series and integrals.

## A polynomial with a stated error budget

For each integer $d\ge1$ and $0\le j\le d$, set

$$
w_{d,j}=\prod_{0\le k<j}\left(1-\frac{k}{d}\right),\qquad
J_d(z)=\sum_{j=0}^d w_{d,j}\frac{(-1)^jm_jz^j}{(2j)!}.
$$

The empty product at $j=0$ is one. These Jensen weights modify the retained coefficients rather than simply truncating the series.

For every $r\ge0$,

$$
\sup_{|z|\le r}|J_d(z)-F(z)|
\le\frac{M_br^2}{3b^2d}\exp\!\left(\frac{r}{2b}\right).
$$

The bound acts like a navigation tolerance attached to a charted area. Increasing the polynomial degree reduces the allowance; enlarging the area changes the allowance too. On each fixed disk, the bound decreases in proportion to $1/d$.

## Formal results and verification

The principal declarations are `SignedJensenEntirePrep.signedPair_nativeKernel_eq`, `SignedJensenEntirePrep.analyticAt_signedPair_nativeKernel` and `SignedJensenMeasurePrep.signedPair_kernel_error_gaussian`. The [exact statements](THEOREM-STATEMENTS.md) connect the finite error to the actual polynomial through `SignedJensenMomentsPrep.finiteMomentPolynomial_error_gaussian`. [Source boundary](SOURCE-HANDOFF.md).

Each of the five unchanged sources has saved individual acceptance with **Lean4.36.0-rc1** and **Mathlib c85646e3ac7d3ca39468f114b2d95d62e1611533**. Their54saved terminal axiom reports stay within `propext`, `Classical.choice` and `Quot.sound`. The full source roster and report coverage are explicit. [Verification](VERIFICATION.md).

**The newly assembled standalone package has not been built or replayed.** Its root lock is a statically checked proposal;fresh aggregate replay is distinct from the five saved acceptances. [Build prerequisites](BUILD.md), [human review](HUMAN-REVIEW.md).

This packages generic approximation and analytic infrastructure. Historical model identities remain unverified,and human understanding,source-rights and release approval remain pending. [Provenance](PROVENANCE.md), [attribution](ATTRIBUTION.md), [notice status](LICENSE-STATUS.md). The positive pair is not identified with Jordan/total variation,and no Gaussian premise for an actual arithmetic source is supplied by this result.
