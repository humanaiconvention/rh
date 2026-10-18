# Complete-form approximation and an exact zero-mode Schur criterion

This note records a formalized domain bridge and a conditional local reduction for a concrete arithmetic quadratic form. It proves neither global positivity nor the Riemann Hypothesis. Its contribution is a checked implementation and an explicit description of the remaining cancellation, rather than a new arithmetic estimate.

## 1. The concrete form

Use the Fourier convention

$$
 \widehat w(\xi)=\int_{\mathbb R}w(t)e^{-2\pi i t\xi}\,dt,
 \quad \beta_k=2k+\tfrac12,
 \quad m(\omega)=\sum_{k\ge0}\frac{2\omega^2}{\beta_k(\beta_k^2+\omega^2)}.
$$

For R>0, let V_R consist of real L2 equivalence classes supported in [-R,R] with

$$
 \|w\|_V^2=\|w\|_2^2+e[w]<\infty,\qquad
 e[w]=\int_{\mathbb R}m(2\pi\xi)|\widehat w(\xi)|^2\,d\xi.
$$

Define S_L z(t)=z(t+L)+z(t-L), using zero extension. With

$$
 C_0=\gamma+\frac\pi2+3\log2+\log\pi,\qquad
 \alpha_n=\frac{\Lambda(n)}{\sqrt n},\qquad L_n=\log n,
$$

the native diagonal is

$$
 q_{R,N}[w]=e[w]-C_0\|w\|_2^2
 +2\left|\int\cosh(t/2)w(t)dt\right|^2
 -2\left|\int\sinh(t/2)w(t)dt\right|^2
 -\sum_{n=2}^N\alpha_n\langle w,S_{L_n}w\rangle.
$$

All integrals of w use its supported representative. The real symmetric bilinear form is its exact polarization. The Lean construction initially permits arbitrary real C in place of C_0 and regards the complex weighted space as real; the physical core is the actual real subspace, not the complex span of real generators.

A horizon is sufficient when every omitted row has either zero von Mangoldt coefficient or log n>=2R. At contact, overlap is a singleton and vanishes almost everywhere. Thus N=floor(exp(2R)) is sufficient. For every bounded radius range, choose one sufficient cap first: all subsequent form equalities and limits in that range use that fixed finite cap. There is no infinite prime-sum interchange. Write q_R=q_{R,N} for any sufficient N; the proved horizon identity makes this independent of that choice.

## 2. Same-support completion

**Domain theorem.** Every w in V_R has real compact smooth approximants w_j supported strictly inside (-R,R), with ||w_j-w||_V->0.

The construction first contracts the support by genuine physical dilation, with strong convergence in the complete weighted norm; it then mollifies within the resulting support gap. The actual spatial and Fourier representatives are identified almost everywhere. No H1 derivative assumption is imposed on w.

All remaining terms of q are bounded forms on physical L2 at a fixed radius. In particular, both ranks, the scalar, and every prime-power two-shift survive convergence. If |q[w]-e[w]|<=K||w||_2^2 with K>=0, the positive shifted norm sqrt(q[w]+(K+1)||w||_2^2) is equivalent to ||.||_V, without assuming q>=0.

For a REAL physical input v in L2([-R,R]), the anchored primitive is

$$
 w(t)=\begin{cases}\int_{-R}^t v(u)du,&t<0,\\
 -\int_t^R v(u)du,&t>0,\\0,&t=0.\end{cases}
$$

It belongs to V_R even when its one-sided limits at zero differ. For a strict-interior smooth f, the anchored primitive of f' equals f almost everywhere; equality at the assigned value zero is not needed. The checked kernel dictionary consequently proves

$$
 \text{native physical kernel PSD on every REAL L2 input at R}
 \quad\Longleftrightarrow\quad q_R[w]\ge0\ \ (w\in V_R).
$$

A hypothetical negative complete-form vector therefore has a genuine strict-interior smooth physical derivative witness. This implication does not construct a negative native vector.

The elementary completion argument and Schur method are standard mathematics. The source comparison with [Suzuki, *Weil's quadratic form via the screw function*, v3](https://arxiv.org/html/2606.09096v3) is a written initial-form/completion comparison; no external spectral theorem or equality of associated unbounded operator domains is silently imported into Lean. The actual compactness and continuity used here are proved directly.

## 3. Compactness and the actual positive complement

The inclusion V_R->L2 is compact. The checked finite Fourier-grid construction has squared approximation error at most

$$
 \left(\frac1{1+m(2\pi\Omega)}
 +\frac{64\pi^2R^3\Omega^3}{M^2}\right)\|w\|_V^2.
$$

Take Omega=n+1 and M=(n+1)^2. In a restricted real spatial codomain, apply inverse Fourier transform, real part and restriction; the latter maps are contractions. Raw inverse-Fourier grid approximants are not asserted to have the desired support.

**Conditional gap theorem.** If q_R>=0, its actual form radical K is finite dimensional, and there is mu>0 such that

$$
 q_R[w]\ge\mu\|w\|_2^2\qquad(w\perp_{L2}K).
$$

Compactness is the proved input, not an assumed compact-resolvent theorem. The physical-L2 orthonormal basis of K and its spanning property are constructed. This is primitive coercivity; it is not an L2 bound on the derivative input v.

## Local point-jet exclusion

A supporting formal theorem concerns continuous real-linear functionals on the WHOLE weighted Fourier Hilbert space, before support restriction. A functional defined only on a restricted core is not silently extended to that space. Let U be open and x_i be finitely many distinct points in U. If a continuous functional T is represented on real compact smooth tests supported in U by

$$
 T(f)=\sum_i\sum_{k=0}^{K}a_{i,k}f^{(k)}(x_i),
$$

then every a_{i,k} is zero. This local statement imposes no condition on T outside U and evaluates only literal smooth representatives, never arbitrary L2 point values.

The checked tests are translated, shrinking bump-times-monomial profiles. Their selected jet equals1 and all other prescribed jets eventually vanish, while

$$
 \|f_{j,r}\|_V^2\le r^{-(2j+1)}(1+5\log r)\|\phi_j\|_V^2\longrightarrow0.
$$

Continuity of T forces the isolated coefficient to vanish. Exact support shrinkage places these tests inside U. No H1 cutout estimate is substituted.

This excludes boundary point distributions **once** their finite-jet representation has been proved. The general finite-support distribution structure theorem and the actual total exterior-flux vanishing are separate obligations; neither is silently supplied by this result.

## 4. Exact outward Schur object

Fix one cap sufficient for a neighborhood of R. For r>=1 put

$$
 U_rw(t)=r^{-1/2}w(t/r),\qquad q_r(v,w)=q_{rR}(U_rv,U_rw).
$$

The actual dilation is a physical L2 isometry between the complete domains, with a continuous inverse. The exact 5 log(r) multiplier estimate gives strong domain control. Together with the transported ranks and all finite two-shifts it proves local graph-form smallness of q_r-q_1.

Assume ONLY q_1>=0. Let K={p:q_1(p,z)=0 for every z in V_R}, let P be its physical-L2 projection and let Q=I-P on V_R. On a genuine neighborhood of r=1, the restricted form

$$
 B_r=q_r|_{Q V_R}
$$

is coercive in the complete norm. For p in K define b_p(z)=q_r(p,z), z in QV_R, and let T_rb_p be the unique weak solution

$$
 B_r(T_rb_p,z)=b_p(z)\quad(z\in QV_R).
$$

This form-dual inverse is constructed. It is not merely identified with an unbounded operator inverse by notation. Define the symmetric Schur form

$$
 S_r(p,p')=q_r(p,p')-B_r(T_rb_p,T_rb_{p'}).
$$

The subtraction includes every ordered source pair through ONE full inverse. No prime cross-covariance is discarded. Square completion proves q_r>=0 iff S_r>=0 on K.

## 5. The stronger zero-mode constraint

Literal support inclusion preserves old pairings exactly. First include K literally into V_{rR}; its inward image

$$
 W_r=U_r^{-1}K\subset V_R
$$

is exactly isotropic for q_r. Its physical coordinate map onto K is locally surjective: in an actual physical orthonormal basis, the overlap matrix tends to identity and its determinant tends to1.

For any coordinates c, select w in W_r with Pw=p_c. Exact square completion gives

$$
 \boxed{c^\top S_rc=-B_r(Qw+T_rb_{p_c},Qw+T_rb_{p_c})\le0.}
$$

Consequently the complete local criterion is

$$
 \boxed{q_r\ge0\text{ on }V_R\quad\Longleftrightarrow\quad S_r=0.}
$$

The right side is literal matrix equality, equivalently vanishing of the WHOLE completed complement vector. This conclusion includes the zero-dimensional radical case. The theorem does not prove that a hypothetical zero radius exists, or that any entry is zero or nonzero. If S_r!=0, the checked exact minimizing vector has negative energy and transfers to a smooth physical witness, conditionally.

A small O(eta^2) inverse-source cost cannot replace this equality. The first variation on an old null vector cannot discard the negative second-order cross-coupling. Newly activated prime powers remain part of the complete source; isolated component signs settle neither cancellation nor noncancellation.

## 6. Remaining mathematical obligation

Continuity and the nondegeneracy strategy are already present in Suzuki v3, Theorem1.3 and its surrounding discussion. The results here are a direct formal implementation for the declared native form, not a new arithmetic route around that known obstruction. The ground energy is normalized by ||w||_2=1 on V_R. The physical-unit Rayleigh set is nonempty, its energies are bounded below, and their infimum is continuous in positive R and nonincreasing under support inclusion. These native statements use exact common-horizon identities, not a moving-cutoff heuristic. A zero bottom gives a genuine nonzero radical vector by compactness. Continuity does not preserve positivity outward.

To prevent finite-radius stalling one needs an actual arithmetic theorem excluding such null states, or proving exact whole Schur compensation at them. Neither is supplied here. The compiled optional global criterion assumes BOTH a strictly positive initial primitive Rayleigh bottom and trivial actual radical at every later nonnegative native state. Within this extract both premises remain explicit. In particular, the arithmetic no-null hypothesis is not discharged. No finite endpoint numerical reserve has been promoted to an all-radius bound, and no Riemann zero location is assumed or derived.

## 7. Verification scope

The release is intended to include sources, pinned build configuration, declaration map and a sanitized replay manifest. Terminal declarations audit only propext, Classical.choice and Quot.sound; no admitted analytic axiom, sorry, or native_decide is accepted. Source compilation and any subsequent kernel recheck must be reported separately. Pinned package binaries/toolchain remain explicit dependencies unless a receipt says they were rechecked. Internal adversarial checks are internal checking, not external independent review. Historical private logs, source archives and unrelated project material are not publication content.

The accompanying verification report states the exact source-closure and imported-library boundaries. No unproved compensation identity is classified as a verified result.
