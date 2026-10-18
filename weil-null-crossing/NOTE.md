# Complete rows, strict domain increase, and the remaining arithmetic question

## Form and domain

Use the [parent form and Fourier normalization](../weil-form-domain/NOTE.md). For R>0, V_R is the REAL complete logarithmic Fourier domain supported in [-R,R]. Its physical norm is the L2 norm of the primitive w, not the norm of the derivative input.

For a real scalar C and finite horizon N,

$$
q_{R,C,N}[w]=e[w]-C\|w\|_2^2
+2\left|\int\cosh(t/2)w(t)\,dt\right|^2
-2\left|\int\sinh(t/2)w(t)\,dt\right|^2
-\sum_{n=2}^{N}\frac{\Lambda(n)}{\sqrt n}\langle w,S_{\log n}w\rangle .
$$

Both shifts, both ranks, the scalar and the full native archimedean energy remain attached. Native statements use C=C_arch and a sufficient horizon, with one common cap fixed before comparing two radii. No infinite prime-sum interchange is used.

## 1. Finite-point removal and complete weak gluing

For every finite point set F, real compact smooth functions supported inside (-R,R) and avoiding F are dense in V_R. The proof uses actual shrinking cutoff profiles in the complete graph norm, not physical L2 density alone.

Consequently a continuous functional defined only on V_S is zero if it vanishes on smooth tests in the old interior (-R,R) and both collars (-S,-R), (R,S). No extension of that functional to the whole weighted space is assumed. Finite-point density removes the possible residual at the two junctions directly.

For an actual old radical vector, literal support inclusion supplies the interior equation. The two whole collar equations are then the exact remaining inputs to gluing.

## 2. Strict-interior weak-null uniqueness

For any real C, finite N and 0<R<S,

$$
p\in V_R,\qquad q_{S,C,N}(p,g)=0\quad(g\in V_S)
\quad\Longrightarrow\quad p=0.
$$

This uses no positivity hypothesis. The proof has three parts.

First, the complete form is jointly translation invariant on compact supported inputs. The archimedean Fourier energy and the finite two-shifts are translation invariant. The two rank moments mix by a hyperbolic 2-by-2 matrix, and their SIGNED difference is invariant. Neither rank is discarded.

Second, on any intermediate window R<T<S, all sufficiently small translates of p lie in the true radical. That radical is finite dimensional even without PSD: the graph bound on a zero row and the actual compact physical embedding make its unit ball compact.

Third, a finite-dimensional local translate span of a nonzero compact L2 vector would be invariant under every ambient translation. Choose a finite basis of sufficiently small translates; a uniform small translation preserves that span and its inverse does too. Iteration gives every translation. A sufficiently distant translate then contradicts compact support.

The distant step is ambient L2 algebra. It never evaluates the native form far away or changes its finite horizon.

Combined with part 1, a hypothetical nonzero old radical cannot have BOTH whole collar weak equations vanish. This proves no numerical lower bound on the collar row and isolates no individual prime contribution.

## 3. Exact literal-old-null Schur sign

Assume the complete base form is PSD on V_R. Its actual finite radical K and a positive physical complement gap are constructed. Under outward unitary physical dilation U_r, pull the LITERAL old supported radical inward:

$$
W_r=U_r^{-1}K\subset V_R,\qquad
q_r(v,w)=q_{rR}(U_rv,U_rw).
$$

The low-low block on W_r is exactly zero. The moving physical orthogonal complement remains coercive for r sufficiently close to 1. Let B_r denote the full complement form, and b_p its WHOLE row source. With the constructed form-dual inverse,

$$
S_r(p,p')=-B_r(T_rb_p,T_rb_{p'}).
$$

For r>1, part 2 makes the source map injective on W_r. Thus

$$
S_r(p,p)<0\qquad(0\ne p\in W_r).
$$

The zero-dimensional case is included: there are no nonzero old-null coordinates. Locally outward PSD holds exactly when the old radical dimension is zero.

This is the Schur matrix for the literal-old-null projection. It is not identified with the parent's fixed-projection matrix or claimed simply congruent through an overlap matrix. All ordered source interactions use one full inverse.

More generally, a hypothetical nonzero old zero-diagonal vector yields a genuine compact smooth physical derivative witness of negative energy in every strictly larger window. This conditional theorem does not construct the old vector. A zero diagonal of an indefinite form is not silently classified as a radical.

## 4. Attainment and strict radial decrease

Let

$$
\lambda_{R,C,N}=\inf_{\substack{w\in V_R\\\|w\|_2=1}}q_{R,C,N}[w].
$$

The unit set is nonempty and its energies are bounded below. Exact scalar shifting gives

$$
q_{C+a}=q_C-a\langle\cdot,\cdot\rangle_{L^2},
\qquad \lambda_{R,C+a,N}=\lambda_{R,C,N}-a.
$$

Set $a=\lambda_{R,C,N}$. The shifted bottom is zero; actual compact zero-bottom attainment supplies a nonzero true shifted radical. Physical normalization gives a genuine minimizer of the original Rayleigh quotient.

If the bottoms at R<S were equal, the larger shifted form would also be PSD. Literal inclusion would preserve the smaller minimizer's zero diagonal; PSD would make its WHOLE larger row zero, contradicting part 2. Hence

$$
\boxed{\lambda_{S,C,N}<\lambda_{R,C,N}\quad(0<R<S).}
$$

Choosing the larger sufficient cap first gives strict decrease for the actual native all-prime bottom. No eigenvalue sign or particular zero radius is determined.

## Prior art and the exact remaining question

[Suzuki, Weil's quadratic form via the screw function, v3, 23 September 2026](https://arxiv.org/html/2606.09096v3) supplies the relevant closed-form/Friedrichs framework, ground attainment and continuity in Theorem 1.1, Corollary 1.2 and Theorem 1.3. Its following discussion recalls the RH/nondegeneracy criterion. This supplement implements direct structural consequences for the declared native form; no novelty claim or complete verification of that paper is made.

The source comparison is a written matching of bounded-window forms and Fourier conventions. No associated external unbounded operator theorem or global temperedness of the screw function is imported into these Lean proofs.

Strict decrease excludes a plateau and permits at most one zero radius. It does not tell whether the native bottom remains positive or crosses zero. At a genuine old null, exact outward compensation is impossible; the unresolved task is absence of that OWN-window null in the first place.

Precisely, the parent's conditional global criterion requires a strictly positive initial primitive bottom and the hypothesis NoNullNonnegativeStates for the actual native $C_{\rm arch}$: at every later nonnegative native window, the actual radical is trivial. That arithmetic hypothesis remains unproved. It is not a requirement of nondegeneracy for all C,N; arbitrary scalar shifts intentionally have ground nulls by part 4.

There is no new quantitative arithmetic estimate, renewable margin, all-radius positivity theorem or RH proof.
