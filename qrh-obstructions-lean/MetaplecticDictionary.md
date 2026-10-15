# Conjugate-slot phase survival

`MetaplecticDictionary.lean` proves the exact finite algebra behind the
norm-157 conjugate slot. It uses the same pinned Lean and mathlib versions
as the obstruction formalization.

The concrete Eisenstein ring is the subalgebra
$\mathbb Z[\omega]\subset\mathbb C$, with
$\omega=(-1+i\sqrt3)/2$. The file verifies its primitive-root relation,
the cyclotomic equation $\omega^2+\omega+1=0$, and integrality over
$\mathbb Z$. For the elements

$$
p=13+12\omega=7+6\sqrt3\,i,\qquad
\bar p=1-12\omega=7-6\sqrt3\,i,
$$

it proves both squared complex norms are $157$, and

$$
p^2=-59+84\sqrt3\,i.
$$

Here the arithmetic norm is the **squared** complex norm; the complex
absolute value of each element is $\sqrt{157}$.

Set $\alpha=p/\sqrt{157}$. For **every** complex $u$ satisfying
$|u|=1$ and $u^3=\overline\alpha^{\,2}$, put $x=u+\bar u\in\mathbb R$.
The file proves

$$
157x^3-471x+118=0,\qquad
\frac{118}{471}\le |x|\le2,\qquad x\ne0.
$$

The identity follows from $u\bar u=1$ and
$\overline\alpha^{\,2}+\alpha^2=-118/157$. For the lower bound,
$|x|\le2$ gives $|x^2-3|\le3$, while the polynomial gives
$|x|\,|x^2-3|=118/157$. These are all exact deductions.

Existence of a unit cubic root is also proved using algebraic closure of
$\mathbb C$. The definitions `u_p` and `u_pbar` select one such root
and its conjugate. The principal declarations are:

| Lean declaration | Statement |
| --- | --- |
| `phase_polynomial` | The polynomial for every phase satisfying the two hypotheses |
| `phase_lower_bound` | The uniform positive lower bound |
| `phase_nonzero` | Nonvanishing of the conjugate-pair sum |
| `survival_polynomial` | The polynomial for the selected witness |
| `survival_bounds` | Both bounds for the selected witness |
| `combined_phase_nonzero` | Nonvanishing for the selected witness |

All names are in the `MetaplecticDictionary` namespace. The real variable
is implemented as `combinedReal u = 2 * u.re`; `combinedReal_cast` proves
that its complex embedding equals $u+\bar u$.

Reproduce with:

```sh
lake build MetaplecticDictionary --wfail
lake env lean MetaplecticDictionary.lean
python scripts/verify_metaplectic.py
```

`METAPLECTIC-VERIFICATION.json` and `METAPLECTIC-VERIFICATION.log` record
the compiler and axiom audit. There are no admitted proofs or added
mathematical axioms.

This certifies the **algebraic implication from the stated phase
relation**. It does not derive that relation from the native Gauss-sum
formula, select its specific branch, prove ring-theoretic primality,
evaluate the complete physical row, or formalize Kuznetsov theory. In
particular, nonvanishing of this phase factor is not a lower bound for
the complete row or an RH result.
