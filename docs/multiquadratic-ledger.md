# Exact square-root coordinates: nonzero does not mean large

**Result.** Rational radical coordinates detect exact zero. They do not estimate the size of one chosen real embedding.

Let $P$ be a finite set of distinct primes, $K=\mathbb Q(\sqrt p:p\in P)$, and

$$
q_A=\prod_{p\in A}p,\qquad e_A=\sqrt{q_A}\quad(A\subseteq P).
$$

The $e_A$ form a rational basis. Every assignment $\varepsilon_p\in\{-1,1\}$ extends to a field automorphism $\sigma_\varepsilon$.

Here is a finite induction proof. Suppose the assertion holds for the old primes. If $\sqrt p$ for a new prime lay in their field, each old automorphism would send it to $\pm\sqrt p$. Those signs form a character of the old sign group. Expanding in the old basis and using finite character orthogonality puts $\sqrt p$ in one character eigenspace: $\sqrt p=c e_A$ for rational $c$. Squaring and taking the valuation at the new prime gives $1=2v_p(c)$, impossible. The degree therefore doubles, and either sign of the new root extends every old automorphism.

If $z=\sum_A z_Ae_A$, $z_A\in\mathbb Q$, the finite projector is

$$
2^{-|P|}\sum_\varepsilon
 \left(\prod_{p\in A}\varepsilon_p\right)\sigma_\varepsilon(z)=z_Ae_A.
$$

Hence $z=0$ exactly when every coordinate vanishes. Also

$$
2^{-|P|}\sum_\varepsilon\sigma_\varepsilon(z)\sigma_\varepsilon(w)
 =\sum_A z_Aw_Aq_A.
$$

This average ranges over finitely many algebraic embeddings. It does not bound the single embedding with all square roots positive.

## A finite nonvanishing example

For the quarter-mask sum

$$
H=\sum_{d\le4M}\frac{\mu(d)S_d}{\sqrt d},
$$

only squarefree $d$ survive, and its $\sqrt d$-coordinate is $\mu(d)S_d/d$.

At $d=2$, $\mu(2)S_2$ is the number of odd integers in $(M-k,M]$. It is positive for $M\ge16$, when $k\ge2$, and for odd $8\le M\lt 16$. The remaining small even cases have these nonzero coefficients:

| $M$ | $d$ | $\mu(d)S_d$ |
|---:|---:|---:|
| 8 | 3 | 1 |
| 10 | 3 | −1 |
| 12 | 5 | −1 |
| 14 | 3 | 1 |

Thus $H\ne0$ for every integer $M\ge8$. This says nothing quantitative about $|H|$, and it is not determinant nonvanishing. This rational-coordinate argument also does not apply to arbitrary nonalgebraic kernel weights.
