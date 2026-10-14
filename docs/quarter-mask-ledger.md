# Quarter-mask sum: cancellation without a mean bound

**Result.** The terminal cap is bounded by $2$, and the short-window variance is at most $3M^{3/4}$. Neither result estimates the signed mean.

Fix an integer $M\ge8$, and set

$$
k=\lfloor M^{1/4}\rfloor,\qquad L=M-k,\qquad J_c=4M,\qquad B=4L.
$$

Here $J_c$ is the horizon of this auxiliary floor sum, not an operator cutoff. Let $\mu$ be the ordinary Möbius function. Define

$$
b_d(j)=\left\lfloor\frac{4j}{d}\right\rfloor
 -3\left\lfloor\frac{2j}{d}\right\rfloor
 +2\left\lfloor\frac jd\right\rfloor,\qquad
S_d=\sum_{j=L+1}^{M}b_d(j).
$$

Writing $j/d=q+\theta$, the integer $q$ cancels. The mask is

$$
b_d(j)=\mathcal B(\theta),\qquad
\mathcal B(\theta)=
\begin{cases}
0&0\le\theta\lt 1/4,\\
1&1/4\le\theta\lt 1/2,\\
-1&1/2\le\theta\lt 3/4,\\
0&3/4\le\theta\lt 1.
\end{cases}
$$

Thresholds belong to the cell on their right.

## Exact finite mean and variance

Put

$$
a(n)=\sum_{d\mid n}\frac{\mu(d)}{\sqrt d}
 =\prod_{p\mid n}(1-p^{-1/2}),\qquad
A(x)=\sum_{n\le x}a(n),
$$

$$
r_j=A(4j)-3A(2j)+2A(j),\qquad H=\sum_{j=L+1}^{M}r_j.
$$

Finite reindexing gives

$$
r_j=\sum_{d\le J_c}\frac{\mu(d)b_d(j)}{\sqrt d},
\qquad H=\sum_{d\le J_c}\frac{\mu(d)S_d}{\sqrt d}.
$$

Since $0\lt a(n)\le1$,

$$
r_{j+1}-r_j
 =\sum_{n=4j+1}^{4j+4}a(n)
 -3\bigl(a(2j+1)+a(2j+2)\bigr)+2a(j+1)
 \in[-6,6].
$$

The exact pairwise variance identity therefore yields

$$
W:=\sum_{j=L+1}^{M}(r_j-H/k)^2
 =\frac1k\sum_{L\lt i\lt j\le M}(r_i-r_j)^2
 \le3k(k^2-1)\le3M^{3/4}.
$$

For completeness, its joint divisor form is

$$
W=\sum_{d,e\le J_c}\frac{\mu(d)\mu(e)}{\sqrt{de}}
 \left[\sum_{j=L+1}^{M}b_d(j)b_e(j)-\frac{S_dS_e}{k}\right].
$$

Both divisor variables remain. The variance controls oscillation about the unknown mean; a constant sequence can have zero variance and any mean.

## Common-prefix and boundary cancellation

Let $F(d)=S_d/\sqrt d$, $F(J_c+1)=0$, and
$\mathfrak m(d)=\sum_{n\le d}\mu(n)$. Since $F(1)=0$, finite summation by parts gives, for any common scalar $\theta$,

$$
H=\sum_{d=1}^{J_c}[\mathfrak m(d)-\theta][F(d)-F(d+1)].
$$

The subtracted constant telescopes to zero. It does not impose a sign on the remaining summands.

At a split $1\le D\lt J_c$, the two pieces are exactly

$$
\sum_{d\le D}\mu(d)F(d)-\mathfrak m(D)F(D+1),
\quad
\sum_{D\lt d\le J_c}\mu(d)F(d)+\mathfrak m(D)F(D+1).
$$

The attached boundary phases cancel only when both pieces are retained.

## Uniform terminal cap

Write $H=G+C$, where

$$
G=\sum_{d\le B}\frac{\mu(d)S_d}{\sqrt d},\qquad
C=\sum_{B\lt d\le4M}\frac{\mu(d)[M-\lceil d/4\rceil+1]}{\sqrt d}.
$$

On this cap the bracket takes the values $k,k-1,\ldots,1$, each four times. Consequently

$$
|C|\le\frac{2k(k+1)}{\sqrt{4L+1}}\lt 2.
$$

This supporting estimate may use absolute values on the cap; it does not do so on the unresolved bulk $G$. To verify the strict constant, use $L\ge3M/4$, $k\le M^{1/4}$, and $M^{-1/4}\le8^{-1/4}\lt 3/5$:

$$
\frac{2k(k+1)}{\sqrt{4L+1}}
 \le\frac2{\sqrt3}(1+M^{-1/4})
 \lt \frac{16}{5\sqrt3}\lt 2.
$$

Thus $|H|\le C_H\sqrt M$ and $|G|\le C_G\sqrt M$ are equivalent up to constants. Both remain open here.
