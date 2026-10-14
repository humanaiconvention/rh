# Finite Möbius convolution: exact identity, unestimated pairing

**Result.** A balanced finite convolution can eliminate its residual exactly. It still reproduces every original Möbius coefficient, so it does not by itself improve the arithmetic bound.

Work in the coefficient algebra on $1,\ldots,B$:

$$
(f*g)(n)=\sum_{ab=n}f(a)g(b)\quad(n\le B).
$$

Write $\mathbf1(n)=1$, $\delta(1)=1,\delta(n)=0$ for $n\gt 1$.
Let $1\le Z\le B$, $u=\mu\,1_{n\le Z}$, $v=\mu\,1_{n\gt Z}$.
Finite divisor inversion gives $\mu*\mathbf1=\delta$.

For every integer $h_0\ge1$,

$$
\boxed{
\mu=\sum_{h=1}^{h_0}(-1)^{h-1}\binom{h_0}{h}
 u^{*h}*\mathbf1^{*(h-1)}
 +v^{*h_0}*\mathbf1^{*(h_0-1)}.
}
$$

Indeed $\delta-u*\mathbf1=v*\mathbf1$; expand its $h_0$-th power and convolve with $\mu$. Associativity counts finite ordered factorizations only.

The residual coefficient at $n$ is

$$
\sum_{\substack{d_1,\ldots,d_{h_0}\gt Z,\ r_1,\ldots,r_{h_0-1}\ge1\\
d_1\cdots d_{h_0}r_1\cdots r_{h_0-1}=n}}
 \mu(d_1)\cdots\mu(d_{h_0}).
$$

It vanishes for every $n\le B$ if $(Z+1)^{h_0}\gt B$. Strict inequality matters: equality can leave a nonzero coefficient.

## Balanced cubic form

For the bulk $G=\sum_{d\le B}\mu(d)S_d/\sqrt d$, choose
$h_0=3$, $Z=\lfloor B^{1/3}\rfloor$. The residual is zero. Define, with zero extension when $q\gt B$,

$$
\Psi_2(q)=\sum_{r\le B/q}\frac{S_{qr}}{\sqrt r},
\qquad
\Psi_3(q)=\sum_{r\le B/q}\frac{\tau(r)S_{qr}}{\sqrt r},
$$

where $\tau(r)=\#\{(a,b)\in\mathbb N^2:ab=r\}$. Then

$$
\begin{aligned}
G&=3A_1-3A_2+A_3,\\
A_1&=\sum_{a\le Z}\frac{\mu(a)S_a}{\sqrt a},\\
A_2&=\sum_{a,b\le Z}\frac{\mu(a)\mu(b)}{\sqrt{ab}}\Psi_2(ab),\\
A_3&=\sum_{a,b,v\le Z}\frac{\mu(a)\mu(b)\mu(v)}{\sqrt{abv}}\Psi_3(abv).
\end{aligned}
$$

The multiplicity $\tau(r)$ is mandatory. Product cutoffs and the original mask phases remain inside both $\Psi$ sums.

## Where an estimate is still needed

The coefficientwise identity is

$$
3u-3u*u*\mathbf1+u*u*u*\mathbf1*\mathbf1=\mu\qquad(n\le B).
$$

It restores every original signed coefficient, including squareful cancellations. Estimating the terms separately can lose this compensation. A useful further theorem must bound the **complete signed product-history pairing**, rather than merely increase the number of convolution factors.

This is standard finite binomial and Möbius algebra, presented with its residual and support explicitly exposed.
