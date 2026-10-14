# Lemma 002: a terminal arithmetic criterion and an envelope obstruction

**Abstract.** A fourth-root estimate for a finite Möbius-weighted floor sum is quantitatively equivalent to a square-root estimate for its complete periodic endpoint expression. For a specified anchored pointwise-envelope certificate, we prove a flat-sector cost exceeding $`\sqrt M/(2\log^2(3M))`$. This lower bound concerns the certificate, not the signed arithmetic sum or a physical mass.

## 1. Finite definitions

All logarithms are natural. Let $`\mu`$ be the ordinary Möbius function and let $`M\ge8`$ be an integer. Set
```math
k=\lfloor M^{1/4}\rfloor,\qquad L=M-k,\qquad B=4L,\qquad T=4M.
```
Define
```math
a(n)=\sum_{d\mid n}\frac{\mu(d)}{\sqrt d}
=\prod_{p\mid n}(1-p^{-1/2}),\qquad
A(X)=\sum_{n\le X}a(n),
```
```math
b_d(j)=\left\lfloor\frac{4j}{d}\right\rfloor
-3\left\lfloor\frac{2j}{d}\right\rfloor
+2\left\lfloor\frac jd\right\rfloor,\qquad
S_d=\sum_{j=L+1}^{M}b_d(j).
```
For $`1\le j\le M`$, finite divisor counting gives
```math
r_j:=A(4j)-3A(2j)+2A(j)
=\sum_{d\le T}\frac{\mu(d)b_d(j)}{\sqrt d}.
```
Write
```math
q_M=r_M,\qquad H=\sum_{j=L+1}^{M}r_j,\qquad
G=\sum_{d\le B}\frac{\mu(d)S_d}{\sqrt d}.
```
All floor endpoints are literal. No arithmetic coefficient beyond $`T`$ is used.

The period mean and centered prefix are
```math
\bar b_d=\frac1d\sum_{n=1}^{d}b_d(n)
=\frac{\gcd(4,d)-3\gcd(2,d)+2}{2d},\qquad
c_d(r)=\sum_{n=1}^{r}(b_d(n)-\bar b_d)
\quad(0\le r\le d).
```
Thus $`c_d(0)=c_d(d)=0`$. Define the full primitive at cutoff $`B`$ by
```math
\bar\Phi_B=\sum_{d\le B}\frac{\mu(d)\bar b_d}{\sqrt d},\qquad
u_M(n)=\sum_{d\le B}\frac{\mu(d)}{\sqrt d}
c_d((n-1)\bmod d),\qquad
E_M=u_M(M+1)-u_M(L+1).
```
Periodic telescoping gives the exact identity
```math
G=k\bar\Phi_B+E_M. \tag{1}
```

For nonnegative constants $`C_Q,C_E`$, consider the assertions
```math
\mathrm Q(C_Q):\quad
|A(4M)-3A(2M)+2A(M)|\le C_QM^{1/4}
\quad\text{for every integer }M\ge8,
```
```math
\mathrm{EP}(C_E):\quad
|E_M|\le C_E\sqrt M
\quad\text{for every integer }M\ge8.
```
Neither assertion is established here.

## 2. Quantitative equivalence

**Proposition 1.**
```math
\mathrm Q(C_Q)\ \Longrightarrow\ \mathrm{EP}(C_Q+5),
\qquad
\mathrm{EP}(C_E)\ \Longrightarrow\ \mathrm Q(2C_E+7).
\tag{2}
```

**Proof.** The finite product defining $`a(n)`$ gives $`0\lt a(n)\le1`$. Consequently
```math
r_{j+1}-r_j
=\sum_{n=4j+1}^{4j+4}a(n)
-3\bigl(a(2j+1)+a(2j+2)\bigr)+2a(j+1)
\in[-6,6].
```
Therefore
```math
H=kq_M+\eta_M,\qquad
\eta_M:=\sum_{j=L+1}^{M}(r_j-r_M),\qquad
|\eta_M|\le3k(k-1). \tag{3}
```

For $`B\lt d\le T`$, the mask equals $`1`$ precisely when $`j\ge\lceil d/4\rceil`$ within the given window. Hence
```math
H=G+C_{\mathrm{cap}},\qquad
C_{\mathrm{cap}}
=\sum_{B\lt d\le T}\frac{\mu(d)}{\sqrt d}
\bigl[M-\lceil d/4\rceil+1\bigr].
```
The bracket takes the values $`k,k-1,\ldots,1`$, each four times. Since $`k\le M/4`$ and $`L\ge3M/4`$,
```math
|C_{\mathrm{cap}}|
\le\frac{2k(k+1)}{\sqrt{4L+1}}
\le\frac2{\sqrt3}(1+M^{-1/4})
\lt\frac{16}{5\sqrt3}\lt2. \tag{4}
```
Here $`M^{-1/4}\le8^{-1/4}\lt3/5`$.

Period counting gives $`\bar b_d=-1/d`$ for $`d\equiv2\pmod4`$ and zero otherwise. With $`R=\lfloor B/2\rfloor`$, finite integral comparison yields
```math
|\bar\Phi_B|
\le2^{-3/2}\sum_{n=1}^{R}n^{-3/2}
\le2^{-3/2}\left(1+\int_1^R t^{-3/2}\,dt\right)
\le K_0:=\frac3{2\sqrt2}. \tag{5}
```
The mean formula follows, for example, by applying
```math
\sum_{n=0}^{d-1}\left\lfloor\frac{an}{d}\right\rfloor
=\frac{(a-1)(d-1)+\gcd(a,d)-1}{2}
```
to $`a=4,2,1`$; periodicity permits the same period sum from $`1`$ to $`d`$.

Combining the complete identities before estimating gives
```math
E_M=kq_M+\eta_M-C_{\mathrm{cap}}-k\bar\Phi_B. \tag{6}
```
If $`\mathrm Q(C_Q)`$ holds, then $`k\le M^{1/4}`$ and $`2\le\sqrt M/\sqrt2`$ imply
```math
|E_M|
\le\left(C_Q+3+\frac5{2\sqrt2}\right)\sqrt M
\lt(C_Q+5)\sqrt M.
```
Conversely, $`\mathrm{EP}(C_E)`$ gives
```math
|H|\le C_E\sqrt M+K_0k+2\lt(C_E+2)\sqrt M.
```
Using $`k\ge M^{1/4}/2`$ in (3),
```math
|q_M|\le |H|/k+3(k-1)
\le(2C_E+7)M^{1/4}.
```
This proves (2), with the cap and full discrete mean retained. ∎

## 3. The specified anchored envelope certificate

Let
```math
\mathfrak m(x)=\sum_{n\le x}\mu(n)\quad(x\ge0),\qquad
g_M(d)=\frac{b_d(M)}{\sqrt d}\quad(1\le d\le T),
\qquad g_M(T+1)=0.
```
The zero extension adds no arithmetic coefficient. Since $`g_M(1)=0`$, finite summation by parts gives, for any common scalar $`\theta`$,
```math
q_M=\sum_{d=1}^{T}
[\mathfrak m(d)-\theta]\,[g_M(d)-g_M(d+1)]. \tag{7}
```
Indeed, the unshifted formula is finite Abel summation, and
$`\sum_{d=1}^T[g_M(d)-g_M(d+1)]=0`$ removes the scalar.

Johnston–Leong–Tudzi [1, Theorem A.1, (A.5)] prove
```math
|\mathfrak m(x)|\le \frac{2.91890\,x}{(\log x)^2}
\qquad(x\gt1).
```
We use only the weaker envelope
```math
e(1)=1,\qquad e(t)=\frac{3t}{(\log t)^2}\quad(t\gt1).
```
Choose $`\theta=\mathfrak m(T)`$. The prefix envelope and the native unit-increment bound $`|\mu(n)|\le1`$ imply
```math
|\mathfrak m(d)-\mathfrak m(T)|
\le\mathcal E_T(d):=\min\{T-d,\ e(d)+e(T)\}.
\tag{8}
```
Applying absolute values in (7) and then (8) gives the specified certificate
```math
|q_M|\le
\sum_{d=1}^{T}|\mathfrak m(d)-\mathfrak m(T)|
\,|g_M(d)-g_M(d+1)|
\le\mathcal B_Q(M),
```
```math
\mathcal B_Q(M):=
\sum_{d=1}^{T}\mathcal E_T(d)
\,|g_M(d)-g_M(d+1)|. \tag{9}
```
The result below concerns this explicitly defined majorant. It is not a statement about every possible use of the prefix bound.

## 4. Flat-sector obstruction

**Proposition 2.** For every integer $`M\ge\exp(4)`$,
```math
\boxed{\mathcal B_Q(M)\gt
\frac{\sqrt M}{2[\log(3M)]^2}.} \tag{10}
```
Consequently $`\mathcal B_Q(M)/M^{1/4}\to\infty`$. The certificate (9) cannot prove $`\mathrm Q(C_Q)`$ with a constant independent of $`M`$.

**Proof.** For $`2M\lt d\le4M`$, the literal floors give $`b_d(M)=1`$. Thus for $`2M+1\le d\le3M-1`$,
```math
g_M(d)-g_M(d+1)
=d^{-1/2}-(d+1)^{-1/2}\gt0. \tag{11}
```
The function $`e(t)`$ is increasing for $`t\gt\exp(2)`$, since
```math
e'(t)=\frac{3(\log t-2)}{(\log t)^3}.
```
On this sector, $`M\ge\exp(4)`$ therefore implies
```math
e(d)\le e(3M)=\frac{9M}{[\log(3M)]^2}
\lt M\le T-d.
```
Both entries of the minimum in (8) are at least $`e(d)`$. Restricting the nonnegative cost (9) to this sector and telescoping,
```math
\begin{aligned}
\mathcal B_Q(M)
&\ge\sum_{d=2M+1}^{3M-1}
\frac{3d}{(\log d)^2}
\bigl[d^{-1/2}-(d+1)^{-1/2}\bigr]\\
&\ge\frac{6M}{[\log(3M)]^2}
\left[(2M+1)^{-1/2}-(3M)^{-1/2}\right].
\end{aligned}
```
For $`M\ge8`$, $`2M+1\le(17/8)M`$. The exact comparisons
```math
\sqrt{\frac8{17}}\gt\frac23,\qquad
\frac1{\sqrt3}\lt\frac7{12}
```
give
```math
(2M+1)^{-1/2}-(3M)^{-1/2}
\gt\frac1{12\sqrt M}.
```
This proves (10). Finally,
```math
\frac{\mathcal B_Q(M)}{M^{1/4}}
\gt\frac{M^{1/4}}{2[\log(3M)]^2}\longrightarrow\infty.
```
All arithmetic sums in the proof have finite limits. ∎

## 5. Scope

Proposition 1 establishes a conditional equivalence; it proves neither uniform arithmetic assertion. Proposition 2 is a lower bound on the **specified envelope cost**. It gives no growing lower bound on $`q_M`$, $`G`$, $`E_M`$, or an associated physical mass. It does not even show that the intermediate cost using the actual absolute relative prefixes in (9) has this growth.

The unresolved estimate is the signed pairing (7) with $`\theta=\mathfrak m(T)`$ at fourth-root precision. Cancellation between its quotient cells and boundary phases remains possible. No obstruction to every signed use of the Johnston–Leong–Tudzi theorem, no actual lower fluctuation, and no consequence for the Riemann hypothesis is asserted. The finite Abel and increment arguments are elementary; no research novelty is claimed.

## Reference

[1] Daniel R. Johnston, Nicol Leong, and Sebastian Tudzi,
*New bounds and progress towards a conjecture on the summatory function of* $`(-2)^{\Omega(n)}`$,
[arXiv:2408.04143v3](https://arxiv.org/pdf/2408.04143v3), version submitted 8 September 2024, Theorem A.1, equation (A.5).
