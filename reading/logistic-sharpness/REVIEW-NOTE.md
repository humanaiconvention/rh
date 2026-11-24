# A sharp bound for a signed lattice convolution with logistic smoothing

**Status.** This is a reading copy for human review on a public review branch, not a release or a novelty claim. Its literal theorem has local Lean acceptance at pinned sources; strict isolated comparator replay and external human review are pending. The proof below concerns one explicit pair of infinite Radon banks. It asserts no Möbius, theta/zeta or RH consequence.

## Statement

For every positive real \(L\), set
\[
h_L(x)=e^{-x}(1+e^{x/L})^{-L},\quad
p=\sum_{k=0}^{\infty}\delta_{-2k},\quad
n=\frac14\sum_{k=0}^{\infty}\delta_{-(2k+1)}.
\]
Define the original, untruncated quotient
\[
Q_L(v)=\frac{\int h_L(v-u)\,dp(u)-\int h_L(v-u)\,dn(u)}{h_L(v)}.
\]
Both bank masses are infinite, but every displayed convolution integral is separately finite. Put
\[
q=e^{-1},\quad A=\frac{1-q^2/4}{1-q^4},\quad
b=1-q/4,\quad C=b+q^3A.
\]
Then
\[
\boxed{Q_L(v)>C\quad\text{for every real }L>0,\ v\in\mathbb R,}
\qquad
Q_{1/(n+1)}(-1)\longrightarrow C\quad(n\to\infty).
\]
Consequently \(C\) is the exact uniform infimum, not attained at any finite positive width or location. More explicitly, for every real \(B\),
\[
[\ B\le Q_L(v)\text{ for all }L>0,v\ ]\quad\Longleftrightarrow\quad B\le C.
\]
This is a strict bound at every pair \((L,v)\), not a positive uniform gap above \(C\).

## 1. Properness and the hinge minimum

Let \(H(x)=e^{-x}\min(1,e^{-x})\). Both \(h_L(x)\) and \(H(x)\) are positive and at most \(e^{-x}\). Since
\[
\int e^u\,dp=\frac1{1-q^2},\qquad
\int e^u\,dn=\frac{q}{4(1-q^2)},
\]
all bank convolutions below converge absolutely for each fixed location. No subtraction of infinite total masses is used.

Write \(S(v)=\sum_{k\ge0}H(v+2k)\) and
\(Q_H(v)=(S(v)-S(v+1)/4)/H(v)\). Splitting only the actual \(k=0\) term and summing geometric tails gives
\[
Q_H(v)=
\begin{cases}
A,&v\ge0,\\
1+e^{-v}(A-1),&-1\le v\le0,\\
b+e^{-v-4}A,&-2\le v\le-1.
\end{cases}
\]
The endpoint values agree. Because \(0<q<1/2\), we have \(0<A<1\). The middle piece is strictly increasing and the lower piece strictly decreasing. Their common minimum at \(-1\) is \(C\); the identity there follows from \(A(1-q^4)=1-q^2/4\).

For \(v\le-2\), the exact recursion is
\[
Q_H(v)=b+q^2Q_H(v+2).
\]
Moreover \(b+q^2C-C=q^2(C-qA)>0\), since \(C>b>7/8\) and \(qA<1/2\). Every real \(v<-2\) reaches \([-2,0]\) after finitely many such translations. Iterating this recursion proves \(Q_H(v)>C\) there. Thus
\[
Q_H(v)\ge C,\qquad Q_H(v)=C\iff v=-1
\]
on the whole real line, not just a tested interval.

**An exact check retaining the first atoms.** At \(v=-1\),
\[
\int H(-1-u)\,dp=q^{-1}+\frac{q^2}{1-q^4},\quad
\int H(-1-u)\,dn=\frac1{4(1-q^4)},\quad H(-1)=q^{-1}.
\]
The positive first atom contributes \(q^{-1}\); the negative first atom is the transition value \(H(0)/4=1/4\). The quotient is \(1+(q^3-q/4)/(1-q^4)=C\). Each series converges before subtraction.

## 2. A positive mixture transfers the minimum, strictly

For \(r>0\), put
\[
w_L(r)=(L+1)(1+r)^{-L-2},\qquad t=L\log r.
\]
This is a positive probability density, and the literal identity is
\[
h_L(x)=\int_0^\infty e^{-t}H(x-t)w_L(r)\,dr. \tag{1}
\]
To check it, let \(a=e^{x/L}\) and use
\(e^{-t}H(x-t)=e^{-x}\min(1,e^{-x}r^L)\). Split at \(a\). Antiderivatives of the two pieces are supplied by
\(- (1+r)^{-L-1}\) and \(r^{L+1}(1+r)^{-L-1}\). Their respective endpoint values give
\[
e^{-2x}a^{L+1}(1+a)^{-L-1}+e^{-x}(1+a)^{-L-1}=h_L(x).
\]
All improper endpoints are controlled by \(L>0\). The value at \(r=0\) is immaterial because the integration domain is open and the endpoint is null; no original lattice atom is removed.

For either bank separately, the full integrand of (1) with \(x=v-u\) is bounded by \(e^{-v+u}w_L(r)\), which has finite product integral. Thus Fubini is justified separately before subtraction. After normalizing, (1) yields
\[
Q_L(v)=\int_0^\infty W_{L,v}(r)Q_H(v-L\log r)\,dr,\quad
W_{L,v}(r)=\frac{e^{-t}H(v-t)w_L(r)}{h_L(v)}.
\]
Here \(W_{L,v}>0\) and \(\int W_{L,v}=1\). Properness of both bank terms also controls the absolute integral of the signed quotient in this identity. The hinge minimum proves \(Q_L(v)\ge C\). Equality could occur only where \(r=e^{(v+1)/L}\); this is one Lebesgue-null point. Therefore the integrable nonnegative gap is positive almost everywhere on a set of positive measure, and \(Q_L(v)>C\).

One must not assume that the unnormalized measure \(e^{-t}w_L(r)dr\) is finite: for \(L\ge1\) it is not. The full products and the normalized weight above are the proper objects.

## 3. The width limit proves sharpness

For every positive \(L\) and every real \(x\),
\[
2^{-L}H(x)\le h_L(x)\le H(x).
\]
For \(x\le0\), the remaining base \(1+e^{x/L}\) lies in \([1,2]\). For \(x\ge0\), factor it to write
\(h_L(x)=e^{-2x}(1+e^{-x/L})^{-L}\), with the same base bounds. This includes \(x=0\), where \(h_L(0)=2^{-L}\).

Along \(L_n=1/(n+1)\), every width is positive, including \(L_0=1\), and \(2^{-L_n}\to1\). Squeezing gives pointwise convergence to \(H\). At \(v=-1\), dominated convergence applies to each original bank separately with majorant \(H(-1-u)\). Subtract the resulting finite limits, then divide by the nonzero denominator limit \(H(-1)=e\). Hence \(Q_{L_n}(-1)\to C\). Any uniform lower bound is at most this limit, which proves the asserted optimality.

This argument never substitutes \(L=0\) into the raw formula. Its Lean-totalized value at zero width is \(e^{-x}\), not \(H(x)\) for \(x>0\). No convergence rate or uniform-in-location convergence is asserted.

## Review scope

The exact public theorem, definition map, source pins and evidence tiers are in [CLAIM-MAP.md](CLAIM-MAP.md). The source-only replay plan is in [REPLAY.md](REPLAY.md). The general signed-measure criterion, exact three-atom cutoff, theta/zeta application and any actual Möbius claim are separate. This note makes no priority claim: it packages a concrete sharp example and its local formalization. The proof and its use remain subject to human mathematical review.
