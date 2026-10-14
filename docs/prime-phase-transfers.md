# Prime phases: exact transfers, no automatic damping

**Result.** Prime regrouping preserves the whole signed mass. It transfers energy between a grouped diagonal and its complete cross term; that transfer can have either sign.

Use $`M,L,B,S_d,G`$ from [the quarter-mask note](quarter-mask-ledger.md). Write $`j/d=q+\theta`$, $`0\le\theta\lt 1`$, and $`h=q\bmod p`$. Then

```math
b_{pd}(j)=\mathcal B((h+\theta)/p).
```

The columns below are the four half-open quarter cells of $`\theta`$, in order.

| $`p`$ | $`h`$ | phase values |
|---|---:|---|
| 2 | 0 | 0, 0, 1, 1 |
| 2 | 1 | −1, −1, 0, 0 |
| 3 | 0 | 0, 0, 0, 1 |
| 3 | 1 | 1, 1, −1, −1 |
| 3 | 2 | −1, 0, 0, 0 |
| 5 | 0 | 0, 0, 0, 0 |
| 5 | 1 | 0, 1, 1, 1 |
| 5 | 2 | 1, 1, −1, −1 |
| 5 | 3 | −1, −1, −1, 0 |
| 5 | 4 | 0, 0, 0, 0 |

Hence $`b_d(j)b_{2d}(j)\le0`$ and $`b_d(j)b_{3d}(j)\ge0`$. These are same-$`j`$ statements only:

```math
S_dS_{pd}
 =\sum_j b_d(j)b_{pd}(j)
 +\sum_{j\ne\ell}b_d(j)b_{pd}(\ell).
```

The distinct-history terms prevent either cell sign from becoming a global sign theorem.

## Grouping with every cutoff tail retained

Let $`P`$ be a finite prime set and $`\Pi=\prod_{p\in P}p`$. For $`(r,\Pi)=1`$, define

```math
K_{P,r}=\sum_{\substack{b\mid\Pi\\br\le B}}
 \frac{\mu(b)S_{br}}{\sqrt b}.
```

Set $`K_{P,r}=0`$ for $`r\gt B`$. Unique separation of the primes in $`P`$ gives

```math
G=\sum_{\substack{r\le B\\(r,\Pi)=1}}
 \frac{\mu(r)K_{P,r}}{\sqrt r}.
```

For two distinct histories $`u,v`$, with a common finite horizon and zero extension outside their respective supports, put

```math
D_P(u,v)=\sum_{(r,\Pi)=1}\frac{\mu(r)^2K_{P,r}(u)K_{P,r}(v)}r,
```

```math
Y_P(u,v)=\sum_{\substack{r\ne t\\(rt,\Pi)=1}}
 \frac{\mu(r)\mu(t)K_{P,r}(u)K_{P,t}(v)}{\sqrt{rt}}.
```

Then $`G(u)G(v)=D_P(u,v)+Y_P(u,v)`$. No weights or delays have been identified.

For a new prime $`p\notin P`$, the exact two-history transfer is

```math
K_{P\cup\{p\},q}=K_{P,q}-p^{-1/2}K_{P,pq},
```

```math
D_{P\cup\{p\}}(u,v)-D_P(u,v)
 =-\frac1{\sqrt p}
 \sum_{(q,p\Pi)=1}\frac{\mu(q)^2}{q}
 [K_{P,q}(u)K_{P,pq}(v)+K_{P,pq}(u)K_{P,q}(v)].
```

It follows by expanding the new product and canceling its $`p^{-1}`$ corner against the old $`pq`$-row. All sums stop at the horizon. In particular, when $`pq\gt B`$, the original $`q`$-row is retained unchanged. The cross term has the opposite transfer.

For a single history and distinct new primes $`p,q`$, the mixed transfer is

```math
\begin{aligned}
\Omega_{p,q\mid P}
&:=D_{P\cup\{p,q\}}-D_{P\cup\{p\}}-D_{P\cup\{q\}}+D_P\\
&=\frac2{\sqrt{pq}}\sum_{(r,pq\Pi)=1}\frac{\mu(r)^2}{r}
 [K_{P,r}K_{P,pqr}+K_{P,pr}K_{P,qr}].
\end{aligned}
```

Expanding the four grouped energies proves this identity with the same zero extensions. It is a signed four-corner aggregate, not independent prime estimates.

The whole square stays fixed. [Reproducible finite intervals](../data/finite-measurements.md) show positive and negative transfers, ruling out universal prime damping. They do not decide the open uniform bound.
