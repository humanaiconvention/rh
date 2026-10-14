# A finite GCD kernel and the centering obstruction

**Result.** Nonnegative weights have a nonpositive complete uncentered cross term. Centering adds two explicit positive companions and can reverse that sign.

Let $N\ge1$, $P$ be a finite prime set, and $\Pi=\prod_{p\in P}p$. For real vectors $u,v$ on $1,\ldots,N$, define

$$
a_P(n)=\prod_{\substack{p\in P\\p\mid n}}(1-p^{-1/2}),\qquad
K_{P,r}(u)=\sum_{rm\le N}a_P(m)u_{rm}\quad((r,\Pi)=1),
$$

$$
a(n)=\prod_{p\mid n}(1-p^{-1/2}),\qquad
A(u)=\sum_{n\le N}a(n)u_n,\qquad F(u)=\sum_{n\le N}u_n.
$$

Finite Möbius inversion gives $A(u)=\sum_{(r,\Pi)=1}\mu(r)K_{P,r}(u)/\sqrt r$.

## Closed product and sign theorem

The uncentered grouped diagonal is exactly

$$
\boxed{
D_P^u(u,v)=
\sum_{n,m\le N}u_nv_m\,a_P(n)a_P(m)
 \prod_{\substack{p\mid\gcd(n,m)\\p\notin P}}(1+p^{-1}).
}
$$

Proof: expand
$\sum_{(r,\Pi)=1}\mu(r)^2K_{P,r}(u)K_{P,r}(v)/r$.
For $r\mid n$ coprime to $\Pi$, $a_P(n/r)=a_P(n)$. The remaining finite sum over squarefree divisors of $\gcd(n,m)$ factors into the displayed product.

For $u,v\ge0$, $a_P(n)\ge a(n)\gt 0$ and the GCD product is at least one. Coefficientwise,

$$
D_P^u(u,v)\ge A(u)A(v),\qquad
Y_P^u(u,v):=A(u)A(v)-D_P^u(u,v)\le0.
$$

This uses neither a Gram argument nor a Möbius-correlation estimate.

## Exact centered compensation

Fix a real scalar $c$, and center $V(u)=A(u)-cF(u)$. Allocate the scalar **only to the $r=1$ row**:

$$
L_1(u)=K_{P,1}(u)-cF(u),\qquad L_r(u)=K_{P,r}(u)\quad(r\gt 1).
$$

Let $D_P^c=\sum_{(r,\Pi)=1}\mu(r)^2L_r(u)L_r(v)/r$. Expanding with both weights retained gives

$$
\boxed{
Y_P^c:=V(u)V(v)-D_P^c
 =Y_P^u+
 c[F(u)(K_{P,1}(v)-A(v))+F(v)(K_{P,1}(u)-A(u))].
}
$$

The scalar square cancels exactly in this subtraction; both linear companions survive. If $c\ge0$ and $u,v\ge0$, the added terms are nonnegative. Replacing $a_P(n)$ by $a_P(n)-c$ in every divisor row would give a different expression.

## A literal two-row counterexample

Take $N\ge6$, $P=\{2\}$, $c=1/2$, and $u=v$ with $u_6=1$, all other entries zero. Put $a_2=1-1/\sqrt2$. The only nonzero signed rows $\mu(r)L_r/\sqrt r$ are

$$
z_1=a_2-\tfrac12,\qquad z_3=-a_2/\sqrt3.
$$

Their product matrix is

$$
\begin{pmatrix}
(a_2-\tfrac12)^2&(\tfrac12-a_2)a_2/\sqrt3\\
(\tfrac12-a_2)a_2/\sqrt3&a_2^2/3
\end{pmatrix}.
$$

Thus

$$
Y_{\{2\}}^c=2(\tfrac12-a_2)a_2/\sqrt3\gt 0.
$$

Adding prime $3$ leaves only the $r=1$ row, so the diagonal increases by exactly this amount while the complete mass stays fixed.

This is a self-contained finite sign counterexample. The same algebra holds for two vectors supported at $6$, with distinct positive values $F_1,F_2$, after multiplying every entry by $F_1F_2$. The [actual kernel](kernel-calculus.md) at $N=10$, shifts $x_1=13/2,x_2=7$, and integer sample support $N/2\lt n\lt x_i$, supplies such values. This specialization uses the freely stated scalar $c=1/2$; it does not assert a value for any external normalization.

A positive cross term at one cutoff defeats a universal sign shortcut. It supplies no asymptotic lower fluctuation.
