# Singular kernel: positivity and a bounded inverse bridge

**Result.** The kernel is positive on the recent-index support. An exact Volterra bridge replaces its changing derivative by a monotone quarter-root kernel, with inverse cost below $`24/19`$. This fixes a geometric issue; it does not estimate the signed arithmetic history.

Fix $`C\gt 0`$. For $`v\ge0`$, set $`z=e^{-2v}`$ and

```math
A(z)=\int_z^1 r^{1/8}(1-r)^{-3/4}\,dr,\quad
B(z)=\int_z^1 r^{1/4}(1-r)^{-3/4}\,dr,
```

```math
\beta(v)=C[3A(z)-2e^{v/4}B(z)],\qquad
f_x(t)=t^{-1/4}\beta(\log(x/t))\quad(0\lt t\lt x),
```

and $`f_x(t)=0`$ for $`t\ge x`$. All integrals converge at $`r=1`$.

## Positivity on the actual ratio range

For $`a\le t\lt x\le2a`$, $`z=(t/x)^2\ge1/4`$. With
$`R=1-(1-z)u^4`$, substitution gives

```math
\frac{f_x(t)}C
 =4t^{-1/4}(1-z)^{1/4}
 \int_0^1 R^{1/8}[3-2(R/z)^{1/8}]\,du.
```

Since $`z\le R\le1`$ and $`2^{1/4}\lt 3/2`$, the integrand is positive. Thus $`f_x(t)\gt 0`$ for $`a\le t\lt x`$.

At fixed $`x\gt 0`$, write $`\epsilon=x-t`$. Expansion of the convergent integrals at $`z=1`$ gives

```math
f_x(t)=4\,2^{1/4}C x^{-1/2}\epsilon^{1/4}
 +O(\epsilon^{5/4}),\qquad
f'_x(t)=-2^{1/4}C x^{-1/2}\epsilon^{-3/4}
 +O(\epsilon^{1/4}).
```

The differentiated expansion follows by factoring the integrals as $`(1-z)^{1/4}`$ times functions analytic near $`z=1`$. The derivative is locally integrable, but its square is not. Positivity does not justify global derivative monotonicity.

## Exact bridge on a bounded shift interval

Define

```math
h_x(t)=4C x^{-1/4}(1-(t/x)^2)_+^{1/4},\qquad
a_0(u)=e^{u/4}-\tfrac34 .
```

For $`t\ge a`$ and $`a\le x\le2a`$,

```math
\boxed{
f_x(t)=h_x(t)-
 \int_0^{\log(x/a)}a_0(u)h_{xe^{-u}}(t)\,du.
}
```

The integrand is zero once $`xe^{-u}\le t`$. To check the identity, integrate by parts:

```math
A(z)=4z^{1/8}(1-z)^{1/4}
 +\tfrac12\int_z^1 r^{-7/8}(1-r)^{1/4}\,dr,
```

```math
B(z)=4z^{1/4}(1-z)^{1/4}
 +\int_z^1 r^{-3/4}(1-r)^{1/4}\,dr.
```

Substitute $`r=ze^{2u}`$ in the remaining terms. No endpoint term is omitted.

For any fixed finite vector $`v_n`$, supported at $`n\ge a`$, set
$`F(y)=\sum_n v_nf_{ae^y}(n)`$,
$`H(y)=\sum_n v_nh_{ae^y}(n)`$.
For $`0\le y\le L\le\log2`$, finite summation gives
$`F=H-a_0*H`$, with convolution over $`0\le u\le y`$.
The explicit resolvent

```math
b_0(u)=\tfrac38e^{3u/4}-\tfrac18e^{-u/4}
```

satisfies $`b_0=a_0+a_0*b_0`$: direct integration gives

```math
(a_0*b_0)(u)=\tfrac38e^{3u/4}-e^{u/4}-\tfrac18e^{-u/4}+\tfrac34.
```

Consequently

```math
H=F+b_0*F,\qquad
\|H\|_\infty\le
\frac{e^{3L/4}+e^{-L/4}}2\,\|F\|_\infty.
```

Uniqueness follows from Grönwall's inequality for the difference of two continuous solutions on the bounded interval. All kernels are bounded there, so the convolution reassociation is absolutely integrable. At $`L=\log2`$ the cost is

```math
\tfrac32\,2^{-1/4}\lt 24/19.
```

The last inequality is equivalent to $`19^4\lt 2\cdot16^4`$. This is an exact finite-family bridge, not an infinite convolution completion.
