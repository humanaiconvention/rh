# Reproducible finite measurements

**Purpose:** rule out universal sign shortcuts. These values do not prove or refute an all-scale bound.

Use the complete $G,D_P,Y_P$ from [the prime-transfer note](../docs/prime-phase-transfers.md), with $B=4(M-\lfloor M^{1/4}\rfloor)$. Thus $Y_P=G^2-D_P$ includes every between-class pair and every cutoff tail.

| $M$ | $P$ | certified $D_P$ interval | certified $Y_P$ interval |
|---:|---|---|---|
| 113 | 2, 3 | [14.674, 14.675] | [16.815, 16.816] |
| 284 | 2, 3 | [31.862, 31.863] | [52.540, 52.541] |
| 4,096 | 2, 3, 5, 7 | [123.229, 123.230] | [−99.782, −99.781] |
| 65,536 | 2, 3, 5, 7, 11, 13 | [510.477, 510.478] | [−126.444, −126.443] |

Two further complete transfers are informative:

- At $M=4096$, adding prime $7$ to $P=\{2,3,5\}$ **increases** $D_P$ by an amount in [0.910, 0.911].
- At $P=\varnothing$, $\Omega_{2,3}$ lies in [1.577, 1.578] for $M=27$, and in [−82.597, −82.596] for $M=65536$.

These signs refute universal diagonal damping and a universal sign for the mixed transfer. Since regrouping leaves $G$ unchanged, neither observation is a lower bound on its growth.

## Error control and reproduction

Run:

~~~text
python -B scripts/reproduce_measurements.py
~~~

The script constructs the floor histories and Möbius sieve afresh. For each needed $n$, it computes
$t=\lfloor2^{80}/\sqrt n\rfloor$ by integer square root and verifies

$$
t^2n\le2^{160}\lt (t+1)^2n.
$$

This encloses $1/\sqrt n$ between consecutive $2^{-80}$ rationals, or exactly at one rational when equality holds. Products, squares, and signed sums use outward interval arithmetic. Each recomputed interval must fit within its published enclosure and have width below $10^{-12}$.

Choosing a lower or upper root enclosure by the sign of a coefficient controls **rounding error only**. It is not an estimate formed by replacing arithmetic coefficients with their magnitudes.

[Machine-readable published intervals](finite-measurements.json) contain no external certificate dependencies. Optional `--output path.json` saves exact rational endpoints to a new file. Optional `--max-M 4096` runs a shorter check and reports skipped entries.
