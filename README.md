# Finite arithmetic: identities, limits, and checks

A small collection of **proved finite identities** for Möbius-weighted floor sums, prime regrouping, and divisor kernels. The most useful result is a closed GCD kernel: it proves an uncentered sign inequality and shows exactly why centering can reverse that sign.

These are explanatory notes and reproducible checks, using standard finite algebra and calculus. **No research novelty, RH proof, uniform arithmetic bound, or determinant-nonvanishing result is claimed.**

## Start here

| Question | Read |
|---|---|
| What cancels, and what remains unbounded? | [Quarter-mask sum](docs/quarter-mask-ledger.md) |
| Why does the anchored prefix-envelope certificate miss fourth-root precision? | [Envelope obstruction](docs/LEMMA-002-ENVELOPE-OBSTRUCTION.md) |
| Does prime regrouping damp the whole sum? | [Prime phases and transfers](docs/prime-phase-transfers.md) |
| Why does centering defeat an uncentered sign theorem? | [Finite GCD kernel](docs/uncentered-gcd-kernel.md) |
| Can a finite convolution remove the hard estimate? | [Möbius convolution](docs/finite-convolution.md) |
| Can radical coordinates detect an exact zero? | [Multiquadratic coordinates](docs/multiquadratic-ledger.md) |
| What is valid for the singular weight? | [Kernel calculus](docs/kernel-calculus.md) |
| What would a counterexample actually establish? | [Converse and negative targets](docs/converse-and-negative-targets.md) |

**Open target in this extract:** for the complete bulk sum $`G(M)`$ defined in the first note, prove $`|G(M)|\le C\sqrt M`$ for all integers $`M\ge8`$, or show that $`|G(M)|/\sqrt M`$ is unbounded. Neither is established here. A growing isolated component is insufficient.

## Run the checks

Python 3.9 or later; standard library only, no installation needed.

~~~text
python -B scripts/check_finite_identities.py
python -B scripts/reproduce_measurements.py
~~~

The first checks exact rational square-root coordinates against separately constructed finite sums. The second recomputes every interval in [the measurement table](data/finite-measurements.md), including the largest $`M=65\,536`$. Integer square roots give rigorous rounding bounds; floating-point values are not used.

Finite tests support bookkeeping. The proofs in the notes establish the stated general identities; the tests do not establish the open all-scale estimate.

## Scope and reuse

Every arithmetic sum is finite, with its cutoff stated. Kernel integrals are proper limits of convergent integrals over bounded intervals. Centering, boundary terms, and both weights in bilinear identities stay attached.

This is a curated, AI-assisted extract. It has internal checking, **not external peer review or formal proof-assistant verification**. Historical research logs and third-party source archives are excluded. MIT applies to the entire repository; see [LICENSE](LICENSE).
