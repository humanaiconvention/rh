# Finite arithmetic and Lean certificates

A small collection of **proved finite identities** for Möbius-weighted floor sums, prime regrouping, and divisor kernels. The most useful result is a closed GCD kernel: it proves an uncentered sign inequality and shows exactly why centering can reverse that sign.

These are explanatory notes and reproducible checks, using standard finite algebra and calculus. **No research novelty, RH proof, uniform arithmetic bound, or determinant-nonvanishing result is claimed.**

The separate [Lean 4 package](qrh-obstructions-lean/README.md) provides machine-verified certificates for a specified analytic architecture and a local conjugate-slot phase. These certificates do not resolve the open finite-arithmetic estimate below.

## Start here

| Question | Read |
|---|---|
| Where are the machine-verified proofs and reproduction commands? | [Lean certificates](qrh-obstructions-lean/README.md) |
| What cancels, and what remains unbounded? | [Quarter-mask sum](docs/quarter-mask-ledger.md) |
| Why does the anchored prefix-envelope certificate miss fourth-root precision? | [Envelope obstruction](docs/LEMMA-002-ENVELOPE-OBSTRUCTION.md) |
| Does prime regrouping damp the whole sum? | [Prime phases and transfers](docs/prime-phase-transfers.md) |
| Why does centering defeat an uncentered sign theorem? | [Finite GCD kernel](docs/uncentered-gcd-kernel.md) |
| Can a finite convolution remove the hard estimate? | [Möbius convolution](docs/finite-convolution.md) |
| Can radical coordinates detect an exact zero? | [Multiquadratic coordinates](docs/multiquadratic-ledger.md) |
| What is valid for the singular weight? | [Kernel calculus](docs/kernel-calculus.md) |
| What would a counterexample actually establish? | [Converse and negative targets](docs/converse-and-negative-targets.md) |

**Open target in this extract:** for the complete bulk sum $`G(M)`$ defined in the first note, prove $`|G(M)|\le C\sqrt M`$ for all integers $`M\ge8`$, or show that $`|G(M)|/\sqrt M`$ is unbounded. Neither is established here. A growing isolated component is insufficient.

## Machine-verified certificates

The [standalone Lake project](qrh-obstructions-lean/README.md) pins Lean **4.35.0** and mathlib commit **`6015dbbfc399f4548bafd46f9560ff61595fd328`**. It contains:

- [Analytic obstructions](qrh-obstructions-lean/Obstructions.lean): non-summability of the specified Euler defects over Eisenstein prime ideals for $`1/2<\sigma\le2/3`$, the exact supplied-exponent deficit $`3/8`$, and the stipulated sieve-parameter mismatch at $`1/2`$.
- [Local phase survival](qrh-obstructions-lean/MetaplecticDictionary.md): for the norm-157 conjugate slot $`\{13+12\omega,1-12\omega\}`$, the unit-phase cube relation implies $`157x^3-471x+118=0`$ and $`118/471\le|x|\le2`$, hence $`x\ne0`$.

Both compile without admitted proofs or added mathematical axioms. Their verification reports, compiler logs, and axiom audits are included. The analytic certificate concerns the specified factor and supplied parameters; the local certificate does not formalize the native Gauss-sum identification or the regularization operation. Neither certifies an RH proof or a lower fluctuation of the complete physical row.

From the repository root:

~~~text
cd qrh-obstructions-lean
lake update
lake exe cache get
lake build --wfail
lake env lean Obstructions.lean
lake env lean MetaplecticDictionary.lean
~~~

See the [package README](qrh-obstructions-lean/README.md) for prerequisites, citation metadata, and the exact scope. [GitHub Actions](https://github.com/humanaiconvention/rh/actions/workflows/lean-certificates.yml) runs both compiler and axiom checks.

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

This is a curated, AI-assisted extract. The finite-arithmetic notes have internal checking and **no external peer review or proof-assistant certification**. The separately identified Lean certificates have compiler verification within their stated scope. Historical research logs and third-party source archives are excluded. MIT applies to the entire repository; see [LICENSE](LICENSE).
