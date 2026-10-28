# Finite arithmetic and Lean certificates

Exact finite-arithmetic identities, reproducible checks, and two Lean 4 certificates from a bounded investigation related to the Riemann hypothesis.

**No RH proof, resolution of the open arithmetic bound, determinant-nonvanishing result, or research novelty is claimed.** The mathematical statements and their limits are identified below.

## Additional Lean review packages

The [ten-package review collection](review-packages/README.md) adds finite boundary and prefix identities, a classical digamma integral, scalar EGF differentiation, paired-measure Jensen approximation, theta–Macdonald cumulative order, sharp cumulative/Lipschitz duality, finite polynomial root counting, logarithmic polynomial degree growth, and signed single-crossing bounds along a coordinate.

These are unchanged sources with saved individual acceptance, **not freshly replayed standalone releases**. Eight packages use the recorded Lean 4.36.0-rc1 baseline; the finite root-counting and polynomial-growth APIs retain their Lean 4.35.0 baseline. Each separate project retains exact statements, evidence, build prerequisites, notices and pending-review status. The older certificates below retain their original pins and verification scope.

## Start here

| Question | Read |
|---|---|
| What has Lean verified, and how can I reproduce it? | [Lean certificates](qrh-obstructions-lean/README.md) |
| Why is the norm-157 conjugate phase nonzero? | [Local phase survival](qrh-obstructions-lean/MetaplecticDictionary.md) |
| What cancels, and what remains unbounded? | [Quarter-mask sum](docs/quarter-mask-ledger.md) |
| Why does the anchored prefix-envelope certificate miss fourth-root precision? | [Envelope obstruction](docs/LEMMA-002-ENVELOPE-OBSTRUCTION.md) |
| Does prime regrouping damp the whole sum? | [Prime phases and transfers](docs/prime-phase-transfers.md) |
| Why does centering defeat an uncentered sign theorem? | [Finite GCD kernel](docs/uncentered-gcd-kernel.md) |
| Can a finite convolution remove the hard estimate? | [Möbius convolution](docs/finite-convolution.md) |
| Can radical coordinates detect an exact zero? | [Multiquadratic coordinates](docs/multiquadratic-ledger.md) |
| What is valid for the singular weight? | [Kernel calculus](docs/kernel-calculus.md) |
| What would a counterexample actually establish? | [Converse and negative targets](docs/converse-and-negative-targets.md) |

## Machine-verified certificates

The [standalone Lake project](qrh-obstructions-lean/README.md) pins Lean **4.35.0** and mathlib commit **`6015dbbfc399f4548bafd46f9560ff61595fd328`**. It contains:

- [Analytic obstructions](qrh-obstructions-lean/Obstructions.lean): non-summability of the specified Euler defects over Eisenstein prime ideals for $`1/2<\sigma\le2/3`$, the exact supplied-exponent deficit $`3/8`$, and the stipulated sieve-parameter mismatch at $`1/2`$.
- [Local phase survival](qrh-obstructions-lean/MetaplecticDictionary.md): for the norm-157 conjugate slot $`\{13+12\omega,1-12\omega\}`$, the unit-phase cube relation implies $`157x^3-471x+118=0`$ and $`118/471\le|x|\le2`$, hence $`x\ne0`$.

Both compile without admitted proofs or added mathematical axioms. Their source hashes, compiler logs, and axiom audits are included. The analytic certificate concerns the specified factor and supplied parameters. The local certificate proves the algebraic phase implication; it does not formalize the native Gauss-sum identification, regularization operation, or a lower bound for the complete physical row.

See the [package README](qrh-obstructions-lean/README.md) for exact theorem names and limitations. [GitHub Actions](https://github.com/humanaiconvention/rh/actions/workflows/lean-certificates.yml) checks both certificates.

## Finite identities and the open estimate

The notes in [`docs/`](docs/) prove identities for Möbius-weighted floor sums, prime regrouping, and divisor kernels using finite algebra and calculus. A useful starting result is the [closed GCD kernel](docs/uncentered-gcd-kernel.md): it proves an uncentered sign inequality and explains why centering can reverse that sign.

The remaining target is for the **complete** bulk sum $`G(M)`$ in [the quarter-mask ledger](docs/quarter-mask-ledger.md): prove $`|G(M)|\le C\sqrt M`$ for every integer $`M\ge8`$, or prove $`|G(M)|/\sqrt M`$ is unbounded. Neither is established. Regrouping, finite numerical stability, or growth of one component does not settle this target.

## Reproduce

**Finite arithmetic:** Python 3.9 or later, standard library only. From the repository root:

~~~text
python -B scripts/check_finite_identities.py
python -B scripts/reproduce_measurements.py
~~~

The first checks exact rational square-root coordinates against separately constructed finite sums. The second recomputes every interval in [the measurement table](data/finite-measurements.md), including the largest $`M=65\,536`$. Integer square roots give rigorous rounding bounds; floating-point values are not used.

Finite tests support bookkeeping. The proofs in the notes establish the stated general identities; the tests do not establish the open all-scale estimate.

**Lean certificates:** install [Elan](https://github.com/leanprover/elan), then run from the repository root:

~~~text
cd qrh-obstructions-lean
elan toolchain install leanprover/lean4:v4.35.0
lake update
lake exe cache get
lake build --wfail
lake env lean Obstructions.lean
lake env lean MetaplecticDictionary.lean
~~~

The [package instructions](qrh-obstructions-lean/README.md#reproduce) also explain source-hash and axiom-report verification. Build caches and dependency checkouts are excluded from Git.

## Scope and reuse

Every arithmetic sum is finite, with its cutoff stated. Kernel integrals are proper limits of convergent integrals over bounded intervals. Centering, boundary terms, and both weights in bilinear identities stay attached.

This is a curated, AI-assisted collection with **no external peer review**. The finite-arithmetic notes have internal checking; only the separately identified Lean certificates have proof-assistant verification within their stated scope. Historical research logs, third-party source archives, and unrelated project material are excluded.

MIT applies to the repository; see [LICENSE](LICENSE). Dependency licenses remain their own. The Lean package includes [citation metadata](qrh-obstructions-lean/CITATION.cff).
