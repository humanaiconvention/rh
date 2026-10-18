# Complete-form domain and zero-mode Schur criterion

A source-only Lean 4 formalization for a concrete Weil-type arithmetic form. **No all-radius positivity, RH proof, or new arithmetic cancellation is claimed.**

The useful results are:

- Same-support smooth approximation in the full logarithmic Fourier form norm, including actual anchored primitives with jumps.
- Actual compact embedding, finite nullspace and positive physical complement gap, conditional on base-radius positivity.
- The exact local Schur reduction: at a hypothetical null state, the outward residual is nonpositive; outward positivity holds **iff the whole residual matrix is exactly zero**.
- Local exclusion of finite point-jet functionals and an honest conditional radius-continuation criterion.

Read [the mathematical note](NOTE.md), then [the theorem map](THEOREMS.md). [Verification and limits](VERIFICATION.md) distinguishes source compilation, imported binaries and the limited extra kernel replay. These are formal implementations and concrete specializations of standard analysis; no research novelty is claimed. The remaining arithmetic statement is exact whole Schur compensation or exclusion of finite null states.

## Reproduce without downloads

The package pins Lean 4.35.0 and mathlib commit `6015dbbfc399f4548bafd46f9560ff61595fd328`. With an existing matching Lean executable and prepared dependencies:

```text
python -B replay.py --lean /path/to/lean --packages /path/to/.lake/packages
```

The helper checks all release hashes, every dependency checkout revision and clean tracked source, an exact direct-import allowlist, and the saved 72 direct package-entry binary hashes. It creates a new `.verification/run-*`, compiles all 199 local modules from sources in dependency order, and checks all declared terminal axiom reports against `propext`, `Classical.choice`, and `Quot.sound`. It downloads and installs nothing. Existing transitive package binaries and the Lean toolchain remain trusted dependencies. Saved package binary hashes describe the tested environment; a different binary build must be authenticated separately rather than silently accepted.

For a separately prepared standard Lake environment, `lake build WeilForm` is the corresponding build target. The direct replay is the tested path; the full Lake dependency-resolution/build workflow is not claimed to have been executed here. The supplied Lake configuration is syntax checked separately.

The helper uses two Lean threads, a 3072MiB Lean heap limit and a 1800-second per-module timeout. This heap flag is not a portable operating-system working-set guarantee. Generated proof objects and local logs are excluded from Git. This package disables Git line-ending conversion so the distributed source bytes match the recorded hashes on each platform. `--verify-only` checks release/dependency consistency without recompiling proofs.

MIT applies through the repository [license](../LICENSE); dependency licenses remain their own. This is AI-assisted work with internal checking and no external peer review.
