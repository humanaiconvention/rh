# Reproduction recipe — unexecuted rc1 candidate

**No command below was used to claim a new Lean result in this packaging pass.** A qualified operator must supply the exact accepted toolchain/dependencies and preserve the project's resource limits before proof execution.

1. Clone/check out this review commit. Keep the historical provider at `review-packages/gauss-digamma/DigammaGauss.lean`; verify its SHA256 against [CANDIDATE.json](CANDIDATE.json). Do not substitute an older/different proof or copy cached local package objects.
2. Enter `review/gauss-digamma-lean437rc1`. The unchanged `lean-toolchain` selects 4.37.0-rc1. Authenticate the binary's origin and source revision; record `lean --version` and `lean --githash` output. Do not change the global toolchain.
3. Materialize the nine exact Git revisions in [lake-manifest.json](lake-manifest.json), with matching trusted upstream artifacts where used. Check each actual checkout revision and configuration/object provenance before execution. Do not use `lake update`, float revisions, edit the lock, or use the partial 3159 checkout.
4. Start with no package-local `.lake/build` outputs. Under the accepted bounded runner, capture complete separate stdout/stderr and exit status for:

```text
lake build PackageConsumer
```

This must freshly cover the linked provider, public API and both typed consumer declarations. The layout uses the provider's existing public source, not an external path dependency or a changed theorem. All three libraries request two Lean threads and 3072 MiB; that request alone is not a qualified parent/configuration resource guard.

5. In a separately specified Mathlib-only statement environment, elaborate [challenge/Challenge.lean](challenge/Challenge.lean), retaining its deliberate specification holes. Inspect expanded types, definitions, assumptions, instances, real/complex coercions, signs, measure and `Ioi 0`. Compare to the actual solution types. No solution import belongs in the Challenge. A Challenge exit0 is not proof acceptance.
6. Save actual output hashes, clean-state evidence, commands and exits. Require the 27 exact named solution reports in [the historical reference receipt](evidence/historical-rc2-replay.json), with transitive axioms contained in `{propext, Classical.choice, Quot.sound}`. Reject `sorryAx`, custom and native-computation axioms; do not infer fresh results from the old list.

## Separate strict gate

Ordinary Lake acceptance, if obtained later, is local evidence. Strict independent replay additionally requires pinned source/checkers/config in isolated unprivileged Linux/bubblewrap, no secrets/network during proof execution, separately frozen exact Challenge, complete `lake comparator --paranoid --json` per-kernel evidence, and a legitimate compiling-but-wrong statement rejected for the intended mismatch. No qualified strict configuration/runner is supplied or claimed by this candidate. No global settings, old pins, or sandbox policy should be changed to manufacture a pass.

First current prerequisites are exact accepted rc1 inputs and a qualified full execution route; 3158–3159 did not provide them. Provider provenance/rights review and human proof understanding are separate pending reviews. This branch is for reading and review, not submission-ready installation instructions or a guaranteed build.
