# Pinned clean-checkout recipe and unperformed checks

**Documentation only. No command below was run for this assembly.** Saved local acceptance is separate from a fresh standalone build. Dependency acquisition, setup, cache retrieval and compiler execution need their own authorization and resource accounting; none is hidden in the existing unused proof allowance.

## Inputs

1. Use a clean copy of this candidate directory as the project root, without inherited `.lake` outputs or machine-local path adapters. No public repository URL or branch is assigned by this assembly.
   A clean directory alone is insufficient: the later reviewed replay environment must record and neutralize unintended `LEAN_PATH`, `LEAN_SRC_PATH`, `LEAN_SYSROOT` and `LEAN_PREFIX` overrides, and check the selected toolchain, `PATH` and cache settings for private providers. This is a future setup requirement; no present environment setting was changed by this assembly.
2. Make the exact toolchain named in `lean-toolchain` available: `leanprover/lean4:v4.36.0-rc1`. The toolchain binaries are not bundled here.
3. Review `lakefile.toml` and the **candidate** root `lake-manifest.json`. Mathlib itself and all eight upstream dependency revisions are listed in [dependency pins](evidence/dependency-pins.json). `rev` fields are fixed commits; branch-like `inputRev` fields retain the upstream declaration metadata and are not a request to update them.
4. Materialize those exact public dependencies through a separately approved workflow. They may require configuration compilation, setup or cache/source builds. No offline-ready external artifact closure, network bootstrap or process count has been validated for this package. Do not silently reuse an unrelated cache or update the lock to moving branches.
5. Retain the existing notices and resolve [human review and release blockers](HUMAN-REVIEW.md) before distribution.

## Logical build target

From the clean project root, after the prerequisites are legitimately ready, the intended target is:

```text
lake build IteratedDerivOfScalars
```

The default target is the same. Its complete package-local source closure is the single `IteratedDerivOfScalars.lean` file,with four public Mathlib imports and one saved terminal `#print axioms` command. Its private helpers are included in that source,not separate modules. No additional proof wrapper, hidden local provider or new theorem has been added.

This is a build recipe, **not an admitted local runner**. It may create multiple configuration, dependency or local compiler processes. It must not be counted as one compiler launch merely because it is one outer command.

## Required execution controls for this project's later replay

The existing admission gate is unresolved and was not retried. A reviewed scheduler must preserve one concurrent compiler, two Lean threads, 3,072 MiB heap, the 2.9 GiB owned working-set stop, 10 GiB private/job cap, 1 GiB physical/commit reserve, four owned-process cap and all applicable time limits.

`moreLeanArgs = ["-j", "2", "-M", "3072"]` constrains each Lean process; it does not prove that Lake serializes its tasks or enforces the other caps. No verified `lake -j1` option or `LAKE_NUM_JOBS` serialization guarantee was established from the inspected pinned Lake source. A compatible guarded scheduler remains **unassembled and not run**. No such flag, environment assumption or alternative executor is supplied as a workaround.

## What a later accepted replay must record

- A clean root and unchanged source/config/lock fingerprints, exact toolchain identity, and a legitimate external dependency/artifact closure.
- Whether Lake accepts this manually assembled root lock without alteration. JSON/TOML parsing alone is not that test.
- Every actual setup/configuration/local compiler process, resource admission and cleanup result, build log and output fingerprint.
- Successful inclusion of the local source, all declared names and exact terminal statements.
- A fresh axiom report for the one saved public declaration, with no `sorryAx` or unsupported axioms. The two private implementation helpers have no separate saved terminal report and are not advertised as public API. The public theorem's transitive report is the saved audit boundary.
- A source admission scan and a semantic review that retains the complex scalar/function types,existing representation premise,center0,same r:ENNReal,shift n+k,and denominator n!.

The saved acceptance used machine-local output/cache paths. Inspected private environment metadata also contains a Batteries source/object adapter; it does not establish the exact source/object binding for every historical run. Those private arrangements are **not declared release prerequisites** and are not included in the candidate. A public-pin clean build is needed to close the portability gap rather than inheriting that environment implicitly.

Until these checks are admitted and completed, the exact source results have saved acceptance, while standalone replay, external artifact readiness, root-lock semantics and full guarded build integration remain **NOT RUN**. [Test ledger](evidence/test-ledger.json).
