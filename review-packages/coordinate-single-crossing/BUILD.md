# Pinned replay proposal; not executed

The source has the historical acceptance recorded in [EVIDENCE.json](EVIDENCE.json). This extracted project and its manually assembled root lock have not been built or accepted by Lake. No fresh downstream import has been checked. The recipe is a reviewable target, not an admitted runner or completion forecast.

## Exact inputs

- Use a clean copy of this package directory without inherited outputs or machine-local providers.
- Toolchain: `leanprover/lean4:v4.36.0-rc1`.
- Mathlib: `c85646e3ac7d3ca39468f114b2d95d62e1611533`; the full declared project package set is in [DEPENDENCIES.json](DEPENDENCIES.json).
- Review `lakefile.toml`, `lean-toolchain` and `lake-manifest.json`. Exact `rev` values are fixed commits; branch-like `inputRev` metadata is not an instruction to update them.
- Materialize/authenticate the exact dependencies through a separately approved standard route. Configuration, setup, cache and dependency builds are separate work; no artifact readiness or producer closure is asserted.
- Review and neutralize unintended provider-path/toolchain overrides in the later isolated environment. No present environment setting has been changed.

## Intended source and consumer checks

After legitimate provisioning and process/resource admission, the intended source target is:

```text
lake build CoordinateSingleCrossing
```

The source contains its saved terminal `#print axioms` commands. A later fresh importing consumer must import this exact module and check the declarations below. It is not supplied as an already compiled wrapper.

```lean
import CoordinateSingleCrossing
#check CoordinateSingleCrossing.lipschitz_comp_mul_integrable
#print axioms CoordinateSingleCrossing.lipschitz_comp_mul_integrable
#check CoordinateSingleCrossing.centered_coordinate_moment_eq
#print axioms CoordinateSingleCrossing.centered_coordinate_moment_eq
#check CoordinateSingleCrossing.coordinate_moment_nonneg
#print axioms CoordinateSingleCrossing.coordinate_moment_nonneg
#check CoordinateSingleCrossing.abs_integral_comp_le_coordinate_moment
#print axioms CoordinateSingleCrossing.abs_integral_comp_le_coordinate_moment
#check CoordinateSingleCrossing.universal_coordinate_budget_iff
#print axioms CoordinateSingleCrossing.universal_coordinate_budget_iff
```

Record the exact source/configuration/lock fingerprints, dependency provenance, actual process accounting, logs and output identity. Require each report to remain within `propext`, `Classical.choice`, and `Quot.sound`. Reject admissions, numerical oracles, accidental private providers or changed hypotheses. A successful source build alone does not certify the importing consumer or a version port.

## Resource and acceptance boundary

The existing project limits remain: one concurrent compiler, two Lean threads, 3072 MiB Lean heap, owned working-set stop 3113851289 bytes, private/job cap 10737418240 bytes, 1 GiB physical and commit reserves, and at most four owned active processes. The two per-process flags in the proposed Lake file do not enforce concurrency, ownership or the other limits. No special scheduler, resource probe, supervisor or bypass is introduced here.

Do not assume one outer Lake command is one compiler launch. Establish supported admission and a bounded budget separately before any run; setup and provisioning are unpriced here. If the normal route is unavailable, preserve the blocker instead of retrying a denied action or extending custom infrastructure.

Open checks: root-lock acceptance without drift; clean source build; actual declaration/type and transitive-axiom reports; fresh importer; semantic review of the exact hypotheses; notices and intended-upstream API fit. None was run for this package snapshot.
