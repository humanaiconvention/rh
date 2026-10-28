# Standalone replay proposal; not executed

The copied sources have the historical checks mapped in [EVIDENCE.json](EVIDENCE.json) and [DEPS.json](DEPS.json). This newly assembled project, its lock and a fresh importing consumer have not been accepted by Lean/Lake. Source identity checking is not a clean build.

## Independent local layout

All 29 required local `.lean` files are included flat in this directory, with their original names and bytes. `ThetaPowerCoordinate` imports `CoordinateSingleCrossing` and `ThetaMomentOrder`. `ThetaMomentOrder` and its 26 local dependencies form the 27-source density/moment chain. Every local module is separately declared as a `lean_lib` in the proposed `lakefile.toml`. The sole default target is `ThetaPowerCoordinate`.

The neighboring theta and coordinate packages are comparisons and source provenance, not runtime providers or relative-path build dependencies. No private cache adapter, external local source directory, provider object or binary is bundled.

## Inputs and intended target

- Review the proposed `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`.
- Use Lean `leanprover/lean4:v4.36.0-rc1` and Mathlib `c85646e3ac7d3ca39468f114b2d95d62e1611533`; the complete declared nine-package upstream set is fixed in the dependency map and lock. Branch-like `inputRev` values are provenance, not permission to update fixed revisions.
- Materialize and authenticate dependencies through a separately authorized standard route. Cache, setup, configuration and dependency builds have not been priced or performed for this snapshot.
- Use a clean isolated root without inherited outputs or accidental provider-path overrides. Authenticate the actual selected toolchain and artifact producers. No active environment setting was changed here.

After legitimate provisioning/admission, the intended source target is:

```text
lake build ThetaPowerCoordinate
```

This command is a recipe, not a qualified scheduler or completed check. Its dependency processes and configuration work must be accounted for separately. A later fresh consumer should import `ThetaPowerCoordinate`, check the definition and all seven declarations in [THEOREM-STATEMENTS.md](THEOREM-STATEMENTS.md), and print their transitive axioms. The original source already contains those seven terminal print commands; provider source prints may also appear during a clean build. Reused supporting reports are not new results.

```lean
import ThetaPowerCoordinate
#check ThetaMacdonald.PowerCoordinate.powerMomentGap
#check ThetaMacdonald.PowerCoordinate.powerMomentGap_pos
#check ThetaMacdonald.PowerCoordinate.powerMomentGap_eq_signed
#check ThetaMacdonald.PowerCoordinate.actual_power_coordinate_measurable
#check ThetaMacdonald.PowerCoordinate.actual_power_crossing_ae
#check ThetaMacdonald.PowerCoordinate.actual_power_weighted_integrable
#check ThetaMacdonald.PowerCoordinate.actual_power_lipschitz_gap_le
#check ThetaMacdonald.PowerCoordinate.actual_positive_power_budget_iff
#print axioms ThetaMacdonald.PowerCoordinate.powerMomentGap_pos
#print axioms ThetaMacdonald.PowerCoordinate.powerMomentGap_eq_signed
#print axioms ThetaMacdonald.PowerCoordinate.actual_power_coordinate_measurable
#print axioms ThetaMacdonald.PowerCoordinate.actual_power_crossing_ae
#print axioms ThetaMacdonald.PowerCoordinate.actual_power_weighted_integrable
#print axioms ThetaMacdonald.PowerCoordinate.actual_power_lipschitz_gap_le
#print axioms ThetaMacdonald.PowerCoordinate.actual_positive_power_budget_iff
```

For acceptance, require only `propext`, `Classical.choice`, `Quot.sound` in all seven terminal reports. Preserve every source/config/lock fingerprint, actual imports, exact theorem types, resource/accounting logs and outputs. Reject admissions, numerical oracles, changed hypotheses or unintended private providers.

## Resource and semantic gates

Existing project limits remain: one concurrent compiler; two Lean threads; 3072 MiB Lean heap; owned working-set stop 3113851289 bytes; private/job cap 10737418240 bytes; 1 GiB physical and commit reserves; at most four owned active processes. The two proposed per-process flags do not enforce concurrency or the other controls. Establish supported execution/admission and a bounded replay budget separately. Do not extend custom runtime infrastructure or retry a denied action to run this recipe.

Check Lake's acceptance of the new root lock and target/provider declarations, then the actual source build and fresh importer. Check natural k versus `0<k`, coordinate Lipschitzness in `φ(u^k)`, NNReal K including zero, all-real B, actual normalization and weighted integrability. No real-power, negative-power, uniform-in-k numerical bound or root-count statement is added by this package.

The source/record crosswalk covers the needed 29 vertices and 31 local edges. It is not new binary-sidecar qualification or a replay of the larger historical 59-provider profile. Fresh standalone, root-lock and downstream checks remain NOT RUN. Review [ATTRIBUTION.md](ATTRIBUTION.md) and [LICENSE-STATUS.md](LICENSE-STATUS.md) for the remaining notices/API/rights decisions.
