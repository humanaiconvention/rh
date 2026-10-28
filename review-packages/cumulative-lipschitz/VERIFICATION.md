# Verification status

## Saved acceptance

The unchanged [source](Cumulative.lean) has SHA-256

`22af796226a21064b9c6a90c5cda1e1c5af24846430ebb75f24614a523fcc230`.

Saved acceptance records a successful single-module Lean check at **2026-10-24T01:59:59.595724+00:00**, using Lean **4.36.0-rc1** and Mathlib **c85646e3ac7d3ca39468f114b2d95d62e1611533**. The four terminal declarations in [the API statement](THEOREM-STATEMENTS.md) each have saved transitive axiom reports containing only:

- `propext`
- `Classical.choice`
- `Quot.sound`

The accepted module uses nine direct Mathlib imports and no local provider imports. The package [evidence record](EVIDENCE.json) separates this saved acceptance from checks not performed here. [Dependency metadata](DEPENDENCIES.json) records the pinned target.

## Not freshly replayed

This package preparation does not include a new compiler run, a fresh standalone dependency build, or a fresh importing-consumer check. No compiled object is supplied as a substitute for those checks. Reproducing the historical result requires the pinned environment and an ordinary supported build route; see [BUILD.md](BUILD.md).

The source contains the accepted four exports. It is not the separate, uncompiled five-export API transformation or a claim of compatibility with another Mathlib revision. Static copying and source identification do not establish fresh elaboration or consumer visibility.

There has been no new current-upstream duplicate search, external review or independent proof replay for this packet. The integrability and zero-mass assumptions remain mathematical inputs. Formal acceptance of this API is not verification of any application-specific estimate.
