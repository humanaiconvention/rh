# Saved acceptance and present assembly status

The two `.lean` files are byte-identical copies of the accepted sources. [Local dependency closure](evidence/source-closure.json) records their source hashes, local edge and four direct Mathlib imports. This is the complete package-local source closure; external library contents are pinned by Git revisions, not vendored or newly replayed here.

## Historical checks for these exact sources

The preserved migration records identify Lean **4.36.0-rc1** and Mathlib **c85646e3ac7d3ca39468f114b2d95d62e1611533**. Both source builds passed, in approximately 10.844 and 10.437 seconds respectively. Those historical times are not a forecast for a clean dependency build.

[Saved acceptance](evidence/saved-acceptance.json) is a portable projection of the selected existing records. It gives source/object/log fingerprints and actual terminal reports. The full local originals remain preserved outside this candidate; the projection is not presented as a fresh compiler receipt. [Boundary axiom output](evidence/CumulativeBoundary.saved-axioms.txt), [quadratic axiom output](evidence/CumulativeQuadratic.saved-axioms.txt).

Five structural boundary reports list only `propext`. The other two boundary reports and three bilinear/quadratic reports list only `propext`, `Classical.choice`, and `Quot.sound`. All ten expected saved terminal reports are present. `mixedDifference_eq` is also public and compiled in the saved source, but it was not separately printed in that terminal list. [Public declaration roster](evidence/public-declarations.json).

The earlier collection's saved source-admission flag covered these same source bytes, although its build used the older collection environment. Its projected audit is retained separately from the 4.36 migration evidence. A new static token scan of only the two copied files found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe` or `opaque` declarations. That scan is not a compiler, Lean parser or whole-Mathlib audit. [Saved source audit](evidence/saved-source-audit.json), [assembly scan](evidence/static-source-audit.json).

## Fresh checks

No compiler, import/export-table command, axiom command, dependency acquisition/build, configuration execution, runtime/admission query, new research or external communication ran during this assembly. No `.olean` file is bundled as a substitute for a fresh build. Existing source comments and printed commands were preserved unchanged.

The root lock was constructed statically from a saved 1.3.0 root schema and the exact pinned upstream Mathlib manifest, adding Mathlib itself and marking its transitive dependencies inherited. All package names/revisions/config paths were checked for internal consistency; **Lake has not accepted this root lock in a fresh project**. [Lock provenance](evidence/lock-provenance.json).

The remaining checks are listed individually in [test status](evidence/test-ledger.json). Saved Lean acceptance, current static assembly, fresh portable replay, and human release approval are different verification levels.
