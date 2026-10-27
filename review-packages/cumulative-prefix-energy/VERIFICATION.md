# Saved acceptance and present assembly status

The two Lean files are byte-identical copies of the accepted sources. [Source closure](evidence/source-closure.json) records `FinitePrefixBilinear -> CumulativeSquareEnergy` and seven direct Mathlib roots. This is complete package-local closure, not a bundled or freshly replayed external dependency tree. The broad `Mathlib.Tactic` import is preserved unchanged.

## Historical acceptance

Saved migration records identify Lean **4.36.0-rc1** and Mathlib **c85646e3ac7d3ca39468f114b2d95d62e1611533**. Both source builds passed, taking approximately 16.657 and 20.672 seconds respectively. Those times do not estimate clean dependency/bootstrap work.

[Saved acceptance](evidence/saved-acceptance.json) is a curated portable projection of selected existing records. It retains exact source/object/record/full-log fingerprints and actual terminal reports; original native-path records remain private. The projection is not a new compiler receipt. [Square reports](evidence/CumulativeSquareEnergy.saved-axioms.txt), [bilinear reports](evidence/FinitePrefixBilinear.saved-axioms.txt).

Six square-source and four bilinear-source terminal reports are present. Each lists only `propext`, `Classical.choice`, and `Quot.sound`. Eighteen public theorems and four definitions are present in the compiled source. Eight public theorems have no separate saved terminal axiom print; all names and report coverage are explicit in the [declaration roster](evidence/public-declarations.json). Two private polarization helpers are not public API.

The older collection's source-admission audit covers these same bytes but is distinct from the later 4.36 migration. A static token scan of the two copied sources found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe` or `opaque` declaration token after comments were removed. This scan is not a compiler, Lean parser or transitive Mathlib audit. [Earlier audit](evidence/saved-source-audit.json), [assembly scan](evidence/static-source-audit.json).

## Present checks and limits

This assembly compares file hashes, exact headers, saved reports, local dependency edges, JSON/TOML/pins and local links. Internal review checks statement/essay alignment. No new theorem, compiler/import/export/axiom command, dependency acquisition/build, runtime/admission query, numerical experiment or external communication ran.

The root lock is manually assembled from a saved 1.3.0 root schema and pinned upstream manifest. Mathlib and eight transitive revisions are statically consistent. **Lake has not accepted this lock in a fresh root.** [Lock provenance](evidence/lock-provenance.json).

No cached proof object is bundled as a replay substitute. Clean dependency/bootstrap/artifact closure, guarded build integration, fresh import/type/axiom replay and human rights/release approval remain NOT RUN or pending. [Test ledger](evidence/test-ledger.json), [build recipe](BUILD.md), [human review](HUMAN-REVIEW.md).
