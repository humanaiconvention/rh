# Verification scope

## Prepared source release

This supplement contains exactly 28 new source modules over the unchanged published parent 199 package at commit 46a969283f22775a7a064df297cf10f7d9caf578. All 28 exact source bytes were authenticated against their accepted local source/snapshot/standard-axiom receipts during preparation. Their source and import metadata are recorded in [the manifest](REPLAY-MANIFEST.json).

The parent has a completed fresh 199-source replay with 630 terminal axiom reports. Its recorded receipt and source hashes remain unchanged. The supplement declares 99 additional terminal reports; the combined helper expects 227 local modules and 729 reports.

The private incremental isolated replay PASSED: 28 new modules, 99 new terminal reports, and a maximum observed new working set of 2,130,042,880 bytes. Its [sanitized evidence](INCREMENTAL-REPLAY-RECEIPT.json) authenticates source, import, object, log and standard-axiom records. The 199 previously fresh parent modules were authenticated and reused in that earlier incremental check. A subsequent, distinct public-helper replay PASSED ALL 227 sources from empty local outputs with all 729 terminal reports. Its maximum observed working set was 2,259,513,344 bytes. The [fresh receipt](FRESH-REPLAY-RECEIPT.json) has SHA-256 `6ddb98df07e9abdfb0132ca3b34b7b1c7e15129cf6dc7ddfb001c705847bc979`. No proof source, import manifest or executed helper was edited after the fresh run; only this report, the README and the distributed hash list were completed.

## What the helper verifies

The helper uses the two distributed source folders and existing pinned package binaries. It does not reuse prior local proof objects. It authenticates all release files, the unchanged parent boundary, dependency checkout revisions and clean tracked sources, the exact 80 direct package-entry binary hashes, source import fingerprints and terminal-report names.

Every reported axiom must belong to propext, Classical.choice, Quot.sound. Sources containing admitted proofs, added axioms, native_decide or opaque replacements are rejected. Successful source compilation is distinct from a separate kernel replay of an imported environment.

Resources are fixed at two Lean threads, a 3072 MiB Lean heap cap and a maximum 1800 seconds per module. The Windows monitor fails closed on monitoring errors and stops before 3 GiB. The alternative POSIX 3 GiB address-space path is prepared but untested. The helper stops on a failed proof, changed source, unexpected axiom or exceeded budget; it never changes mathematical tolerances.

Existing pinned toolchain and transitive package binaries remain explicit trust boundaries. Direct binary hashes describe the tested environment; an alternate build requires separate authentication. No numerical oracle, source installation, downloaded code execution or external review is claimed.

## Mathematical limits

The new statements are actual complete-domain identities and conditional consequences. They prove no nonzero old null at any specified radius, no unconditional all-radius energy-sign conclusion, no quantitative collar size, no all-radius positivity or RH. The strict negative Schur conclusion requires a genuine nonzero old-null coordinate and the constructed local coercive regime.

Internal checking and isolated replays are not external peer review. Private logs, original research paths, compiled objects and failed-attempt archives are not distributed.
