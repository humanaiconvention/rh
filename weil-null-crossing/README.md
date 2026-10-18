# Strict radial decrease and zero-mode loss

A source-only Lean supplement for the concrete complete Weil-type form in the [parent package](../weil-form-domain/README.md), pinned to parent commit 46a969283f22775a7a064df297cf10f7d9caf578.

**No actual zero state, sign of the native ground energy, all-radius positivity, RH proof or research novelty is claimed.** The results are checked structural consequences of the declared form.

The useful additions are:

- Smooth tests avoiding finitely many points are dense in the complete form norm, so old-interior and two-collar weak equations glue without a point-distribution representation assumption.
- A nonzero compact vector cannot have its complete row vanish on a strictly larger window.
- Conditional on an actual old null state and local complement coercivity, the Schur residual for the literal old nullspace is strictly negative on every nonzero coordinate.
- The primitive physical-unit Rayleigh bottom is attained and strictly decreases with support radius.

Thus a hypothetical own-window null is followed by strict outward loss. This does not establish or exclude such a null. The unresolved arithmetic criterion concerns the actual native scalar at later nonnegative states, not every scalar-shifted form.

Read [the note](NOTE.md), [the theorem map](THEOREMS.md), and [verification scope](VERIFICATION.md). The published parent package remains unchanged; this supplement adds exactly 28 modules.

## Replay all 227 sources from empty local outputs

Python 3.9 or later, an existing matching Lean 4.35.0 executable, and the pinned prepared packages are required. No downloads or installations occur.

~~~text
python -B replay.py --lean /path/to/lean --packages /path/to/.lake/packages
~~~

The helper authenticates the parent 199 sources and these 28 sources, the recursive import graph, all 80 direct package-entry binary hashes, the tested Lean executable hash, and every dependency checkout revision/clean tracked source. It then compiles ALL 227 local modules into a NEW output directory, using only that directory and pinned package binaries. It checks all 729 declared terminal axiom reports.

Existing toolchain and transitive package binaries remain trusted. Different binary builds must be authenticated separately. The helper uses two threads, a 3072 MiB Lean heap limit and at most 1800 seconds per module. Windows has a fail-closed monitored stop before 3 GiB; POSIX uses a 3 GiB address-space cap. The POSIX execution path is not claimed tested here. No radius, matrix margin or saved arithmetic tolerance is changed.

The fresh public-helper replay PASSED all 227 local sources from empty outputs, with 729 terminal axiom reports. Its [sanitized receipt](FRESH-REPLAY-RECEIPT.json) records source, object and log hashes. See the verification report for the explicit trusted binary boundary. The manifest is source metadata, not a certificate of global positivity.

MIT applies through the repository [license](../LICENSE); dependencies retain their own licenses. AI-assisted work with internal checking, not external peer review.
