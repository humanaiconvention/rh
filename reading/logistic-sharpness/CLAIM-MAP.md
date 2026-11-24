# Logistic example — exact claim and evidence boundary

This is a portable reading map for the existing catalog3146/3147 theorem, not a new proof run or port. [The short proof](REVIEW-NOTE.md) gives the literal kernel, all atoms and the exact constant. Both banks have infinite mass; both convolution integrals are separately finite.

Historical locally checked declaration (source closure not included here): `SmallWidthSharpness.actual_small_width_limit_and_sharpness` in `SmallWidthLimitRepair001.lean`. Its conjunction asserts:

1. Along n:Nat atTop, quotient((n+1)^(-1),−1) tends to the exact sharp constant; n=0 is included.
2. For all real L,v, L>0 implies C<quotient(L,v).
3. For all real B, [for every L>0,v, B≤quotient(L,v)] iff B≤C.

There is no extra theorem hypothesis, finite truncation, eventual-width or bounded-location restriction. Strict pointwise positivity above C does not mean a uniform positive gap above C. No separate fixed-width saturation or cross-width theorem is added.

## Historical local evidence, not a new verdict

- Lean4.36.0-rc1, Mathlib `c85646e3ac7d3ca39468f114b2d95d62e1611533`, with the saved historical overlay/dependency boundary.
- Accepted provider source SHA256 `4aead6574a1ffebd827d3c60323a0f3c70138c6f041b32b8cbafbdbd492596dd`.
- Recorded transitive axioms exactly `propext`, `Classical.choice`, `Quot.sound`.
- Historical local Challenge/type-printer and axiom evidence was accepted at its recorded scope. Strict isolated exported-definition comparison, qualified checker roster/control and external human review remain pending.
- This branch does not include the38custom-module solution closure or claim it is a small independent port. No new Lean,4.37build, consumer, export, comparator or CI replay ran.

The note is a written derivation subject to human review; mathematics/prose are not kernel-checked merely by association with the declaration. Literature priority and practical value remain unestablished. No actual Möbius, theta/zeta, RH or general estimator consequence is inferred.

The only editorial change in this reading copy replaces the original private-review visibility phrase with public-review-branch wording. Mathematical content is unchanged. [Reading-copy manifest](READING-COPY.json) records original/current hashes and the exact delta. Original frozen files remain in the project's sealed record.
