# Supplement theorem map

All native statements retain the full archimedean energy, scalar, both ranks and every active finite prime-power shift.

| Purpose | Exact declaration | Source |
|---|---|---|
| Finite-point smooth-core density | RhPuncturedSmoothCore.puncturedCore_eq_flat | [source](WeilNullCrossing/RhPuncturedSmoothCore001.lean) |
| Functional gluing on the restricted complete domain | RhEndpointWeakGluing.functional_zero_of_three_regions | [source](WeilNullCrossing/RhEndpointWeakGluing001.lean) |
| Native old-interior plus two-collar gluing | RhNativeEndpointGluing.native_old_null_and_collars_full_null | [source](WeilNullCrossing/RhNativeEndpointGluing001.lean) |
| Actual strict-interior whole-row uniqueness, no PSD assumption | RhNativeStrictInteriorUCP.full_row_unique | [source](WeilNullCrossing/RhNativeStrictInteriorUCP001.lean) |
| Literal-old-null local Schur construction, conditional on base PSD | RhActualLiteralNullSchur.local_literal_null_schur_target | [source](WeilNullCrossing/RhActualLiteralNullSchur001.lean) |
| Strict negative literal Schur quadratic form on nonzero coordinates | RhLiteralSchurStrictSign.schur_quadratic_strictly_negative | [source](WeilNullCrossing/RhLiteralSchurStrictSign001.lean) |
| Actual local outward PSD iff old radical dimension zero | RhActualStrictSchurAudit.local_strict_schur_audit | [source](WeilNullCrossing/RhActualStrictSchurAudit001.lean) |
| The two whole collar weak equations cannot both vanish, conditional on nonzero old radical | RhNativeCollarNonvanishing.native_not_both_collar_equations | [source](WeilNullCrossing/RhNativeCollarNonvanishing001.lean) |
| Smooth physical negative witness, conditional on nonzero old native zero diagonal | RhNativeOutwardZeroNegative.native_outward_negative | [source](WeilNullCrossing/RhNativeOutwardZeroNegative001.lean) |
| Genuine physical-unit primitive minimizer | RhNativeRayleighStrict.bottom_attained | [source](WeilNullCrossing/RhNativeRayleighStrict001.lean) |
| Strict native bottom decrease under support enlargement | RhNativeRayleighStrict.nativeBottom_strict_antitone | [source](WeilNullCrossing/RhNativeRayleighStrict001.lean) |

The generic uniqueness and strict-bottom theorems allow arbitrary fixed real C and finite N. The unresolved arithmetic criterion uses ONLY the actual native C_arch and sufficient prime horizon at later nonnegative states.

The core is real, inside a complex weighted Fourier ambient space. Physical unit normalization concerns the primitive, not its derivative. Inverses are constructed full complement form-dual solutions. No graph unitarity, independent-prime bound or pointwise L2 evaluation is assumed.

The eight terminal source roots have 28 additional source modules in their closure. The unchanged parent package contributes 199 modules, including its seven explicit proof-preserving utility excerpts. See [the manifest](REPLAY-MANIFEST.json).

The conditional helper `RhConditionalWeakNullUCP001` retains its premise by design; `RhNativeStrictInteriorUCP.combined_weak_ucp` proves that premise for strict support enlargements. No own-window uniqueness is substituted.
