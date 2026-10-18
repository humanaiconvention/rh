# Theorem map

All statements use the exact declared form and function spaces. “Conditional” hypotheses remain explicit Lean premises.

| Purpose | Terminal declaration | Source |
|---|---|---|
| Same-window real smooth approximation | `RhRealSameWindowSmooth.real_same_window_smooth_approximation` | [source](WeilForm/RhRealSameWindowSmooth001.lean) |
| Actual physical kernel iff complete-form positivity | `RhSmoothPhysicalTransfer.physical_positive_iff_complete_form_positive` | [source](WeilForm/RhSmoothPhysicalTransfer001.lean) |
| Actual compact embedding | `RhSupportedCompactEmbedding.physical_embedding_compact` | [source](WeilForm/RhSupportedCompactEmbedding001.lean) |
| Finite nullspace and physical complement gap, conditional on PSD | `RhNativeCompactGap.finite_nullspace`, `.physical_complement_gap` | [source](WeilForm/RhNativeCompactGap001.lean) |
| Actual nullspace basis and gap, conditional on PSD | `RhActualKernelData.exists_actual_kernel_data` | [source](WeilForm/RhActualKernelData001.lean) |
| Native local graph-form control | `RhNativeDilationSmallness.uniform_actual_graph_form_smallness` | [source](WeilForm/RhNativeDilationSmallness001.lean) |
| Exact local Schur-zero criterion, conditional on base PSD | `RhBasePositiveSchurReduction.local_complete_schur_zero_target` | [source](WeilForm/RhBasePositiveSchurReduction001.lean) |
| Negative smooth witness, conditional on nonzero nonpositive Schur matrix | `RhSchurNegativeWitness.nonzero_nonpositive_schur_negative_smooth` | [source](WeilForm/RhSchurNegativeWitness001.lean) |
| Exact sufficient-horizon agreement | `RhCompleteFormHorizon.completeForm_horizon_eq` | [source](WeilForm/RhCompleteFormHorizon001.lean) |
| Actual all-prime primitive ground continuity | `RhNativeRadiusFamily.nativeBottom_continuousAt` | [source](WeilForm/RhNativeRadiusFamily001.lean) |
| Sign change implies an intermediate zero with actual nullvector | `RhNativeRadiusFamily.native_sign_change_has_null` | [source](WeilForm/RhNativeRadiusFamily001.lean) |
| Conditional global positivity: strict base bottom PLUS unproved no-null condition | `RhGlobalNoNullCriterion.global_native_positive_of_no_null` | [source](WeilForm/RhGlobalNoNullCriterion001.lean) |
| Local finite-point jet coefficient exclusion | `RhLocalFiniteJetFunctional.coefficients_zero` | [source](WeilForm/RhLocalFiniteJetFunctional001.lean) |

The ground value uses the physical L2 norm of the **primitive**, not the derivative input. The intermediate zero is not asserted to be the minimal first-zero radius. Form-dual inverses are constructed weak solutions; equality with an associated unbounded-operator inverse is not silently assumed. The finite-point representation and actual exterior-flux vanishing remain separate hypotheses/obligations.

Seven small utility modules are proof-preserving extracts: their 14 selected declaration statements/proof bodies match the originals exactly. Their import headers omit unrelated endpoint-matrix proofs. See `utility_excerpts` in [the manifest](REPLAY-MANIFEST.json). The original source hashes are recorded; historical logs, binary objects and research archives are not distributed.
