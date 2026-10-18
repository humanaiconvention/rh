import RhNativeNullFlux001
import RhSmoothPhysicalTransfer001

/-! If a hypothetical old null vector has NONZERO COMPLETE outward flux,
its negative form witness transfers to an actual strict-interior smooth
physical derivative. No actual flux or null vector is declared nonzero. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace RhNativeNullFluxPhysical
open RhAnchored RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear

/-- Exact conditional failure witness for the native finite-horizon kernel.
Choosing N=radiusCutoff S makes the conclusion the actual S-radius kernel. -/
theorem complete_flux_nonzero_gives_physical_negative {R S : ℝ}
    (hRS : R ≤ S) (hS : 0 < S) (N : ℕ)
    (p : FlatCoreSpace R) (g : FlatCoreSpace S)
    (hp : completeForm R archConstant N (p : WeightedSpace) (p : WeightedSpace) = 0)
    (hb : completeForm S archConstant N (p : WeightedSpace) (g : WeightedSpace) ≠ 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo (-S) S ∧
      kernelQuadratic S (RhAllPrime.completeKernel N) (deriv f) < 0 := by
  obtain ⟨x, hx⟩ := RhNativeNullFlux.nonzero_total_flux_negative_witness hRS archConstant N p g hp hb
  apply RhSmoothPhysicalTransfer.negative_form_has_smooth_derivative hS N x
  rw [hx]
  norm_num

end RhNativeNullFluxPhysical
#print axioms RhNativeNullFluxPhysical.complete_flux_nonzero_gives_physical_negative
