import RhAnchoredKernel001

/-!
An explicitly conditional assembly lemma. Its two convolution hypotheses
remain obligations; this file does not assert the complete finite-J identity.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

def firstFlux (A C α L : ℝ) (J : ℕ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(∫ u in interval A, w u * deriv (fun y => finiteKernel C α L J t y) u)

lemma firstFlux_zero (A C α L : ℝ) (J : ℕ) (w : ℝ → ℝ) :
    firstFlux A C α L J w 0 = 0 := by
  have h : (fun y => finiteKernel C α L J 0 y) = (fun _ : ℝ => (0 : ℝ)) := by
    funext y
    exact finiteKernel_zero_left C α L J y
  simp [firstFlux, h]

theorem finite_J_identity_of_flux_derivative {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α L : ℝ) (J : ℕ)
    (hflux : AbsolutelyContinuousOnInterval
      (firstFlux A C α L J (primitive A v)) (-A) A)
    (hderiv : ∀ᵐ t ∂physicalMeasure A,
      deriv (firstFlux A C α L J (primitive A v)) t =
      -nativeOperator A C α L J (primitive A v) t) :
    (∫ t in interval A, ∫ u in interval A, finiteKernel C α L J t u * v u * v t) =
    ∫ t in interval A, nativeOperator A C α L J (primitive A v) t * primitive A v t := by
  have hfirst (t : ℝ) : (∫ u in interval A, finiteKernel C α L J t u * v u) =
      firstFlux A C α L J (primitive A v) t := finiteKernel_first_parts hA hv C α L J t
  have hweak := primitive_parts_setIntegral_anchored hA hv hflux
    (firstFlux_zero A C α L J (primitive A v))
  have hconverted : -(∫ t in interval A,
      primitive A v t * deriv (firstFlux A C α L J (primitive A v)) t) =
      ∫ t in interval A, nativeOperator A C α L J (primitive A v) t * primitive A v t := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hderiv] with t ht
    simp only [ht]
    ring
  calc
    _ = ∫ t in interval A, firstFlux A C α L J (primitive A v) t*v t := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t _
      dsimp only
      rw [integral_mul_const, hfirst t]
    _ = ∫ t in interval A, v t*firstFlux A C α L J (primitive A v) t := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => mul_comm _ _)
    _ = _ := hweak.trans hconverted

end RhAnchored
#print axioms RhAnchored.finite_J_identity_of_flux_derivative
