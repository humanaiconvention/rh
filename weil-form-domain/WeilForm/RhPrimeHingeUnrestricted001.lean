import RhPrimeHingePrimitive001

/-!
Unrestricted positive-shift hinge identity for the actual anchored primitive.
The six shifted trace locations are excluded only almost everywhere. No
first-window geometric assumption A < L is used.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval BigOperators

namespace RhPrimeHingeUnrestricted
open RhAnchored RhSupportPrimeHinge RhPrimeHingePrimitive

lemma hingeConvolution_difference {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (L t : ℝ) :
    hingeConvolution A L (primitive A v) t - hingeConvolution A L (primitive A v) 0 =
      shiftFlux A L (primitive A v) t := by
  rw [hingeConvolution_eq_cumulative hA hv L t,
    hingeConvolution_eq_cumulative hA hv L 0]
  simp only [zero_sub, zero_add]
  unfold shiftFlux
  ring

/-- The only excluded locations are the translated zero and support traces. -/
theorem shiftFlux_ae_deriv_unrestricted {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (L : ℝ) :
    ∀ᵐ t ∂physicalMeasure A,
      deriv (shiftFlux A L (primitive A v)) t = primeShift A L (primitive A v) t := by
  apply ae_restrict_of_ae
  filter_upwards [ae_ne_const L, ae_ne_const (L - A), ae_ne_const (L + A),
    ae_ne_const (-L), ae_ne_const (-L - A), ae_ne_const (A - L)]
      with t h0 h1 h2 h3 h4 h5
  apply HasDerivAt.deriv
  apply shiftFlux_hasDerivAt_regular hA hv
  · intro he
    apply h0
    linarith
  · intro he
    apply h1
    linarith
  · intro he
    apply h2
    linarith
  · intro he
    apply h3
    linarith
  · intro he
    apply h4
    linarith
  · intro he
    apply h5
    linarith

lemma firstFlux_hinge_difference {A L : ℝ} (hA : 0 < A) (hL : 0 < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (alpha t : ℝ) :
    firstFlux A 0 alpha L 0 (primitive A v) t -
        firstFlux A 0 0 L 0 (primitive A v) t =
      alpha * shiftFlux A L (primitive A v) t := by
  rw [firstFlux_eq_slope_difference hA hL hv 0 alpha 0,
    firstFlux_eq_slope_difference hA hL hv 0 0 0]
  simp only [potentialSlopeConvolution_expansion hA hv, Finset.sum_range_zero,
    zero_div, zero_mul, sub_zero, add_zero]
  linear_combination alpha * hingeConvolution_difference hA hv L t

/-- Exact row identity; both anchored lower-boundary companions are retained. -/
theorem physical_row_identity {A L : ℝ} (hA : 0 < A) (hL : 0 < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (alpha t : ℝ) :
    (∫ u in interval A, primeHinge alpha L t u * v u) =
      alpha * shiftFlux A L (primitive A v) t := by
  have hrowA := finiteKernel_row_integrable hA hv 0 alpha L 0 t
  have hrow0 := finiteKernel_row_integrable hA hv 0 0 L 0 t
  have hfirstA : (∫ u in interval A, finiteKernel 0 alpha L 0 t u * v u) =
      firstFlux A 0 alpha L 0 (primitive A v) t := by
    simpa only [firstFlux] using finiteKernel_first_parts hA hv 0 alpha L 0 t
  have hfirst0 : (∫ u in interval A, finiteKernel 0 0 L 0 t u * v u) =
      firstFlux A 0 0 L 0 (primitive A v) t := by
    simpa only [firstFlux] using finiteKernel_first_parts hA hv 0 0 L 0 t
  calc
    _ = ∫ u in interval A,
        finiteKernel 0 alpha L 0 t u * v u - finiteKernel 0 0 L 0 t u * v u := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun u => by
        dsimp only
        rw [primeHinge_as_difference]
        ring)
    _ = (∫ u in interval A, finiteKernel 0 alpha L 0 t u * v u) -
        (∫ u in interval A, finiteKernel 0 0 L 0 t u * v u) :=
      integral_sub hrowA hrow0
    _ = _ := by rw [hfirstA, hfirst0, firstFlux_hinge_difference hA hL hv]

lemma shiftFlux_pairing {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (L : ℝ) :
    (∫ t in interval A, shiftFlux A L (primitive A v) t * v t) =
      -(∫ t in interval A, primeShift A L (primitive A v) t * primitive A v t) := by
  have hw := primitive_parts_setIntegral_anchored hA hv (shiftFlux_ac hv L)
    (shiftFlux_zero A L (primitive A v))
  calc
    _ = ∫ t in interval A, v t * shiftFlux A L (primitive A v) t := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => mul_comm _ _)
    _ = -(∫ t in interval A, primitive A v t * deriv (shiftFlux A L (primitive A v)) t) := hw
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [shiftFlux_ae_deriv_unrestricted hA hv L] with t ht
      rw [ht]
      ring

/-- The actual physical hinge equals its two-delay primitive form for every
positive support radius and every positive shift, without `A < L`. -/
theorem physical_primitive_identity {A L : ℝ} (hA : 0 < A) (hL : 0 < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (alpha : ℝ) :
    kernelQuadratic A (primeHinge alpha L) v =
      -alpha * (∫ t in interval A,
        primeShift A L (primitive A v) t * primitive A v t) := by
  unfold kernelQuadratic
  calc
    _ = ∫ t in interval A, (alpha * shiftFlux A L (primitive A v) t) * v t := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by
        dsimp only
        rw [integral_mul_const, physical_row_identity hA hL hv])
    _ = alpha * (∫ t in interval A, shiftFlux A L (primitive A v) t * v t) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by ring)
    _ = _ := by rw [shiftFlux_pairing hA hv L]; ring

end RhPrimeHingeUnrestricted

#print axioms RhPrimeHingeUnrestricted.hingeConvolution_difference
#print axioms RhPrimeHingeUnrestricted.shiftFlux_ae_deriv_unrestricted
#print axioms RhPrimeHingeUnrestricted.physical_row_identity
#print axioms RhPrimeHingeUnrestricted.physical_primitive_identity
