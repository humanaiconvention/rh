import RhNativeArchDilationControl001
import RhNativeRankDilationControl001
import RhNativePrimeDilationControl001

/-! Genuine local graph-form smallness of the ACTUAL full signed complete
arithmetic perturbation on one fixed actual real core and one fixed finite
prime horizon. All components are identified before their continuity budgets
are combined. No sign, spectral gap, or Schur residual inequality is assumed.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhNativeDilationSmallness
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhPulledCompleteForm RhNativeRankDilationControl RhNativePrimeDilationControl

/-- Exact physical L2 invariance, so the native scalar term costs nothing. -/
lemma scalar_mass_invariant {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace R) :
    spatialPair (RhFlatCoreDilation.outwardMap hr F : WeightedSpace)
      (RhFlatCoreDilation.outwardMap hr F : WeightedSpace) =
      spatialPair (F : WeightedSpace) (F : WeightedSpace) := by
  rw [spatialPair_apply, spatialPair_apply, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  change ‖physicalEmbedding (RhWeightedDilation.outwardLift hr (F : WeightedSpace)
    (flatCore_supported R F.property))‖^2 = ‖physicalEmbedding (F : WeightedSpace)‖^2
  rw [RhWeightedDilation.outwardLift_physical]
  exact RhWeightedDilation.dilatedPhysical_norm_square (by linarith : 0 < r)
    (F : WeightedSpace) (flatCore_supported R F.property)

/-- Exact full signed diagonal: complete arch energy, BOTH signed ranks, and
the ENTIRE finite arithmetic aggregate. No mixed companion is discarded. -/
theorem difference_diagonal_components {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (F : FlatCoreSpace R) :
    let U : WeightedSpace := RhFlatCoreDilation.outwardMap hr F
    differenceForm hr C N F F =
      (archPair U U - archPair (F : WeightedSpace) (F : WeightedSpace)) +
      (rankValue (r * R) U - rankValue R (F : WeightedSpace)) -
      (arithmeticValue N U - arithmeticValue N (F : WeightedSpace)) := by
  dsimp only
  rw [differenceForm_apply, pulledForm_apply, baseForm_apply]
  change archPair _ _ + boundedPart (r * R) C N _ _ -
    (archPair _ _ + boundedPart R C N _ _) = _
  rw [boundedPart_apply, boundedPart_apply, scalar_mass_invariant hr F]
  unfold rankValue arithmeticValue
  ring

/-- Full actual local diagonal form continuity. The radius and finite horizon
are fixed BEFORE choosing delta; this theorem does not control an increasing
horizon or guarantee preservation of a zero eigenvalue's sign. -/
theorem uniform_actual_graph_form_smallness {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (r : ℝ) (hr : 1 ≤ r), |r - 1| < delta →
      ∀ F : FlatCoreSpace R, |differenceForm hr C N F F| ≤ eta * ‖F‖^2 := by
  obtain ⟨K, hK, hRank⟩ := exists_flat_rank_graph_budget hR
  obtain ⟨d, hd, hPrime⟩ := uniform_native_prime_graph_budget N (eta := eta / 2) (by positivity)
  let delta := min 1 (min d (eta / (2 * (5 + K))))
  have hden : 0 < 2 * (5 + K) := by positivity
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (by norm_num) (lt_min hd (div_pos heta hden))
  refine ⟨delta, hdelta, ?_⟩
  intro r hr hclose F
  have hnonneg : 0 ≤ r - 1 := sub_nonneg.mpr hr
  have hOne : r - 1 < 1 := by
    have hh := hclose.trans_le (min_le_left 1 (min d (eta / (2 * (5 + K)))))
    simpa only [abs_of_nonneg hnonneg] using hh
  have hr2 : r ≤ 2 := by linarith
  have hprimeClose : |r - 1| < d :=
    hclose.trans_le ((min_le_right 1 (min d (eta / (2 * (5 + K))))).trans
      (min_le_left d (eta / (2 * (5 + K)))))
  have hStep : (5 + K) * (r - 1) ≤ eta / 2 := by
    have hh := hclose.trans_le ((min_le_right 1 (min d (eta / (2 * (5 + K))))).trans
      (min_le_right d (eta / (2 * (5 + K)))))
    rw [abs_of_nonneg hnonneg] at hh
    have hm := (le_div_iff₀ hden).mp hh.le
    nlinarith
  let U : WeightedSpace := RhFlatCoreDilation.outwardMap hr F
  let a := archPair U U - archPair (F : WeightedSpace) (F : WeightedSpace)
  let b := rankValue (r * R) U - rankValue R (F : WeightedSpace)
  let c := arithmeticValue N U - arithmeticValue N (F : WeightedSpace)
  have hArch : |a| ≤ 5 * (r - 1) * ‖F‖^2 := by
    have ha := RhNativeArchDilationControl.flat_arch_graph_budget hr F
    have hl := Real.log_le_sub_one_of_pos (by linarith : 0 < r)
    exact ha.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 5)) (sq_nonneg ‖F‖))
  have hRk : |b| ≤ K * (r - 1) * ‖F‖^2 := hRank r hr hr2 F
  have hPr : |c| ≤ (eta / 2) * ‖F‖^2 := hPrime R r hr hprimeClose F
  have hT := abs_add_le a b
  have hS := abs_sub_le (a + b) 0 c
  simp only [sub_zero, zero_sub, abs_neg] at hS
  have hExact : differenceForm hr C N F F = a + b - c := difference_diagonal_components hr C N F
  rw [hExact]
  have hPay := mul_le_mul_of_nonneg_right hStep (sq_nonneg ‖F‖)
  nlinarith

end RhNativeDilationSmallness
#print axioms RhNativeDilationSmallness.scalar_mass_invariant
#print axioms RhNativeDilationSmallness.difference_diagonal_components
#print axioms RhNativeDilationSmallness.uniform_actual_graph_form_smallness
