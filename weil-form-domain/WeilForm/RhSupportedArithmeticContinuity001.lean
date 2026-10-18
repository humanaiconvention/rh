import RhPhysicalShiftFourier001
import RhAllPrimeKernel001

/-! Exact support-threshold vanishing and finite-horizon arithmetic form
continuity. Absolute coefficient sums occur only in an auxiliary continuity
constant. The prescribed signed arithmetic sum itself remains unchanged. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators
namespace RhSupportedArithmeticContinuity
open RhWeightedMeasureEmbedding RhPhysicalShiftFourier

lemma shifted_pair_zero {R ell : ℝ} (hgap : 2 * R ≤ |ell|)
    {F G : WeightedSpace} (hF : F ∈ supportedSubspace R) (hG : G ∈ supportedSubspace R) :
    (∫ t, inner ℝ (physicalEmbedding F t) (physicalEmbedding G (t + ell))) = 0 := by
  have hf := (mem_supportedSubspace_iff R F).mp hF
  have hg := (mem_supportedSubspace_iff R G).mp hG
  have hgt := (measurePreserving_add_right volume ell).quasiMeasurePreserving.ae hg
  apply integral_eq_zero_of_ae
  filter_upwards [hf, hgt, (volume : Measure ℝ).ae_ne (-R),
    (volume : Measure ℝ).ae_ne R] with t hft hgt' hneg hpos
  by_cases ht : t ∈ Icc (-R) R
  · have hlo : -R < t := lt_of_le_of_ne ht.1 (Ne.symm hneg)
    have hhi : t < R := lt_of_le_of_ne ht.2 hpos
    have hout : t + ell ∉ Icc (-R) R := by
      intro h
      have hab : |ell| < 2 * R := abs_lt.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
      linarith
    rw [hgt' hout]
    simp
  · rw [hft ht]
    simp

/-- Equality at the support boundary is included: the only possible overlap
is confined to null endpoint sets, not silently discarded pointwise. -/
theorem spatialPair_zero_of_threshold {R ell : ℝ} (hgap : 2 * R ≤ |ell|)
    {F G : WeightedSpace} (hF : F ∈ supportedSubspace R) (hG : G ∈ supportedSubspace R) :
    spatialPair (physicalEmbedding F) (physicalEmbedding G) ell = 0 := by
  unfold spatialPair
  simp_rw [sub_eq_add_neg]
  rw [integral_add (shifted_integrable _ _ ell) (shifted_integrable _ _ (-ell)),
    shifted_pair_zero hgap hF hG,
    shifted_pair_zero (by simpa only [abs_neg] using hgap) hF hG, add_zero]

/-- The actual finite arithmetic spatial sum, with every prescribed prime-power
coefficient and both delays. The horizon is fixed and explicit. -/
def arithmeticPair (N : ℕ) (r : ℝ) (F G : WeightedSpace) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, RhAllPrime.weight n *
    spatialPair (physicalEmbedding F) (physicalEmbedding G) (Real.log (n : ℝ) / r)

/-- Continuity of the complete fixed-horizon arithmetic aggregate in its
dilation parameter, in the actual native graph norm. No cancellation or sign
conclusion is extracted from the auxiliary finite continuity constant. -/
theorem uniform_finite_arithmetic_continuity (N : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (R r : ℝ), |r - 1| < delta →
      ∀ (F G : WeightedSpace), F ∈ supportedSubspace R → G ∈ supportedSubspace R →
      |arithmeticPair N r F G - arithmeticPair N 1 F G| ≤ eta * ‖F‖ * ‖G‖ := by
  let c : ℝ := ∑ n ∈ Finset.Icc 2 N, |RhAllPrime.weight n|
  have hc : 0 ≤ c := Finset.sum_nonneg (fun n _ => abs_nonneg _)
  obtain ⟨d, hd, hs⟩ := uniform_supported_spatial_shift (eta := eta / (c + 1)) (by positivity)
  have hn : ∀ n ∈ Finset.Icc 2 N,
      ContinuousAt (fun r : ℝ => Real.log (n : ℝ) / r) 1 := by
    intro n hn
    exact continuousAt_const.div continuousAt_id (by norm_num)
  have hevent : ∀ᶠ r : ℝ in 𝓝 1, ∀ n ∈ Finset.Icc 2 N,
      |Real.log (n : ℝ) / r - Real.log (n : ℝ)| < d := by
    apply (Finset.eventually_all _).mpr
    intro n hn'
    have h := (hn n hn').tendsto.eventually (Metric.ball_mem_nhds _ hd)
    simpa only [Metric.mem_ball, Real.dist_eq, div_one] using h
  obtain ⟨delta, hdelta, hsub⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨delta, hdelta, ?_⟩
  intro R r hr F G hF hG
  have hclose := hsub (by simpa only [Metric.mem_ball, Real.dist_eq] using hr)
  have hpair (n : ℕ) (hn : n ∈ Finset.Icc 2 N) :
      |spatialPair (physicalEmbedding F) (physicalEmbedding G) (Real.log (n : ℝ) / r) -
        spatialPair (physicalEmbedding F) (physicalEmbedding G) (Real.log (n : ℝ))| ≤
        (eta / (c + 1)) * ‖F‖ * ‖G‖ :=
    hs R _ _ (hclose n hn) F G hF hG
  have heq : arithmeticPair N r F G - arithmeticPair N 1 F G =
      ∑ n ∈ Finset.Icc 2 N, RhAllPrime.weight n *
        (spatialPair (physicalEmbedding F) (physicalEmbedding G) (Real.log (n : ℝ) / r) -
          spatialPair (physicalEmbedding F) (physicalEmbedding G) (Real.log (n : ℝ))) := by
    unfold arithmeticPair
    simp only [div_one, ← Finset.sum_sub_distrib, mul_sub]
  rw [heq]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 2 N, |RhAllPrime.weight n *
        (spatialPair (physicalEmbedding F) (physicalEmbedding G) (Real.log (n : ℝ) / r) -
          spatialPair (physicalEmbedding F) (physicalEmbedding G) (Real.log (n : ℝ)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 2 N, |RhAllPrime.weight n| *
        ((eta / (c + 1)) * ‖F‖ * ‖G‖) := by
      apply Finset.sum_le_sum
      intro n hn'
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hpair n hn') (abs_nonneg _)
    _ = c * ((eta / (c + 1)) * ‖F‖ * ‖G‖) := by
      rw [← Finset.sum_mul]
    _ ≤ eta * ‖F‖ * ‖G‖ := by
      have hh : c * (eta / (c + 1)) ≤ eta := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0 < c + 1)).mpr
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hh (norm_nonneg F)) (norm_nonneg G)]

end RhSupportedArithmeticContinuity
#print axioms RhSupportedArithmeticContinuity.spatialPair_zero_of_threshold
#print axioms RhSupportedArithmeticContinuity.uniform_finite_arithmetic_continuity
