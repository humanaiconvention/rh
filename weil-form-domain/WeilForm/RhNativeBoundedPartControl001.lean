import RhNativeCompleteBilinear001

/-! Native finite bounded-part control on the entire actual weighted Hilbert
space, including COMPLEX physical vectors regarded over the reals. This is a
semibounded-form norm estimate, not positivity of the signed arithmetic form.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhNativeBoundedPartControl
open RhAnchored RhWeightedMeasureEmbedding RhWeightedPrimitiveLift
open RhNativeCompleteBilinear

lemma translation_norm (u : WholeSpace) (ell : ℝ) : ‖translation ell u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u (measurePreserving_add_right volume ell)

lemma twoShift_norm_bound (u : WholeSpace) (ell : ℝ) : ‖twoShift ell u‖ ≤ 2 * ‖u‖ := by
  change ‖translation ell u + translation (-ell) u‖ ≤ _
  calc
    _ ≤ ‖translation ell u‖ + ‖translation (-ell) u‖ := norm_add_le _ _
    _ = _ := by rw [translation_norm, translation_norm]; ring

/-- Native spatial two-shift norm estimate, no missing signed translation. -/
theorem shiftPair_mass_bound (ell : ℝ) (F : WeightedSpace) :
    |shiftPair ell F F| ≤ 2 * ‖physicalEmbedding F‖ ^ 2 := by
  rw [shiftPair_diagonal]
  calc
    _ ≤ ‖physicalEmbedding F‖ * ‖twoShift ell (physicalEmbedding F)‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖physicalEmbedding F‖ * (2 * ‖physicalEmbedding F‖) :=
      mul_le_mul_of_nonneg_left (twoShift_norm_bound _ ell) (norm_nonneg _)
    _ = _ := by ring

/-- Both real and imaginary components of each actual complex moment are
controlled; this is a bound on the whole complex moment norm. -/
theorem profilePair_mass_bound (R : ℝ) (f : ℝ → ℝ)
    (hf : MemLp f 2 (physicalMeasure R)) (F : WeightedSpace) :
    0 ≤ profilePair R f hf F F ∧
    profilePair R f hf F F ≤ (∫ t in interval R, (f t)^2) * ‖physicalEmbedding F‖^2 := by
  rw [profilePair_diagonal]
  refine ⟨sq_nonneg _, ?_⟩
  have h : ‖profileMoment R f hf F‖ ≤
      ‖RhTail.physicalFourierVector R f hf‖ * ‖physicalEmbedding F‖ := by
    change ‖inner ℂ (RhTail.physicalFourierVector R f hf) (physicalEmbedding F)‖ ≤ _
    exact norm_inner_le_norm _ _
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, physicalVector_norm_square hf] at hs
  exact hs

/-- Full signed bounded part is controlled with EXACTLY the saved native K_R.
No altered rank coefficient, omitted imaginary moment, or support assumption
is needed. This bound holds for every weighted vector, not just a test core. -/
theorem boundedPart_mass_bound (R C : ℝ) (N : ℕ) (F : WeightedSpace) :
    |boundedPart R C N F F| ≤
      RhCompleteFormBound.boundConstant R C N * ‖physicalEmbedding F‖^2 := by
  let mass := ‖physicalEmbedding F‖^2
  let cp := coshPair R F F
  let sp := sinhPair R F F
  let ar := ∑ n ∈ Finset.Icc 2 N,
    RhAllPrime.weight n * shiftPair (Real.log (n : ℝ)) F F
  have hm : 0 ≤ mass := sq_nonneg _
  have hcp := profilePair_mass_bound R (fun t => Real.cosh (t / 2)) (cosh_memLp R) F
  have hsp := profilePair_mass_bound R (fun t => Real.sinh (t / 2)) (sinh_memLp R) F
  change 0 ≤ cp ∧ cp ≤ (∫ t in interval R, (Real.cosh (t / 2))^2) * mass at hcp
  change 0 ≤ sp ∧ sp ≤ (∫ t in interval R, (Real.sinh (t / 2))^2) * mass at hsp
  have har : |ar| ≤ 2 * (∑ n ∈ Finset.Icc 2 N, |RhAllPrime.weight n|) * mass :=
    RhCompleteFormBound.finite_weighted_abs_bound (Finset.Icc 2 N)
      RhAllPrime.weight (fun n => shiftPair (Real.log (n : ℝ)) F F) mass
      (fun n _ => shiftPair_mass_bound _ F)
  have h1 := abs_add_le (-C * mass) (2 * cp)
  have h2 := abs_sub_le (-C * mass + 2 * cp) 0 (2 * sp)
  have h3 := abs_sub_le (-C * mass + 2 * cp - 2 * sp) 0 ar
  simp only [sub_zero, zero_sub, abs_neg] at h2 h3
  have ha : |-C * mass| = |C| * mass := by rw [abs_mul, abs_neg, abs_of_nonneg hm]
  have hc : |2 * cp| = 2 * cp := abs_of_nonneg (mul_nonneg (by norm_num) hcp.1)
  have hs : |2 * sp| = 2 * sp := abs_of_nonneg (mul_nonneg (by norm_num) hsp.1)
  rw [ha, hc] at h1
  rw [hs] at h2
  rw [boundedPart_apply, spatialPair_apply, real_inner_self_eq_norm_sq]
  change |-C * mass + 2 * cp - 2 * sp - ar| ≤ _
  unfold RhCompleteFormBound.boundConstant RhCompleteFormBound.rankCost
  nlinarith [hcp.2, hsp.2]

end RhNativeBoundedPartControl
#print axioms RhNativeBoundedPartControl.shiftPair_mass_bound
#print axioms RhNativeBoundedPartControl.profilePair_mass_bound
#print axioms RhNativeBoundedPartControl.boundedPart_mass_bound
