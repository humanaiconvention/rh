import RhCompactPositiveSequence001

/-! Conditional PHYSICAL complement gap from actual compact embedding and
positive complete graph form. No gap or coercivity is among the premises. -/
set_option maxHeartbeats 0
noncomputable section
open Filter Set
open scoped Topology
namespace RhCompactPhysicalGap
variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def PhysicallyOrthogonalToZeros (q : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] H) (x : V) : Prop :=
  ∀ z : V, q z z = 0 → inner ℝ (J x) (J z) = 0

/-- The physical positive gap is derived, conditional only on complete-form
positivity at the radius in question and the proved compact graph embedding. -/
theorem physical_gap (q : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] H) (hJ : IsCompactOperator J)
    {G : ℝ} (hG : 0 ≤ G) (hq : ∀ x : V, 0 ≤ q x x)
    (hgraph : ∀ x : V, ‖x‖^2 ≤ q x x + G*‖J x‖^2) :
    ∃ mu : ℝ, 0 < mu ∧ ∀ x : V,
      PhysicallyOrthogonalToZeros q J x → mu*‖J x‖^2 ≤ q x x := by
  by_contra hn
  push_neg at hn
  have hbad (n : ℕ) : ∃ x : V, PhysicallyOrthogonalToZeros q J x ∧
      q x x < (1/((n : ℝ)+1))*‖J x‖^2 := hn _ (by positivity)
  choose x hxorth hxsmall using hbad
  have hJne (n : ℕ) : ‖J (x n)‖ ≠ 0 := by
    intro hh
    have hs := hxsmall n
    rw [hh] at hs
    nlinarith [hq (x n)]
  let y : ℕ → V := fun n => ‖J (x n)‖⁻¹ • x n
  have hynorm (n : ℕ) : ‖J (y n)‖ = 1 := by
    simp only [y, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (hJne n)]
  have hyenergy (n : ℕ) : q (y n) (y n) ≤ 1/((n : ℝ)+1) := by
    have hh := mul_le_mul_of_nonneg_left (hxsmall n).le (sq_nonneg (‖J (x n)‖⁻¹))
    have he : q (y n) (y n) = (‖J (x n)‖⁻¹)^2*q (x n) (x n) := by
      simp only [y, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, pow_two]
      ring
    rw [he]
    calc
      _ ≤ (‖J (x n)‖⁻¹)^2 * ((1/((n : ℝ)+1))*‖J (x n)‖^2) := hh
      _ = _ := by field_simp [hJne n]
  have hyorth (n : ℕ) : PhysicallyOrthogonalToZeros q J (y n) := by
    intro z hz
    change inner ℝ (J (‖J (x n)‖⁻¹ • x n)) (J z) = 0
    rw [map_smul, real_inner_smul_left, hxorth n z hz, mul_zero]
  have hb (n : ℕ) : ‖y n‖ ≤ G+2 := by
    have hg := hgraph (y n)
    rw [hynorm n] at hg
    have he := hyenergy n
    have hunit : 1/((n : ℝ)+1) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < (n : ℝ)+1)).mpr
      have hh : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    nlinarith [norm_nonneg (y n), sq_nonneg G]
  have hden : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n => q (y n) (y n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => hq (y n)) hyenergy (by
      simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hden)
  obtain ⟨z,phi,hphi,ht,hzero⟩ := RhCompactPositiveSequence.compact_zero_subsequence
    q J hJ hG hq hgraph y hb he
  have hJt : Tendsto (fun n => J (y (phi n))) atTop (𝓝 (J z)) :=
    (J.continuous.tendsto z).comp ht
  have hnlimit : ‖J z‖ = 1 := by
    apply tendsto_nhds_unique hJt.norm
    simpa only [hynorm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hzeroInner : inner ℝ (J z) (J z) = 0 := by
    apply tendsto_nhds_unique (hJt.inner tendsto_const_nhds)
    have hzeroSeq (n : ℕ) : inner ℝ (J (y (phi n))) (J z) = 0 := hyorth (phi n) z hzero
    simpa only [hzeroSeq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  rw [real_inner_self_eq_norm_sq, hnlimit] at hzeroInner
  norm_num at hzeroInner

end RhCompactPhysicalGap
#print axioms RhCompactPhysicalGap.physical_gap


