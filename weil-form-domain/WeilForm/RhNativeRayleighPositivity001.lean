import RhNativeRayleighRadius001
import RhNativeCompactGap001

/-! Exact sign/zero dictionary for the primitive PHYSICAL L2 Rayleigh bottom.
A zero bottom is an actual null state, not merely a totalized-infimum artifact.
No radius with zero bottom is asserted to exist. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhNativeRayleighPositivity
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhNativeRayleighDomain RhNativeCompactGap

lemma physical_norm_pos {R : ℝ} {F : FlatCoreSpace R} (hF : F ≠ 0) :
    0 < ‖physicalEmbedding (F : WeightedSpace)‖ := by
  apply lt_of_le_of_ne (norm_nonneg _)
  intro hh
  apply hF
  apply physical_injective R
  change physicalEmbedding (F : WeightedSpace) = physicalEmbedding (0 : WeightedSpace)
  rw [map_zero]
  exact norm_eq_zero.mp hh.symm

lemma diagonal_smul (R C : ℝ) (N : ℕ) (c : ℝ) (F : FlatCoreSpace R) :
    diagonal R C N (c • F) = c^2 * diagonal R C N F := by
  change completeForm R C N (c • (F : WeightedSpace)) (c • (F : WeightedSpace)) = _
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  unfold RhNativeRayleighDomain.diagonal
  ring

/-- Native complete-form PSD is exactly nonnegativity of the genuine bottom. -/
theorem bottom_nonnegative_iff {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ) :
    0 ≤ bottom R C N ↔ ∀ F : FlatCoreSpace R,
      0 ≤ completeForm R C N (F : WeightedSpace) (F : WeightedSpace) := by
  constructor
  · intro hb F
    by_cases hz : F = 0
    · subst F; simp
    · have hn := physical_norm_pos hz
      let c := ‖physicalEmbedding (F : WeightedSpace)‖⁻¹
      have hc : 0 < c := inv_pos.mpr hn
      have hu : c • F ∈ physicalUnit R := by
        change ‖physicalEmbedding (c • (F : WeightedSpace))‖ = 1
        rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
        exact inv_mul_cancel₀ hn.ne'
      have hh : 0 ≤ diagonal R C N (c • F) := hb.trans (bottom_le_diagonal R C N _ hu)
      rw [diagonal_smul] at hh
      exact nonneg_of_mul_nonneg_right hh (sq_pos_of_pos hc)
  · intro hpos
    apply le_csInf ((physicalUnit_nonempty hR).image (diagonal R C N))
    rintro y ⟨F,_hF,rfl⟩
    exact hpos F

/-- If the lowest primitive energy is EXACTLY zero, there is a genuine
nonzero actual form-radical vector. This is conditional, not its construction
at any specified arithmetic radius. -/
theorem zero_bottom_has_actual_null {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hz : bottom R C N = 0) :
    ∃ F : FlatCoreSpace R, F ≠ 0 ∧ F ∈ (form R C N).ker := by
  have hpos := (bottom_nonnegative_iff hR C N).mp hz.ge
  obtain ⟨mu,hmu,hgap⟩ := physical_complement_gap hR C N hpos
  by_contra hnone
  have hker : ∀ z : FlatCoreSpace R, z ∈ (form R C N).ker → z = 0 := by
    intro z hzker
    by_contra hn
    exact hnone ⟨z,hn,hzker⟩
  have hunit : ∀ F ∈ physicalUnit R, mu ≤ diagonal R C N F := by
    intro F hF
    have hh := hgap F (by
      intro z hzker
      simp only [hker z hzker,map_zero,inner_zero_right])
    change mu*‖physicalEmbedding (F : WeightedSpace)‖^2 ≤ diagonal R C N F at hh
    rw [hF] at hh
    simpa using hh
  have hlow : mu ≤ bottom R C N := by
    apply le_csInf ((physicalUnit_nonempty hR).image (diagonal R C N))
    rintro y ⟨F,hF,rfl⟩
    exact hunit F hF
  rw [hz] at hlow
  linarith

end RhNativeRayleighPositivity
#print axioms RhNativeRayleighPositivity.bottom_nonnegative_iff
#print axioms RhNativeRayleighPositivity.zero_bottom_has_actual_null
