import RhNativeFirstZeroReduction001

/-! Exact local non-stalling under the explicit absence of actual nullvectors.
This conditional input is the arithmetic frontier, not a proven property at
arbitrary radii. The physical norm is that of the primitive, never its derivative. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhNativeNoNullOpenness
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhNativeRayleighDomain RhNativeRayleighPositivity RhNativeRayleighContinuity
open RhNativeCompactGap

theorem positive_bottom_of_positive_no_null {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ F : FlatCoreSpace R,
      0 ≤ completeForm R C N (F : WeightedSpace) (F : WeightedSpace))
    (hno : ∀ F : FlatCoreSpace R, F ∈ (form R C N).ker → F = 0) :
    0 < bottom R C N := by
  obtain ⟨mu,hmu,hgap⟩ := physical_complement_gap hR C N hpos
  have hunit : ∀ F ∈ physicalUnit R, mu ≤ diagonal R C N F := by
    intro F hF
    have hh := hgap F (by
      intro z hz
      simp only [hno z hz,map_zero,inner_zero_right])
    change mu*‖physicalEmbedding (F : WeightedSpace)‖^2 ≤ diagonal R C N F at hh
    rw [hF] at hh
    simpa using hh
  have hlow : mu ≤ bottom R C N := by
    apply le_csInf ((physicalUnit_nonempty hR).image (diagonal R C N))
    rintro y ⟨F,hF,rfl⟩
    exact hunit F hF
  exact hmu.trans_le hlow

/-- Strict primitive coercivity has a genuine two-sided neighborhood.
No width or all-radius renewable numerical margin is asserted. -/
theorem local_positive_neighborhood {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ F : FlatCoreSpace R,
      0 ≤ completeForm R C N (F : WeightedSpace) (F : WeightedSpace))
    (hno : ∀ F : FlatCoreSpace R, F ∈ (form R C N).ker → F = 0) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ S : ℝ, 0 < S → |S-R| < delta →
      0 < bottom S C N ∧ ∀ F : FlatCoreSpace S,
        0 ≤ completeForm S C N (F : WeightedSpace) (F : WeightedSpace) := by
  have hb := positive_bottom_of_positive_no_null hR C N hpos hno
  obtain ⟨delta,hd,hc⟩ := radius_neighborhood hR C N (show 0 < bottom R C N/2 by positivity)
  refine ⟨delta,hd,?_⟩
  intro S hS hnear
  have hh := (abs_lt.mp (hc S hnear)).1
  have hsbot : 0 < bottom S C N := by linarith
  exact ⟨hsbot,(bottom_nonnegative_iff hS C N).mp hsbot.le⟩

end RhNativeNoNullOpenness
#print axioms RhNativeNoNullOpenness.positive_bottom_of_positive_no_null
#print axioms RhNativeNoNullOpenness.local_positive_neighborhood
