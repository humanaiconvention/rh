import RhNativeRayleighLeft001

/-! Actual continuous finite-horizon primitive ground value on positive radii.
The imported exact support/graph estimates provide continuity; its sign and
zero-mode arithmetic compensation remain unproved. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhNativeRayleighContinuity
open RhNativeRayleighDomain RhNativeRayleighRadius RhNativeRayleighLeft

/-- A two-sided physical-radius neighborhood, with no moving-base estimate. -/
theorem radius_neighborhood {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ S : ℝ, |S-R| < delta →
      |bottom S C N-bottom R C N| < eps := by
  obtain ⟨dl,hdl,hl⟩ := left_continuity hR C N heps
  obtain ⟨dr,hdr,hright⟩ := right_continuity hR C N heps
  refine ⟨min dl (R*dr),lt_min hdl (mul_pos hR hdr),?_⟩
  intro S hS
  by_cases hSR : S ≤ R
  · apply hl S _ hSR
    have hh := (abs_lt.mp (hS.trans_le (min_le_left _ _))).1
    linarith
  · have hRS : R ≤ S := (lt_of_not_ge hSR).le
    let r := S/R
    have hr : 1 ≤ r := (le_div_iff₀ hR).mpr (by simpa only [one_mul] using hRS)
    have he : r*R = S := div_mul_cancel₀ S hR.ne'
    have hdiff : r-1 = (S-R)/R := by dsimp only [r]; field_simp
    have hh : |r-1| < dr := by
      rw [hdiff,abs_div,abs_of_pos hR]
      apply (div_lt_iff₀ hR).mpr
      simpa only [mul_comm] using hS.trans_le (min_le_right _ _)
    have hc := hright r hr hh
    rwa [he] at hc

/-- Native continuity at every positive radius, under one literal finite N. -/
theorem bottom_continuousAt {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ) :
    ContinuousAt (fun S : ℝ => bottom S C N) R := by
  apply Metric.continuousAt_iff.mpr
  intro eps heps
  obtain ⟨delta,hd,hc⟩ := radius_neighborhood hR C N heps
  refine ⟨delta,hd,?_⟩
  intro S hS
  simpa only [Real.dist_eq] using hc S (by simpa only [Real.dist_eq] using hS)

theorem bottom_continuousOn (C : ℝ) (N : ℕ) :
    ContinuousOn (fun R : ℝ => bottom R C N) (Ioi 0) := by
  intro R hR
  exact (bottom_continuousAt hR C N).continuousWithinAt

end RhNativeRayleighContinuity
#print axioms RhNativeRayleighContinuity.radius_neighborhood
#print axioms RhNativeRayleighContinuity.bottom_continuousAt
#print axioms RhNativeRayleighContinuity.bottom_continuousOn
