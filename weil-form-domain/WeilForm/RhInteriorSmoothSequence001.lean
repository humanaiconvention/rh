import RhInteriorSmoothDensity001

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RhInteriorSmoothSequence
open RhAnchored RhInteriorSmoothDensity

/-- An actual sequence with strict interior smooth compact support and physical
squared L2 error tending to zero; these convergence hypotheses are constructed. -/
theorem exists_interior_smooth_sequence {R : ℝ} (hR : 0 < R) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) :
    ∃ u : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      (∀ n, tsupport (u n) ⊆ Ioo (-R) R) ∧
      (∀ n, MemLp (u n) 2 (physicalMeasure R)) ∧
      Tendsto (fun n => ∫ t in interval R, (u n t - v t)^2) atTop (𝓝 0) := by
  have hex (n : ℕ) := exists_interior_smooth_approx hR hv
    (eps := 1 / ((n : ℝ) + 1)) (by positivity)
  choose u huSmooth huCompact huSupp huMem huErr using hex
  refine ⟨u, huSmooth, huCompact, huSupp, huMem, ?_⟩
  have hnorm : Tendsto (fun n => ‖(huMem n).toLp (u n) - hv.toLp v‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => (huErr n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have he (n : ℕ) : (∫ t in interval R, (u n t - v t)^2) =
      ‖(huMem n).toLp (u n) - hv.toLp v‖^2 := by
    rw [← MemLp.toLp_sub, RhDilationRank.norm_sq_toLp]
    rfl
  simp_rw [he]
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using hnorm.pow 2

end RhInteriorSmoothSequence
#print axioms RhInteriorSmoothSequence.exists_interior_smooth_sequence
