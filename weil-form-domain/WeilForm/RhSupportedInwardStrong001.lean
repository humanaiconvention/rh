import RhFrequencyDilationStrong001
import RhInwardFrequencyDictionary001

/-! Strong inward continuity for actual supported complete form vectors.
Canonical strictly shrinking radii are supplied for later same-window
mollifier assembly. No smooth-core density or positivity is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RhSupportedInwardStrong
open RhWeightedMeasureEmbedding RhWeightedDilationInverse RhWeightedInwardMap
open RhWeightedFrequencyDilation RhFrequencyDilationStrong RhInwardFrequencyDictionary

/-- Literal ambient weighted convergence, with the actual varying support
radii retained by inwardMap. -/
theorem supported_inward_norm_tendsto {r : ℕ → ℝ}
    (hr1 : ∀ n, 1 ≤ r n) (hr2 : ∀ n, r n ≤ 2) (hr : Tendsto r atTop (𝓝 1))
    {R : ℝ} (F : SupportedSpace R) :
    Tendsto (fun n => ‖(inwardMap (hr1 n) F : WeightedSpace) - (F : WeightedSpace)‖)
      atTop (𝓝 0) := by
  have he (n : ℕ) : (inwardMap (hr1 n) F : WeightedSpace) =
      frequencyDilate (hr1 n) (F : WeightedSpace) :=
    inwardLift_eq_frequencyDilate (hr1 n) F F.property
  simpa only [he] using frequencyDilate_norm_tendsto hr1 hr2 hr (F : WeightedSpace)

/-- Fixed explicit inward scales: each support radius is genuinely smaller. -/
def inwardScale (n : ℕ) : ℝ := 1 + 1 / ((n : ℝ) + 1)

lemma inwardScale_gt_one (n : ℕ) : 1 < inwardScale n := by
  unfold inwardScale
  have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

lemma inwardScale_ge_one (n : ℕ) : 1 ≤ inwardScale n := (inwardScale_gt_one n).le

lemma inwardScale_le_two (n : ℕ) : inwardScale n ≤ 2 := by
  have hi : (((n : ℝ) + 1)⁻¹ : ℝ) ≤ 1 := inv_le_one_of_one_le₀ (by have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  unfold inwardScale
  rw [one_div]
  linarith

lemma inwardScale_tendsto : Tendsto inwardScale atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun n : ℕ => 1 + (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1)
  simpa only [add_zero] using h.const_add (1 : ℝ)

def inwardRadius (R : ℝ) (n : ℕ) : ℝ := (inwardScale n)⁻¹ * R

lemma inwardRadius_pos_lt {R : ℝ} (hR : 0 < R) (n : ℕ) :
    0 < inwardRadius R n ∧ inwardRadius R n < R := by
  have hs := inwardScale_gt_one n
  have hs0 : 0 < inwardScale n := lt_trans (by norm_num) hs
  have hi : (inwardScale n)⁻¹ < 1 := (inv_lt_one₀ hs0).mpr hs
  constructor
  · exact mul_pos (inv_pos.mpr hs0) hR
  · change (inwardScale n)⁻¹ * R < R
    nlinarith

/-- An actual norm-convergent sequence on explicit strict interior supports. -/
theorem canonical_supported_inward_norm_tendsto {R : ℝ} (F : SupportedSpace R) :
    Tendsto (fun n => ‖(inwardMap (inwardScale_ge_one n) F : WeightedSpace) -
      (F : WeightedSpace)‖) atTop (𝓝 0) :=
  supported_inward_norm_tendsto inwardScale_ge_one inwardScale_le_two inwardScale_tendsto F

end RhSupportedInwardStrong
#print axioms RhSupportedInwardStrong.supported_inward_norm_tendsto
#print axioms RhSupportedInwardStrong.inwardRadius_pos_lt
#print axioms RhSupportedInwardStrong.canonical_supported_inward_norm_tendsto
