import RhShiftFormMultiplier001
import RhWeightedMeasureEmbedding001
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Topology.MetricSpace.Bounded

/-! Local finiteness of the ACTUAL complete native weighted Fourier measure.
The resulting smooth compact approximation is in FREQUENCY space. It does not
assert spatial support preservation or spatial smooth-core equality. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal
namespace RhWeightedFrequencyDensity
open RhWeightedMeasureEmbedding

/-- An exact compact-frequency density majorant, with the complete native
multiplier and its actual angular-frequency normalization. -/
def intervalWeightBound (B : ℝ) : ℝ≥0∞ :=
  1 + ENNReal.ofReal (RhDilationScalar.archMultiplier (1 / 2) (2 * Real.pi * B))

lemma archWeight_le_on_interval {B xi : ℝ} (hB : 0 ≤ B) (hxi : xi ∈ Icc (-B) B) :
    archWeight xi ≤ intervalWeightBound B := by
  have hab : |xi| ≤ B := abs_le.mpr hxi
  have hangular : |2 * Real.pi * xi| ≤ |2 * Real.pi * B| := by
    calc
      |2 * Real.pi * xi| = |2 * Real.pi| * |xi| := abs_mul _ _
      _ ≤ |2 * Real.pi| * B := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
      _ = |2 * Real.pi * B| := by
        simpa only [abs_of_nonneg hB] using (abs_mul (2 * Real.pi) B).symm
  have hm := RhShiftFormMultiplier.archMultiplier_mono_abs
    (b := 1 / 2) (by norm_num) hangular
  rw [archWeight_eq]
  exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal hm)

theorem weighted_interval_bound {B : ℝ} (hB : 0 ≤ B) :
    weightedMeasure (Icc (-B) B) ≤
      intervalWeightBound B * volume (Icc (-B) B) := by
  unfold weightedMeasure
  rw [withDensity_apply archWeight measurableSet_Icc]
  calc
    (∫⁻ xi in Icc (-B) B, archWeight xi) ≤
        ∫⁻ _ in Icc (-B) B, intervalWeightBound B :=
      setLIntegral_mono' measurableSet_Icc (fun xi hxi => archWeight_le_on_interval hB hxi)
    _ = _ := setLIntegral_const _ _

lemma weighted_interval_lt_top {B : ℝ} (hB : 0 ≤ B) :
    weightedMeasure (Icc (-B) B) < ⊤ := by
  apply (weighted_interval_bound hB).trans_lt
  apply ENNReal.mul_lt_top
  · unfold intervalWeightBound
    exact ENNReal.add_lt_top.mpr ⟨by norm_num, ENNReal.ofReal_lt_top⟩
  · exact isCompact_Icc.measure_lt_top

/-- This instance is proved from boundedness of the actual native multiplier
on compact frequency intervals, without postulating continuity of that sum. -/
instance weightedMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts weightedMeasure where
  lt_top_of_isCompact := by
    intro K hK
    obtain ⟨B, hB, hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℝ)
    have hI : K ⊆ Icc (-B) B := by
      intro xi hxi
      have hx : |xi| ≤ B := by
        simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hsub hxi
      exact abs_le.mp hx
    exact (measure_mono hI).trans_lt (weighted_interval_lt_top hB.le)

/-- Genuine compact C-infinity FREQUENCY representatives are dense in the
actual native weighted L2 space. This statement imposes no physical support. -/
theorem frequency_smooth_dense :
    Dense {F : WeightedSpace | ∃ g : ℝ → ℂ, F =ᵐ[weightedMeasure] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
  Lp.dense_hasCompactSupport_contDiff (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

/-- A quantitative frequency approximation, again without a spatial support
or physical-primitivity assertion. -/
theorem frequency_smooth_approximation (F : WeightedSpace) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ g : ℝ → ℂ, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      eLpNorm ((fun xi => F xi) - g) 2 weightedMeasure ≤ ENNReal.ofReal epsilon :=
  (Lp.memLp F).exist_eLpNorm_sub_le (by norm_num) (by norm_num) hepsilon

end RhWeightedFrequencyDensity
#print axioms RhWeightedFrequencyDensity.weighted_interval_bound
#print axioms RhWeightedFrequencyDensity.weightedMeasure_finiteOnCompacts
#print axioms RhWeightedFrequencyDensity.frequency_smooth_dense
#print axioms RhWeightedFrequencyDensity.frequency_smooth_approximation
