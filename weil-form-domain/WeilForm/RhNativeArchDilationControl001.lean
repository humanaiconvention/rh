import RhFlatCoreDilation001
import RhNativeCompleteBilinear001

/-! Actual complete archimedean form comparison under outward dilation.
The bound is derived from both accepted native energy comparisons and their
constructed inverse, including the exact constant 5. No finite-energy or
positivity premise is imposed on weighted vectors.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhNativeArchDilationControl
open RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhWeightedDilation
open RhWeightedDilationInverse RhNativeCompleteBilinear RhFlatSmoothCore

/-- Complete native archimedean energy decreases, but by at most the ACTUAL
five-logarithm physical mass budget. The absolute value is of the complete
archimedean difference, not a sum of separately estimated spectral modes. -/
theorem native_arch_dilation_budget {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    let U := outwardLift hr F hF
    0 ≤ archPair F F - archPair U U ∧
    |archPair U U - archPair F F| ≤ (5 * Real.log r) * ‖physicalEmbedding F‖ ^ 2 := by
  let U := outwardLift hr F hF
  have hU : U ∈ supportedSubspace (r * R) := outwardLift_supported hr F hF
  have hphys : physicalEmbedding U = dilatedPhysical (by linarith : 0 < r) F hF :=
    outwardLift_physical hr F hF
  have hmass : ‖physicalEmbedding U‖ ^ 2 = ‖physicalEmbedding F‖ ^ 2 := by
    rw [hphys]
    exact dilatedPhysical_norm_square (by linarith : 0 < r) F hF
  have hcontraction : archPair U U ≤ archPair F F := by
    rw [archPair_diagonal, archPair_diagonal, hphys]
    exact ENNReal.toReal_mono (weighted_native_energy_finite F).ne
      (dilatedPhysical_energy_le hr F hF)
  have hcancel : inwardLift hr U hU = F := inward_outward_cancel hr F hF
  have hback : dilatedPhysical (inv_pos.mpr (by linarith : 0 < r)) U hU =
      physicalEmbedding F := by
    rw [← inwardLift_physical hr U hU, hcancel]
  have hInv := dilatedPhysical_inverse_energy_bound hr U hU
  rw [hback] at hInv
  have hb : 0 ≤ (5 * Real.log r) * ‖physicalEmbedding U‖ ^ 2 := by positivity [Real.log_nonneg hr]
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨(weighted_native_energy_finite U).ne, ENNReal.ofReal_ne_top⟩) hInv
  rw [ENNReal.toReal_add (weighted_native_energy_finite U).ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hb, hmass] at hreal
  rw [← archPair_diagonal, ← archPair_diagonal] at hreal
  dsimp only
  refine ⟨sub_nonneg.mpr hcontraction, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hcontraction)]
  linarith

/-- Uniform graph-form budget on the actual closed smooth core. -/
theorem flat_arch_graph_budget {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace R) :
    |archPair (RhFlatCoreDilation.outwardMap hr F : WeightedSpace)
      (RhFlatCoreDilation.outwardMap hr F : WeightedSpace) -
      archPair (F : WeightedSpace) (F : WeightedSpace)| ≤
      (5 * Real.log r) * ‖F‖ ^ 2 := by
  have h := (native_arch_dilation_budget hr (F : WeightedSpace)
    (flatCore_supported R F.property)).2
  have hm : ‖physicalEmbedding (F : WeightedSpace)‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    have hn := physicalEmbedding_norm_apply_le (F : WeightedSpace)
    change ‖physicalEmbedding (F : WeightedSpace)‖ ≤ ‖F‖ at hn
    nlinarith [norm_nonneg (physicalEmbedding (F : WeightedSpace)), norm_nonneg F]
  exact h.trans (mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) (Real.log_nonneg hr)))

end RhNativeArchDilationControl
#print axioms RhNativeArchDilationControl.native_arch_dilation_budget
#print axioms RhNativeArchDilationControl.flat_arch_graph_budget
