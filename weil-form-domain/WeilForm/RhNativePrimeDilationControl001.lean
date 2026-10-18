import RhPulledCompleteForm001
import RhNativeCompleteDictionary001
import RhComplexShiftDilation001
import RhSupportedArithmeticContinuity001

/-! Actual native finite-prime component under physical dilation. Exact
coefficients, both signed translations and the common finite horizon remain
in the form. The estimate is local continuity, never an arithmetic sign or
cancellation theorem.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhNativePrimeDilationControl
open RhWeightedMeasureEmbedding RhNativeCompleteBilinear RhFlatSmoothCore

/-- Whole exact finite arithmetic component of the native form. -/
def arithmeticValue (N : ℕ) (F : WeightedSpace) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, RhAllPrime.weight n * shiftPair (Real.log (n : ℝ)) F F

lemma shiftPair_spatial_diagonal (ell : ℝ) (F : WeightedSpace) :
    shiftPair ell F F = RhPhysicalShiftFourier.spatialPair
      (physicalEmbedding F) (physicalEmbedding F) ell := by
  rw [shiftPair_diagonal, RhNativeCompleteDictionary.twoShift_spatial_dictionary]

/-- Exact phase/delay dictionary for the ENTIRE actual finite aggregate. -/
theorem outward_arithmetic_value {R r : ℝ} (hr : 1 ≤ r) (N : ℕ) (F : FlatCoreSpace R) :
    arithmeticValue N (RhFlatCoreDilation.outwardMap hr F : WeightedSpace) =
      RhSupportedArithmeticContinuity.arithmeticPair N r (F : WeightedSpace) (F : WeightedSpace) := by
  unfold arithmeticValue RhSupportedArithmeticContinuity.arithmeticPair
  simp_rw [shiftPair_spatial_diagonal, RhComplexShiftDilation.outward_spatialPair hr F F]

lemma base_arithmetic_value (N : ℕ) (F : WeightedSpace) :
    arithmeticValue N F = RhSupportedArithmeticContinuity.arithmeticPair N 1 F F := by
  unfold arithmeticValue RhSupportedArithmeticContinuity.arithmeticPair
  simp only [div_one, shiftPair_spatial_diagonal]

/-- Actual finite arithmetic perturbation is uniformly small in the graph
norm. A growing arithmetic horizon is NOT allowed inside this quantifier. -/
theorem uniform_native_prime_graph_budget (N : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (R r : ℝ) (hr : 1 ≤ r), |r - 1| < delta →
      ∀ F : FlatCoreSpace R,
      |arithmeticValue N (RhFlatCoreDilation.outwardMap hr F : WeightedSpace) -
        arithmeticValue N (F : WeightedSpace)| ≤ eta * ‖F‖^2 := by
  obtain ⟨delta, hdelta, hd⟩ :=
    RhSupportedArithmeticContinuity.uniform_finite_arithmetic_continuity N heta
  refine ⟨delta, hdelta, ?_⟩
  intro R r hr hclose F
  rw [outward_arithmetic_value hr N F, base_arithmetic_value]
  have h := hd R r hclose (F : WeightedSpace) (F : WeightedSpace)
    (flatCore_supported R F.property) (flatCore_supported R F.property)
  simpa only [Submodule.norm_coe, pow_two, mul_assoc] using h

end RhNativePrimeDilationControl
#print axioms RhNativePrimeDilationControl.outward_arithmetic_value
#print axioms RhNativePrimeDilationControl.uniform_native_prime_graph_budget
