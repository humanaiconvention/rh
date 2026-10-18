import RhWeightedEnergyIdentity001
import RhPrimitiveFormDomain001

/-!
Actual physical anchored primitives belong to the concrete supported weighted
Hilbert space. The lift and exact norm are constructed from their already
proved all-radius native finite energy. Assigned point values are used only
through almost-everywhere quotient identities.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhWeightedPrimitiveLift
open RhAnchored RhWeightedMeasureEmbedding RhWeightedEnergyIdentity

lemma physicalVector_support {R : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure R)) :
    ∀ᵐ t ∂volume, t ∉ Icc (-R) R → RhTail.physicalFourierVector R w hw t = 0 := by
  have he : RhTail.physicalFourierVector R w hw =ᵐ[volume] RhTail.complexExtension R w :=
    (RhTail.complexExtension_memLp hw).coeFn_toLp
  filter_upwards [he] with t ht
  intro hnot
  rw [ht]
  simp [RhTail.complexExtension, zeroExtension, interval, hnot]

lemma physicalVector_norm_square {R : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure R)) :
    ‖RhTail.physicalFourierVector R w hw‖ ^ 2 = ∫ t in interval R, (w t) ^ 2 := by
  calc
    _ = ∫ t, ‖RhTail.physicalFourierVector R w hw t‖ ^ 2 :=
      lp_norm_sq_integral (RhTail.physicalFourierVector R w hw)
    _ = ∫ t, ‖RhTail.complexExtension R w t‖ ^ 2 := by
      apply integral_congr_ae
      have he : RhTail.physicalFourierVector R w hw =ᵐ[volume] RhTail.complexExtension R w :=
        (RhTail.complexExtension_memLp hw).coeFn_toLp
      filter_upwards [he] with t ht
      rw [ht]
    _ = _ := RhTail.complexExtension_norm_integral R w

/-- Expose the already-proved finiteness in the exact native predicate. -/
theorem actualPrimitiveEnergy_finite {R : ℝ} (hR : 0 < R) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) :
    RhTail.fullFrequencyEnergy (1 / 2)
      (RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv)) < ⊤ := by
  simpa only [RhPrimitiveFormDomain.FullArchFiniteEnergy] using
    RhPrimitiveFormDomain.physical_primitive_full_arch_finite hR hv

/-- This is an actual weighted L2 vector for every finite positive radius. -/
def actualPrimitiveLift {R : ℝ} (hR : 0 < R) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) : WeightedSpace :=
  frequencyLift (RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv))
    (actualPrimitiveEnergy_finite hR v hv)

/-- The lift reconstructs the actual zero-extended primitive class. -/
theorem actualPrimitiveLift_physical {R : ℝ} (hR : 0 < R) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) :
    physicalEmbedding (actualPrimitiveLift hR v hv) =
      RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv) :=
  physicalEmbedding_frequencyLift _ _

/-- Support is proved in physical space, not assigned pointwise to a Fourier class. -/
theorem actualPrimitiveLift_supported {R : ℝ} (hR : 0 < R) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) :
    actualPrimitiveLift hR v hv ∈ supportedSubspace R :=
  frequencyLift_mem_supportedSubspace R _ _ (physicalVector_support (primitive_memLp hv))

/-- A concrete element of the complete real form-space Hilbert domain. -/
def actualPrimitiveSupportedLift {R : ℝ} (hR : 0 < R) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) : SupportedSpace R :=
  ⟨actualPrimitiveLift hR v hv, actualPrimitiveLift_supported hR v hv⟩

/-- Exact native graph norm, retaining the COMPLETE archimedean multiplier. -/
theorem actualPrimitiveLift_norm_square {R : ℝ} (hR : 0 < R) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) :
    ‖actualPrimitiveLift hR v hv‖ ^ 2 =
      (∫ t in interval R, (primitive R v t) ^ 2) +
      (RhTail.fullFrequencyEnergy (1 / 2)
        (RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv))).toReal := by
  unfold actualPrimitiveLift
  rw [frequencyLift_norm_square, physicalVector_norm_square]

/-- The supported-space norm is the same exact physical mass-plus-energy value. -/
theorem actualPrimitiveSupportedLift_norm_square {R : ℝ} (hR : 0 < R) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) :
    ‖actualPrimitiveSupportedLift hR v hv‖ ^ 2 =
      (∫ t in interval R, (primitive R v t) ^ 2) +
      (RhTail.fullFrequencyEnergy (1 / 2)
        (RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv))).toReal :=
  actualPrimitiveLift_norm_square hR v hv

end RhWeightedPrimitiveLift
#print axioms RhWeightedPrimitiveLift.physicalVector_support
#print axioms RhWeightedPrimitiveLift.physicalVector_norm_square
#print axioms RhWeightedPrimitiveLift.actualPrimitiveLift_physical
#print axioms RhWeightedPrimitiveLift.actualPrimitiveLift_supported
#print axioms RhWeightedPrimitiveLift.actualPrimitiveLift_norm_square
#print axioms RhWeightedPrimitiveLift.actualPrimitiveSupportedLift_norm_square
