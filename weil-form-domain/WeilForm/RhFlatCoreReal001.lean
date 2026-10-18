import RhFlatSmoothCore001

/-! The flattened core is genuinely REAL in physical L2. This follows from
its actual real smooth generators and a closed imaginary-part kernel; it is
not a pointwise assertion about arbitrary representatives or a density claim
for all supported complex functions.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhFlatCoreReal
open RhAnchored RhWeightedMeasureEmbedding RhWeightedPrimitiveLift RhFlatSmoothCore

def imaginaryMap : WeightedSpace →L[ℝ] Lp (α := ℝ) ℝ 2 volume :=
  (Complex.imCLM.compLpL 2 volume).comp physicalEmbedding

lemma imaginaryMap_ae (F : WeightedSpace) :
    imaginaryMap F =ᵐ[volume] fun t => (physicalEmbedding F t).im :=
  Complex.imCLM.coeFn_compLpL (physicalEmbedding F)

lemma smooth_generator_imaginary_zero {R : ℝ} {F : WeightedSpace}
    (hF : F ∈ smoothWeightedSet R) : imaginaryMap F = 0 := by
  obtain ⟨f, _hfS, _hfC, _hfT, hfA⟩ := hF
  apply (Lp.eq_zero_iff_ae_eq_zero).mpr
  filter_upwards [imaginaryMap_ae F, hfA] with t hi hf
  rw [hi, hf]
  simp

theorem flatCore_imaginary_zero (R : ℝ) : flatCore R ≤ imaginaryMap.ker :=
  (Submodule.span ℝ (smoothWeightedSet R)).topologicalClosure_minimal
    (Submodule.span_le.mpr (fun _ h => smooth_generator_imaginary_zero h))
    imaginaryMap.isClosed_ker

/-- Real-valuedness holds AE for the actual spatial L2 representative. -/
theorem physical_im_zero {R : ℝ} (F : FlatCoreSpace R) :
    ∀ᵐ t ∂volume, (physicalEmbedding (F : WeightedSpace) t).im = 0 := by
  have hz : imaginaryMap (F : WeightedSpace) = 0 := flatCore_imaginary_zero R F.property
  have hzero := (Lp.eq_zero_iff_ae_eq_zero).mp hz
  filter_upwards [imaginaryMap_ae (F : WeightedSpace), hzero] with t hi ht
  rw [← hi]
  exact ht

def realPhysical {R : ℝ} (F : FlatCoreSpace R) (t : ℝ) : ℝ :=
  (physicalEmbedding (F : WeightedSpace) t).re

lemma realPhysical_memLp {R : ℝ} (F : FlatCoreSpace R) :
    MemLp (realPhysical F) 2 (physicalMeasure R) :=
  ((Lp.memLp (physicalEmbedding (F : WeightedSpace))).re).mono_measure Measure.restrict_le_self

/-- Exact quotient reconstruction with exterior support and imaginary part
handled AE. Assigned values at the endpoints or zero have no role. -/
theorem physicalVector_realPhysical {R : ℝ} (F : FlatCoreSpace R) :
    RhTail.physicalFourierVector R (realPhysical F) (realPhysical_memLp F) =
      physicalEmbedding (F : WeightedSpace) := by
  apply Lp.ext
  have he : RhTail.physicalFourierVector R (realPhysical F) (realPhysical_memLp F) =ᵐ[volume]
      RhTail.complexExtension R (realPhysical F) :=
    (RhTail.complexExtension_memLp (realPhysical_memLp F)).coeFn_toLp
  have hs := (mem_supportedSubspace_iff R (F : WeightedSpace)).mp (flatCore_supported R F.property)
  filter_upwards [he, physical_im_zero F, hs] with t ht hi hout
  rw [ht]
  by_cases h : t ∈ interval R
  · simp only [RhTail.complexExtension, zeroExtension_eq h]
    apply Complex.ext <;> simp [realPhysical, hi]
  · simp [RhTail.complexExtension, zeroExtension, h, hout h]

lemma realPhysical_mass {R : ℝ} (F : FlatCoreSpace R) :
    (∫ t in interval R, (realPhysical F t)^2) = ‖physicalEmbedding (F : WeightedSpace)‖^2 := by
  rw [← physicalVector_norm_square (realPhysical_memLp F), physicalVector_realPhysical]

end RhFlatCoreReal
#print axioms RhFlatCoreReal.flatCore_imaginary_zero
#print axioms RhFlatCoreReal.physical_im_zero
#print axioms RhFlatCoreReal.physicalVector_realPhysical
#print axioms RhFlatCoreReal.realPhysical_mass
