import RhRealMollifier001
import RhFlatSmoothCore001

/-! Closed real physical subspace of the ACTUAL weighted Hilbert domain.
Reality is the kernel of the continuous spatial-L2 imaginary-part map;
it is not imposed pointwise on arbitrary representatives. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhRealSupportedDomain
open RhWeightedMeasureEmbedding RhRealMollifier RhFlatSmoothCore

abbrev RealWholeSpace := Lp (α := ℝ) ℝ 2 volume

def imaginaryMap : WeightedSpace →L[ℝ] RealWholeSpace :=
  (Complex.imCLM.compLpL 2 volume).comp physicalEmbedding

lemma imaginaryMap_ae (F : WeightedSpace) :
    imaginaryMap F =ᵐ[volume] fun t => (physicalEmbedding F t).im :=
  Complex.imCLM.coeFn_compLpL (physicalEmbedding F)

def realPhysicalSubspace : Submodule ℝ WeightedSpace := imaginaryMap.ker

lemma realPhysical_isClosed : IsClosed (realPhysicalSubspace : Set WeightedSpace) :=
  imaginaryMap.isClosed_ker

lemma mem_realPhysical_iff (F : WeightedSpace) :
    F ∈ realPhysicalSubspace ↔ IsPhysicalReal F := by
  change imaginaryMap F = 0 ↔ _
  constructor
  · intro h
    have hz := (Lp.eq_zero_iff_ae_eq_zero).mp h
    filter_upwards [imaginaryMap_ae F, hz] with t ht hz
    rw [← ht, hz]
    rfl
  · intro h
    apply (Lp.eq_zero_iff_ae_eq_zero).mpr
    filter_upwards [imaginaryMap_ae F, h] with t ht hz
    rw [ht, hz]
    rfl

/-- Exact supported real finite-energy domain; weighted membership already
contains finiteness of the full native graph energy. -/
def realSupportedSubspace (R : ℝ) : Submodule ℝ WeightedSpace :=
  supportedSubspace R ⊓ realPhysicalSubspace

lemma mem_realSupported_iff (R : ℝ) (F : WeightedSpace) :
    F ∈ realSupportedSubspace R ↔ F ∈ supportedSubspace R ∧ IsPhysicalReal F := by
  change (F ∈ supportedSubspace R ∧ F ∈ realPhysicalSubspace) ↔ _
  rw [mem_realPhysical_iff]

lemma realSupported_isClosed (R : ℝ) :
    IsClosed (realSupportedSubspace R : Set WeightedSpace) :=
  (supportedSubspace_isClosed R).inter realPhysical_isClosed

lemma smooth_generator_real {R : ℝ} {F : WeightedSpace}
    (hF : F ∈ smoothWeightedSet R) : IsPhysicalReal F := by
  obtain ⟨f, _hfS, _hfC, _hfT, hfA⟩ := hF
  filter_upwards [hfA] with t ht
  rw [ht]
  exact Complex.ofReal_im _

/-- The old real flat core is contained in the actual supported-real domain. -/
theorem flatCore_le_realSupported (R : ℝ) : flatCore R ≤ realSupportedSubspace R := by
  apply (Submodule.span ℝ (smoothWeightedSet R)).topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    intro F hF
    exact (mem_realSupported_iff R F).mpr ⟨smooth_generator_supported hF, smooth_generator_real hF⟩
  · exact realSupported_isClosed R

end RhRealSupportedDomain
#print axioms RhRealSupportedDomain.imaginaryMap_ae
#print axioms RhRealSupportedDomain.mem_realPhysical_iff
#print axioms RhRealSupportedDomain.realSupported_isClosed
#print axioms RhRealSupportedDomain.flatCore_le_realSupported
