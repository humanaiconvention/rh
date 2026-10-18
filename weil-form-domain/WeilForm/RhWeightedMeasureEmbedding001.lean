import RhDilationScalar001
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Fourier.LpSpace

/-!
A concrete weighted Fourier L2 space and a continuous injective map into actual
spatial L2. Supported vectors form the closed kernel of exterior restriction.
The graph-energy identity and arithmetic form boundedness on this Hilbert
space are separate obligations; neither is postulated in this module.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhWeightedMeasureEmbedding

/-- A single nonnegative scalar summand of the actual archimedean multiplier. -/
def archSummand (k : ℕ) (xi : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (RhTail.multiplier (((2 * Real.pi * xi) ^ 2)) ((1 / 2 : ℝ) + 2 * k))

/-- Exact positive graph density: one plus the full native multiplier. -/
def archWeight (xi : ℝ) : ℝ≥0∞ := 1 + ∑' k : ℕ, archSummand k xi

lemma archSummand_measurable (k : ℕ) : Measurable (archSummand k) := by
  have hk : 0 < (1 / 2 : ℝ) + 2 * k := by positivity
  have hm : Continuous (fun xi : ℝ =>
      RhTail.multiplier (((2 * Real.pi * xi) ^ 2)) ((1 / 2 : ℝ) + 2 * k)) := by
    unfold RhTail.multiplier
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro xi
      exact mul_ne_zero (ne_of_gt hk) (ne_of_gt (by positivity))
  exact hm.measurable.ennreal_ofReal

lemma archWeight_measurable : Measurable archWeight := by
  exact measurable_const.add (Measurable.tsum archSummand_measurable)

lemma archWeight_ge_one (xi : ℝ) : 1 ≤ archWeight xi := by
  unfold archWeight
  exact le_add_of_nonneg_right (by positivity)

/-- The ENNReal density has the actual convergent scalar multiplier value. -/
theorem archWeight_eq (xi : ℝ) :
    archWeight xi = 1 + ENNReal.ofReal
      (RhDilationScalar.archMultiplier (1 / 2) (2 * Real.pi * xi)) := by
  have hn : ∀ k : ℕ,
      0 ≤ RhTail.multiplier (((2 * Real.pi * xi) ^ 2)) ((1 / 2 : ℝ) + 2 * k) :=
    fun k => RhTail.multiplier_nonneg (sq_nonneg _) (by positivity)
  have hs := RhDilationScalar.multiplier_series_summable_pos
    (sq_nonneg (2 * Real.pi * xi)) (by norm_num : (0 : ℝ) < 1 / 2)
  have he := ENNReal.ofReal_tsum_of_nonneg hn hs
  unfold archWeight archSummand RhDilationScalar.archMultiplier
  exact congrArg (fun z : ℝ≥0∞ => 1 + z) he.symm

lemma archWeight_ne_top (xi : ℝ) : archWeight xi ≠ ⊤ := by
  rw [archWeight_eq]
  exact ENNReal.add_ne_top.mpr ⟨by norm_num, ENNReal.ofReal_ne_top⟩

/-- Actual weighted Lebesgue measure, not an abstract target hypothesis. -/
def weightedMeasure : Measure ℝ := volume.withDensity archWeight

/-- This domination is the foundation of the norm-one inclusion. -/
theorem volume_le_weightedMeasure : (volume : Measure ℝ) ≤ weightedMeasure := by
  have h := withDensity_mono (μ := (volume : Measure ℝ))
    (f := fun _ : ℝ => (1 : ℝ≥0∞)) (g := archWeight)
    (Eventually.of_forall archWeight_ge_one)
  change (volume : Measure ℝ).withDensity (1 : ℝ → ℝ≥0∞) ≤
    (volume : Measure ℝ).withDensity archWeight at h
  simpa only [withDensity_one, weightedMeasure] using h

abbrev WeightedSpace := Lp (α := ℝ) ℂ 2 weightedMeasure
abbrev WholeSpace := Lp (α := ℝ) ℂ 2 volume

/-- The existing measure-change API gives an actual continuous real linear map. -/
def measureContraction {mu nu : Measure ℝ} (h : mu ≤ nu) :
    Lp (α := ℝ) ℂ 2 nu →L[ℝ] Lp (α := ℝ) ℂ 2 mu :=
  Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by norm_num)
    (by simpa only [one_smul] using h)

lemma measureContraction_ae {mu nu : Measure ℝ} (h : mu ≤ nu)
    (F : Lp (α := ℝ) ℂ 2 nu) : measureContraction h F =ᵐ[mu] F := by
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞))
    (by norm_num) (by simpa only [one_smul] using h) F

lemma measureContraction_norm_le {mu nu : Measure ℝ} (h : mu ≤ nu) :
    ‖measureContraction h‖ ≤ 1 := by
  have ht := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := (2 : ℝ≥0∞))
    (c := (1 : ℝ≥0∞)) (by norm_num) (by simpa only [one_smul] using h)
  simpa only [measureContraction, ENNReal.toReal_one, Real.one_rpow] using ht

lemma measureContraction_norm_apply_le {mu nu : Measure ℝ} (h : mu ≤ nu)
    (F : Lp (α := ℝ) ℂ 2 nu) : ‖measureContraction h F‖ ≤ ‖F‖ := by
  calc
    _ ≤ ‖measureContraction h‖ * ‖F‖ := (measureContraction h).le_opNorm F
    _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right (measureContraction_norm_le h) (norm_nonneg F)
    _ = ‖F‖ := one_mul _

/-- Frequency-space inclusion with the exact actual density. -/
def inclusion : WeightedSpace →L[ℝ] WholeSpace :=
  measureContraction volume_le_weightedMeasure

lemma inclusion_ae (F : WeightedSpace) : inclusion F =ᵐ[volume] F :=
  measureContraction_ae volume_le_weightedMeasure F

/-- Explicit compatibility with MemLp.mono_measure and its toLp representative. -/
theorem inclusion_eq_toLp (F : WeightedSpace) :
    inclusion F = (MemLp.mono_measure volume_le_weightedMeasure (Lp.memLp F)).toLp F := by
  apply Lp.ext
  exact (inclusion_ae F).trans
    (MemLp.coeFn_toLp (MemLp.mono_measure volume_le_weightedMeasure (Lp.memLp F))).symm

lemma inclusion_norm_apply_le (F : WeightedSpace) : ‖inclusion F‖ ≤ ‖F‖ :=
  measureContraction_norm_apply_le volume_le_weightedMeasure F

/-- Density measure and Lebesgue measure have compatible null sets, so no vector is lost. -/
theorem inclusion_injective : Function.Injective inclusion := by
  intro F G hFG
  apply Lp.ext
  apply (withDensity_absolutelyContinuous (volume : Measure ℝ) archWeight).ae_eq
  have he : (inclusion F : ℝ → ℂ) =ᵐ[volume] inclusion G := by rw [hFG]
  exact (inclusion_ae F).symm.trans (he.trans (inclusion_ae G))

/-- Inverse Fourier transform as an actual real continuous linear map. -/
def inverseFourier : WholeSpace →L[ℝ] WholeSpace :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ

/-- A frequency graph-domain vector has a well-defined actual spatial L2 image. -/
def physicalEmbedding : WeightedSpace →L[ℝ] WholeSpace := inverseFourier.comp inclusion

lemma physicalEmbedding_norm_apply_le (F : WeightedSpace) : ‖physicalEmbedding F‖ ≤ ‖F‖ := by
  change ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm (inclusion F)‖ ≤ ‖F‖
  rw [(Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map]
  exact inclusion_norm_apply_le F

theorem physicalEmbedding_injective : Function.Injective physicalEmbedding := by
  intro F G hFG
  apply inclusion_injective
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm.injective hFG

/-- Exterior restriction avoids assigning values to individual boundary points. -/
def outsideRestriction (R : ℝ) : WholeSpace →L[ℝ]
    Lp (α := ℝ) ℂ 2 (volume.restrict (Icc (-R) R)ᶜ) :=
  measureContraction Measure.restrict_le_self

def outsideMap (R : ℝ) : WeightedSpace →L[ℝ]
    Lp (α := ℝ) ℂ 2 (volume.restrict (Icc (-R) R)ᶜ) :=
  (outsideRestriction R).comp physicalEmbedding

/-- The actual supported graph domain is a concrete closed linear subspace. -/
def supportedSubspace (R : ℝ) : Submodule ℝ WeightedSpace := (outsideMap R).ker

abbrev SupportedSpace (R : ℝ) := ↥(supportedSubspace R)

lemma supportedSubspace_isClosed (R : ℝ) : IsClosed (supportedSubspace R : Set WeightedSpace) :=
  (outsideMap R).isClosed_ker

instance supportedSpace_complete (R : ℝ) : CompleteSpace (SupportedSpace R) :=
  (supportedSubspace_isClosed R).completeSpace_coe

/-- Membership means precisely exterior vanishing almost everywhere in physical space. -/
theorem mem_supportedSubspace_iff (R : ℝ) (F : WeightedSpace) :
    F ∈ supportedSubspace R ↔
      ∀ᵐ t ∂volume, t ∉ Icc (-R) R → physicalEmbedding F t = 0 := by
  change outsideMap R F = 0 ↔ _
  have he : outsideMap R F =ᵐ[volume.restrict (Icc (-R) R)ᶜ] physicalEmbedding F :=
    measureContraction_ae Measure.restrict_le_self (physicalEmbedding F)
  constructor
  · intro hz
    have hzero := (Lp.eq_zero_iff_ae_eq_zero).mp hz
    have hp : physicalEmbedding F =ᵐ[volume.restrict (Icc (-R) R)ᶜ] 0 := he.symm.trans hzero
    simpa only [mem_compl_iff, Pi.zero_apply] using (ae_restrict_iff' measurableSet_Icc.compl).mp hp
  · intro hp
    apply (Lp.eq_zero_iff_ae_eq_zero).mpr
    have hzero : physicalEmbedding F =ᵐ[volume.restrict (Icc (-R) R)ᶜ] 0 :=
      (ae_restrict_iff' measurableSet_Icc.compl).mpr hp
    exact he.trans hzero

/-- This concrete complete space carries the real Hilbert structure needed by Lax-Milgram. -/
@[instance_reducible]
def supportedRealHilbert (R : ℝ) : InnerProductSpace ℝ (SupportedSpace R) := inferInstance

end RhWeightedMeasureEmbedding
#print axioms RhWeightedMeasureEmbedding.archWeight_eq
#print axioms RhWeightedMeasureEmbedding.volume_le_weightedMeasure
#print axioms RhWeightedMeasureEmbedding.inclusion_eq_toLp
#print axioms RhWeightedMeasureEmbedding.inclusion_norm_apply_le
#print axioms RhWeightedMeasureEmbedding.inclusion_injective
#print axioms RhWeightedMeasureEmbedding.physicalEmbedding_norm_apply_le
#print axioms RhWeightedMeasureEmbedding.physicalEmbedding_injective
#print axioms RhWeightedMeasureEmbedding.supportedSubspace_isClosed
#print axioms RhWeightedMeasureEmbedding.mem_supportedSubspace_iff
#print axioms RhWeightedMeasureEmbedding.supportedSpace_complete
