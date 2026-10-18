import RhNativeTranslationAdjoint001
import RhTranslationSupport001
import RhRealSameWindowSmooth001
import RhLiteralSupportForm001
import RhPulledCompleteForm001

/-! Actual real complete-core translations and local FULL radical membership.
The whole larger-window row annihilation is explicit. No finite-dimensional
orbit, unique-continuation, positivity, or nonzero-row claim is asserted.
-/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhTranslatedCoreRadical
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhWeightedTranslation RhNativeTranslationAdjoint RhPulledCompleteForm
open RhRealMollifier RhRealSupportedDomain RhRealSameWindowSmooth

lemma supported_mono {R S : ℝ} (hRS : R ≤ S) {F : WeightedSpace}
    (hF : F ∈ supportedSubspace R) : F ∈ supportedSubspace S := by
  rw [mem_supportedSubspace_iff] at hF ⊢
  filter_upwards [hF] with t ht
  intro hout
  exact ht (fun hin => hout (RhLiteralSupportForm.interval_subset hRS hin))

lemma translated_real (F : WeightedSpace)
    (hI : Integrable (physicalEmbedding F) volume) (hF : IsPhysicalReal F) (a : ℝ) :
    IsPhysicalReal (translated F hI a) := by
  have hi := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hF
  filter_upwards [translated_physical_ae F hI a, hi] with t ht hreal
  rw [ht]
  exact hreal

lemma translated_mem_flatCore {R T : ℝ} (hT : 0 < T) (p : FlatCoreSpace R)
    (a : ℝ) (ha : R+|a| ≤ T) :
    translated (p : WeightedSpace)
      (RhPhysicalShiftFourier.supported_integrable (flatCore_supported R p.property)) a
      ∈ flatCore T := by
  apply realSupported_mem_flatCore hT
  apply (mem_realSupported_iff T _).mpr
  have hp : (p : WeightedSpace) ∈ supportedSubspace R := flatCore_supported R p.property
  have hi := RhPhysicalShiftFourier.supported_integrable hp
  refine ⟨supported_mono ha (RhTranslationSupport.weighted_translated_supported
    (p : WeightedSpace) hi hp a), ?_⟩
  exact translated_real (p : WeightedSpace) hi
    ((mem_realSupported_iff R _).mp (flatCore_le_realSupported R p.property)).2 a

/-- Actual complete-domain vector; integrable physical representative follows
from its ALREADY GIVEN bounded support, not a regularity assumption. -/
def translatedCore {R T : ℝ} (hT : 0 < T) (p : FlatCoreSpace R)
    (a : ℝ) (ha : R+|a| ≤ T) : FlatCoreSpace T :=
  ⟨translated (p : WeightedSpace)
    (RhPhysicalShiftFourier.supported_integrable (flatCore_supported R p.property)) a,
    translated_mem_flatCore hT p a ha⟩

lemma translatedCore_ambient {R T : ℝ} (hT : 0 < T) (p : FlatCoreSpace R)
    (a : ℝ) (ha : R+|a| ≤ T) :
    (translatedCore hT p a ha : WeightedSpace) = translated (p : WeightedSpace)
      (RhPhysicalShiftFourier.supported_integrable (flatCore_supported R p.property)) a := rfl

lemma translatedCore_physical {R T : ℝ} (hT : 0 < T) (p : FlatCoreSpace R)
    (a : ℝ) (ha : R+|a| ≤ T) :
    physicalEmbedding (translatedCore hT p a ha : WeightedSpace) =
      translation a (physicalEmbedding (p : WeightedSpace)) :=
  translated_physical (p : WeightedSpace)
    (RhPhysicalShiftFourier.supported_integrable (flatCore_supported R p.property)) a

/-- Every sufficiently small TRUE translation is in the intermediate full
radical. The fixed finite horizon N is identical in both windows. -/
theorem local_radical_translation {R T S : ℝ} (hR : 0 < R)
    (hRT : R < T) (hTS : T < S) (C : ℝ) (N : ℕ) (p : FlatCoreSpace R)
    (hnull : ∀ g : FlatCoreSpace S,
      completeForm S C N (p : WeightedSpace) (g : WeightedSpace) = 0)
    (a : ℝ) (ha : |a| < min (T-R) (S-T)) :
    ∃ hpT : R+|a| ≤ T,
      translatedCore (lt_trans hR hRT) p a hpT ∈ (baseForm T C N).ker ∧
      physicalEmbedding (translatedCore (lt_trans hR hRT) p a hpT : WeightedSpace) =
        translation a (physicalEmbedding (p : WeightedSpace)) := by
  have haRT : |a| < T-R := ha.trans_le (min_le_left _ _)
  have haTS : |a| < S-T := ha.trans_le (min_le_right _ _)
  have hpT : R+|a| ≤ T := by linarith
  refine ⟨hpT, ?_, translatedCore_physical _ p a hpT⟩
  change baseForm T C N (translatedCore (lt_trans hR hRT) p a hpT) = 0
  apply ContinuousLinearMap.ext
  intro q
  have hS : 0 < S := lt_trans (lt_trans hR hRT) hTS
  have hqS : T+|-a| ≤ S := by rw [abs_neg]; linarith
  let g : FlatCoreSpace S := translatedCore hS q (-a) hqS
  have hpR := flatCore_supported R p.property
  have hqT := flatCore_supported T q.property
  have hpS := supported_mono (le_trans hRT.le hTS.le) hpR
  have hIp := RhPhysicalShiftFourier.supported_integrable hpR
  have hIq := RhPhysicalShiftFourier.supported_integrable hqT
  have htP := flatCore_supported T (translatedCore (lt_trans hR hRT) p a hpT).property
  have htQ := flatCore_supported S g.property
  have he := completeForm_adjoint C N (p : WeightedSpace) (q : WeightedSpace)
    hpS hqT hIp hIq a htP htQ
  change completeForm T C N
    (translated (p : WeightedSpace) hIp a) (q : WeightedSpace) = 0
  rw [he]
  exact hnull g

end RhTranslatedCoreRadical
#print axioms RhTranslatedCoreRadical.translated_real
#print axioms RhTranslatedCoreRadical.translated_mem_flatCore
#print axioms RhTranslatedCoreRadical.translatedCore_physical
#print axioms RhTranslatedCoreRadical.local_radical_translation
