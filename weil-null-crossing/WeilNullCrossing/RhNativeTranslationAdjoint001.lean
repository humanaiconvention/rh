import RhNativeTranslationForm001

/-! Exact opposite-translation covariance across support windows.
No continuation, positivity, or unique-continuation premise is assumed.
All terms use the SAME prescribed finite arithmetic horizon N.
-/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhNativeTranslationAdjoint
open RhWeightedMeasureEmbedding RhNativeCompleteBilinear RhWeightedTranslation
open RhNativeTranslationAlgebra RhNativeTranslationForm

lemma translated_inverse (F : WeightedSpace)
    (hF : Integrable (physicalEmbedding F) volume) (a : ℝ)
    (hT : Integrable (physicalEmbedding (translated F hF a)) volume) :
    translated (translated F hF a) hT (-a) = F := by
  apply physicalEmbedding_injective
  rw [translated_physical, translated_physical, translation_comp, neg_add_cancel,
    translation_zero]

/-- Exact complete two-window covariance in the convention tau_a F(t)=F(t+a).
The translated supports are actual subspace memberships, not pointwise
representative assignments. Both ranks and every finite prime shift persist. -/
theorem completeForm_adjoint {R S : ℝ} (C : ℝ) (N : ℕ) (F G : WeightedSpace)
    (hFR : F ∈ supportedSubspace R) (hGS : G ∈ supportedSubspace S)
    (hF : Integrable (physicalEmbedding F) volume)
    (hG : Integrable (physicalEmbedding G) volume) (a : ℝ)
    (hTF : translated F hF a ∈ supportedSubspace S)
    (hBG : translated G hG (-a) ∈ supportedSubspace R) :
    completeForm S C N (translated F hF a) G =
      completeForm R C N F (translated G hG (-a)) := by
  let H := translated G hG (-a)
  have hH : Integrable (physicalEmbedding H) volume :=
    RhPhysicalShiftFourier.supported_integrable hBG
  have hc : translated H hH a = G := by
    simpa only [neg_neg] using translated_inverse G hG (-a) hH
  have hTH : translated H hH a ∈ supportedSubspace S := by
    rw [hc]
    exact hGS
  have he := completeForm_joint C N F H hFR hBG hF hH a hTF hTH
  simpa only [hc] using he

end RhNativeTranslationAdjoint
#print axioms RhNativeTranslationAdjoint.translated_inverse
#print axioms RhNativeTranslationAdjoint.completeForm_adjoint
