import RhWeightedTranslation001

/-! Exact actual spatial translations, convention tau_a F(t)=F(t+a).
These identities concern actual L2 and weighted Fourier representatives.
No form invariance or arithmetic estimate is assumed.
-/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhNativeTranslationAlgebra
open RhWeightedMeasureEmbedding RhNativeCompleteBilinear RhNativeCompleteDictionary
open RhWeightedTranslation RhNativeBoundedPartControl

lemma translation_comp (u : WholeSpace) (a b : ℝ) :
    translation a (translation b u) = translation (a+b) u := by
  apply Lp.ext
  have hp := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae
    (translation_ae u b)
  filter_upwards [translation_ae (translation b u) a, hp, translation_ae u (a+b)]
    with t ht hb hab
  rw [ht, hb, hab]
  congr 1
  ring

lemma translation_zero (u : WholeSpace) : translation 0 u = u := by
  apply Lp.ext
  simpa only [add_zero] using translation_ae u 0

lemma translation_inner (u v : WholeSpace) (a : ℝ) :
    inner ℝ (translation a u) (translation a v) = inner ℝ u v := by
  exact (Lp.compMeasurePreservingₗᵢ ℝ (fun t : ℝ => t+a)
    (measurePreserving_add_right volume a)).inner_map_map u v

lemma physical_integrable_add (F G : WeightedSpace)
    (hF : Integrable (physicalEmbedding F) volume)
    (hG : Integrable (physicalEmbedding G) volume) :
    Integrable (physicalEmbedding (F+G)) volume := by
  rw [map_add]
  exact (hF.add hG).congr (Lp.coeFn_add (physicalEmbedding F) (physicalEmbedding G)).symm

lemma translated_add (F G : WeightedSpace)
    (hF : Integrable (physicalEmbedding F) volume)
    (hG : Integrable (physicalEmbedding G) volume) (a : ℝ) :
    translated (F+G) (physical_integrable_add F G hF hG) a =
      translated F hF a + translated G hG a := by
  apply physicalEmbedding_injective
  rw [translated_physical, map_add, map_add, map_add, translated_physical, translated_physical]

lemma translated_physical_inner (F G : WeightedSpace)
    (hF : Integrable (physicalEmbedding F) volume)
    (hG : Integrable (physicalEmbedding G) volume) (a : ℝ) :
    inner ℝ (physicalEmbedding (translated F hF a))
      (physicalEmbedding (translated G hG a)) =
    inner ℝ (physicalEmbedding F) (physicalEmbedding G) := by
  rw [translated_physical, translated_physical]
  exact translation_inner _ _ a

lemma translated_graph_inner (F G : WeightedSpace)
    (hF : Integrable (physicalEmbedding F) volume)
    (hG : Integrable (physicalEmbedding G) volume) (a : ℝ) :
    inner ℝ (translated F hF a) (translated G hG a) = inner ℝ F G := by
  have hs := translated_norm (F+G) (physical_integrable_add F G hF hG) a
  rw [translated_add F G hF hG a] at hs
  have hs2 := congrArg (fun t : ℝ => t^2) hs
  rw [norm_add_sq_real, norm_add_sq_real, translated_norm F hF a, translated_norm G hG a] at hs2
  linarith

lemma archPair_joint (F G : WeightedSpace)
    (hF : Integrable (physicalEmbedding F) volume)
    (hG : Integrable (physicalEmbedding G) volume) (a : ℝ) :
    archPair (translated F hF a) (translated G hG a) = archPair F G := by
  rw [archPair_apply, archPair_apply, translated_graph_inner, translated_physical_inner]

lemma spatialPair_joint (F G : WeightedSpace)
    (hF : Integrable (physicalEmbedding F) volume)
    (hG : Integrable (physicalEmbedding G) volume) (a : ℝ) :
    spatialPair (translated F hF a) (translated G hG a) = spatialPair F G :=
  translated_physical_inner F G hF hG a

lemma twoShift_translation (u : WholeSpace) (a ell : ℝ) :
    twoShift ell (translation a u) = translation a (twoShift ell u) := by
  change translation ell (translation a u) + translation (-ell) (translation a u) =
    translation a (translation ell u + translation (-ell) u)
  rw [map_add, translation_comp, translation_comp, translation_comp, translation_comp]
  simp only [add_comm]

lemma shiftPair_joint (F G : WeightedSpace)
    (hF : Integrable (physicalEmbedding F) volume)
    (hG : Integrable (physicalEmbedding G) volume) (a ell : ℝ) :
    shiftPair ell (translated F hF a) (translated G hG a) = shiftPair ell F G := by
  rw [shiftPair_apply, shiftPair_apply, translated_physical, translated_physical,
    twoShift_translation, twoShift_translation, translation_inner, translation_inner]

end RhNativeTranslationAlgebra
#print axioms RhNativeTranslationAlgebra.translation_comp
#print axioms RhNativeTranslationAlgebra.translation_inner
#print axioms RhNativeTranslationAlgebra.translated_graph_inner
#print axioms RhNativeTranslationAlgebra.archPair_joint
#print axioms RhNativeTranslationAlgebra.shiftPair_joint
