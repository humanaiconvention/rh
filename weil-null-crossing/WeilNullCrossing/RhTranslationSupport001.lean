import RhWeightedTranslation001

/-! Actual L2 translation support and far-translate obstruction. All support
statements are AE statements on quotient representatives; endpoint contact is
handled by null sets. No arithmetic null vector is assumed to exist. -/
noncomputable section
set_option maxHeartbeats 100000
open Set Filter MeasureTheory
namespace RhTranslationSupport
open RhWeightedMeasureEmbedding RhNativeCompleteBilinear RhNativeCompleteDictionary
open RhNativeBoundedPartControl RhWeightedTranslation

/-- Physical support of an actual L2 class, without selected point values. -/
def Supported (R : ℝ) (u : WholeSpace) : Prop :=
  ∀ᵐ t ∂volume, t ∉ Icc (-R) R → u t = 0

/-- Literal translation convention is T_a u(t)=u(t+a). -/
theorem translation_supported {R : ℝ} {u : WholeSpace} (hu : Supported R u) (a : ℝ) :
    Supported (R+|a|) (translation a u) := by
  have hs := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hu
  filter_upwards [translation_ae u a, hs] with t ht hsT
  intro hout
  rw [ht]
  apply hsT
  intro hin
  apply hout
  have ha := le_abs_self a
  have hna := neg_le_abs a
  constructor <;> linarith [hin.1,hin.2]

/-- If the original and translated L2 classes both fit disjoint/touching
bounded support intervals, the vector must be zero. Equality is proved AE. -/
theorem supported_translation_forces_zero {R S a : ℝ} {u : WholeSpace}
    (hu : Supported R u) (htu : Supported S (translation a u))
    (hgap : R+S ≤ |a|) : u = 0 := by
  have hs := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hu
  have hz : translation a u = 0 := by
    apply (Lp.eq_zero_iff_ae_eq_zero).mpr
    filter_upwards [translation_ae u a, hs, htu,
      (volume : Measure ℝ).ae_ne (-S), (volume : Measure ℝ).ae_ne S]
      with t ht hsT htT hneg hpos
    change (translation a u) t = 0
    by_cases hi : t ∈ Icc (-S) S
    · have hlo : -S < t := lt_of_le_of_ne hi.1 (Ne.symm hneg)
      have hhi : t < S := lt_of_le_of_ne hi.2 hpos
      have hout : t+a ∉ Icc (-R) R := by
        intro h
        have hab : |a| < R+S := abs_lt.mpr ⟨by linarith [h.1],by linarith [h.2]⟩
        linarith
      rw [ht, hsT hout]
    · exact htT hi
  apply norm_eq_zero.mp
  rw [← translation_norm u a, hz, norm_zero]

/-- A concrete far translation leaves any prescribed fixed support window.
Only the already given compact-support radius is used. -/
theorem exists_translate_not_supported {R S : ℝ} {u : WholeSpace}
    (hu : Supported R u) (hne : u ≠ 0) :
    ∃ a : ℝ, ¬ Supported S (translation a u) := by
  let a : ℝ := |R|+|S|+1
  have ha : 0 < a := by dsimp only [a]; positivity
  have hgap : R+S ≤ |a| := by
    rw [abs_of_pos ha]
    dsimp only [a]
    linarith [le_abs_self R,le_abs_self S]
  exact ⟨a,fun ht => hne (supported_translation_forces_zero hu ht hgap)⟩

theorem not_all_translates_supported {R S : ℝ} {u : WholeSpace}
    (hu : Supported R u) (hne : u ≠ 0) :
    ¬ ∀ a : ℝ, Supported S (translation a u) := by
  obtain ⟨a,ha⟩ := exists_translate_not_supported (S:=S) hu hne
  exact fun hall => ha (hall a)

/-- Actual complete-domain translation preserves compact physical support
with the exact translated-radius enclosure. -/
theorem weighted_translated_supported {R : ℝ} (F : WeightedSpace)
    (hI : Integrable (physicalEmbedding F) volume) (hF : F ∈ supportedSubspace R) (a : ℝ) :
    translated F hI a ∈ supportedSubspace (R+|a|) := by
  rw [mem_supportedSubspace_iff, translated_physical]
  exact translation_supported ((mem_supportedSubspace_iff R F).mp hF) a

/-- A nonzero actual compact weighted vector cannot have every true physical
translation in a single fixed support window. -/
theorem weighted_not_all_translates_supported {R S : ℝ} (F : WeightedSpace)
    (hI : Integrable (physicalEmbedding F) volume) (hF : F ∈ supportedSubspace R)
    (hne : F ≠ 0) : ¬ ∀ a : ℝ, translated F hI a ∈ supportedSubspace S := by
  have hpne : physicalEmbedding F ≠ 0 := by
    intro hz
    apply hne
    apply physicalEmbedding_injective
    simpa only [map_zero] using hz
  intro hall
  apply not_all_translates_supported (S:=S) ((mem_supportedSubspace_iff R F).mp hF) hpne
  intro a
  have hh := (mem_supportedSubspace_iff S (translated F hI a)).mp (hall a)
  rw [translated_physical] at hh
  exact hh

end RhTranslationSupport
#print axioms RhTranslationSupport.translation_supported
#print axioms RhTranslationSupport.supported_translation_forces_zero
#print axioms RhTranslationSupport.not_all_translates_supported
#print axioms RhTranslationSupport.weighted_translated_supported
#print axioms RhTranslationSupport.weighted_not_all_translates_supported

