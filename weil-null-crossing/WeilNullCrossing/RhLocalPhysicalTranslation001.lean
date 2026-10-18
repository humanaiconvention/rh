import RhLocalTranslationSpan001
import RhTranslationSupport001
import RhNativeTranslationAlgebra001

/-! A nonzero compact physical L2 vector has infinite-dimensional local
translation span. This is an actual AE support statement; all far-parameter
steps are ambient translation algebra, not native arithmetic form claims. -/
noncomputable section
set_option maxHeartbeats 150000
open Set Filter MeasureTheory
open scoped Topology
namespace RhLocalPhysicalTranslation
open RhWeightedMeasureEmbedding RhNativeCompleteBilinear RhNativeTranslationAlgebra
open RhTranslationSupport RhLocalTranslationSpan

/-- Closedness is not needed here; only the exact linear support property. -/
def supportSpace (R : ℝ) : Submodule ℝ WholeSpace where
  carrier := {u | Supported R u}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E:=ℂ) (p:=2) (μ:=volume)] with t ht
    intro hout
    exact ht
  add_mem' := by
    intro u v hu hv
    filter_upwards [hu,hv,Lp.coeFn_add u v] with t huT hvT he
    intro hout
    rw [he]
    change u t + v t = 0
    rw [huT hout,hvT hout,add_zero]
  smul_mem' := by
    intro c u hu
    filter_upwards [hu,Lp.coeFn_smul c u] with t huT he
    intro hout
    rw [he]
    change c • u t = 0
    rw [huT hout,smul_zero]

lemma supported_mono {R S : ℝ} {u : WholeSpace} (hRS : R ≤ S)
    (hu : Supported R u) : Supported S u := by
  filter_upwards [hu] with t ht
  intro hout
  exact ht (fun hi => hout ⟨by linarith [hi.1],by linarith [hi.2]⟩)

abbrev action (a : ℝ) : WholeSpace →ₗ[ℝ] WholeSpace := (translation a).toLinearMap

/-- No nonzero compact L2 vector can have a finite-dimensional span of its
translates from ANY open interval of shifts about zero. -/
theorem not_finite_local_span {R : ℝ} (u : WholeSpace) (hu : Supported R u)
    (hne : u ≠ 0) {eps : ℝ} (heps : 0 < eps) :
    ¬ FiniteDimensional ℝ (localSpan action u eps) := by
  intro hfd
  letI : FiniteDimensional ℝ (localSpan action u eps) := hfd
  have hle : localSpan action u eps ≤ supportSpace (R+eps) := by
    apply Submodule.span_le.mpr
    rintro x ⟨a,ha,rfl⟩
    exact supported_mono (by linarith [(abs_lt.mpr ha)]) (translation_supported hu a)
  have hall (a : ℝ) : Supported (R+eps) (translation a u) := by
    exact hle (orbit_mem_of_finite_local_span action translation_zero
      (fun a b x => (translation_comp x a b).symm) u heps a)
  exact not_all_translates_supported hu hne hall

end RhLocalPhysicalTranslation
#print axioms RhLocalPhysicalTranslation.supported_mono
#print axioms RhLocalPhysicalTranslation.not_finite_local_span

