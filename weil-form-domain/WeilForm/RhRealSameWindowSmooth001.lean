import RhRealSupportedDomain001
import RhSupportedInwardStrong001
import RhActualCoreBump001

/-! Same-window REAL smooth approximation and exact real complete-domain
identification. Complex supported vectors are not inserted into the real core.
Every approximation has its actual real spatial representative. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ContDiff
namespace RhRealSameWindowSmooth
open RhWeightedMeasureEmbedding RhWeightedInwardMap RhSupportedInwardStrong
open RhRealMollifier RhRealSupportedDomain RhFlatSmoothCore

lemma inwardMap_real {R r : ℝ} (hr : 1 ≤ r) (F : SupportedSpace R)
    (hreal : IsPhysicalReal (F : WeightedSpace)) :
    IsPhysicalReal (inwardMap hr F : WeightedSpace) := by
  have hr0 : 0 < r := by linarith
  filter_upwards [inwardMap_physical_ae hr F,
    RhWeightedDilation.ae_comp_div (inv_pos.mpr hr0) hreal] with t ht hreal
  rw [ht]
  simp only [div_inv_eq_mul] at hreal
  simp [RhDilation.complexDilate, Complex.mul_im, hreal]

/-- Complete weighted convergence of genuine real C-infinity representatives
with support strictly inside the SAME window, for every actual real vector. -/
theorem real_same_window_smooth_approximation {R : ℝ} (hR : 0 < R) (F : SupportedSpace R)
    (hreal : IsPhysicalReal (F : WeightedSpace)) :
    ∃ (f : ℕ → ℝ → ℝ) (X : ℕ → SupportedSpace R),
      (∀ n, ContDiff ℝ ∞ (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      (∀ n, tsupport (f n) ⊆ Ioo (-R) R) ∧
      (∀ n, physicalEmbedding (X n : WeightedSpace) =ᵐ[volume] fun t => (f n t : ℂ)) ∧
      Tendsto (fun n => ‖(X n : WeightedSpace) - (F : WeightedSpace)‖) atTop (𝓝 0) := by
  let phi : ContDiffBump (0 : ℝ) := RhActualCoreBump.centralBump R hR 0
  let Y (n : ℕ) : SupportedSpace (inwardRadius R n) := inwardMap (inwardScale_ge_one n) F
  have heps (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hex (n : ℕ) := exists_real_smooth_across_gap phi
    (inwardRadius_pos_lt hR n).2 (heps n) (Y n)
      (inwardMap_real (inwardScale_ge_one n) F hreal)
  choose f X hfS hfC hfT hfA hfErr using hex
  have hY : Tendsto (fun n => ‖(Y n : WeightedSpace) - (F : WeightedSpace)‖)
      atTop (𝓝 0) := canonical_supported_inward_norm_tendsto F
  have hbound (n : ℕ) : ‖(X n : WeightedSpace) - (F : WeightedSpace)‖ ≤
      1 / ((n : ℝ) + 1) + ‖(Y n : WeightedSpace) - (F : WeightedSpace)‖ := by
    have ht : ‖(X n : WeightedSpace) - (F : WeightedSpace)‖ ≤
        ‖(X n : WeightedSpace) - (Y n : WeightedSpace)‖ +
          ‖(Y n : WeightedSpace) - (F : WeightedSpace)‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (X n : WeightedSpace) (Y n : WeightedSpace) (F : WeightedSpace)
    have he := hfErr n
    linarith
  have hzero : Tendsto (fun n => ‖(X n : WeightedSpace) - (F : WeightedSpace)‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) hbound
    have he : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [zero_add] using he.add hY
  exact ⟨f, X, hfS, hfC, hfT, hfA, hzero⟩

/-- Every actual supported-real complete graph vector belongs to the old flat
real smooth core; no physical derivative representation is required. -/
theorem realSupported_mem_flatCore {R : ℝ} (hR : 0 < R) {F : WeightedSpace}
    (hF : F ∈ realSupportedSubspace R) : F ∈ flatCore R := by
  obtain ⟨hSupp, hReal⟩ := (mem_realSupported_iff R F).mp hF
  let Y : SupportedSpace R := ⟨F, hSupp⟩
  obtain ⟨f, X, hfS, hfC, hfT, hfA, hNorm⟩ :=
    real_same_window_smooth_approximation hR Y hReal
  have hX (n : ℕ) : (X n : WeightedSpace) ∈ flatCore R :=
    smooth_generator_mem ⟨f n, hfS n, hfC n, hfT n, hfA n⟩
  exact (flatCore_isClosed R).mem_of_tendsto
    (tendsto_iff_norm_sub_tendsto_zero.mpr hNorm) (Eventually.of_forall hX)

/-- Exact common-domain equality for the actual supported REAL complete form
space. It is not an equality with the full complex supported space. -/
theorem flatCore_eq_realSupported {R : ℝ} (hR : 0 < R) :
    flatCore R = realSupportedSubspace R := by
  apply le_antisymm (flatCore_le_realSupported R)
  intro F hF
  exact realSupported_mem_flatCore hR hF

end RhRealSameWindowSmooth
#print axioms RhRealSameWindowSmooth.inwardMap_real
#print axioms RhRealSameWindowSmooth.real_same_window_smooth_approximation
#print axioms RhRealSameWindowSmooth.realSupported_mem_flatCore
#print axioms RhRealSameWindowSmooth.flatCore_eq_realSupported
