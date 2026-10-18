import RhFlatCoreReal001
import RhPulledPhysicalDictionary001
import RhDilationRankPhysical001

/-! Native BOTH-rank transport and uniform parameter control on the actual
closed real form domain. Real-valuedness is proved by the closed core, then
represented by a genuine physical L2 vector. Complex rank moments are never
silently replaced by their real parts.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhNativeRankDilationControl
open RhAnchored RhDilation RhDilationRank
open RhWeightedMeasureEmbedding RhWeightedPrimitiveLift RhNativeCompleteBilinear
open RhNativeCompleteDictionary RhFlatSmoothCore RhFlatCoreReal

/-- The exact signed pair of native archimedean ranks. -/
def rankValue (R : ℝ) (F : WeightedSpace) : ℝ :=
  2 * coshPair R F F - 2 * sinhPair R F F

lemma profilePair_realVector {R : ℝ} (F : WeightedSpace) (w : ℝ → ℝ)
    (hw : MemLp w 2 (physicalMeasure R))
    (hF : physicalEmbedding F = RhTail.physicalFourierVector R w hw)
    (f : ℝ → ℝ) (hf : MemLp f 2 (physicalMeasure R)) :
    profilePair R f hf F F = (∫ t in interval R, f t * w t)^2 := by
  rw [profilePair_diagonal]
  have hm : profileMoment R f hf F = ((∫ t in interval R, f t * w t : ℝ) : ℂ) := by
    change inner ℂ (RhTail.physicalFourierVector R f hf) (physicalEmbedding F) = _
    rw [hF]
    exact physicalVector_inner hf hw
  rw [hm]
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Exact identity for the whole signed rank component, not an inequality. -/
lemma rankValue_realVector {R : ℝ} (F : WeightedSpace) (w : ℝ → ℝ)
    (hw : MemLp w 2 (physicalMeasure R))
    (hF : physicalEmbedding F = RhTail.physicalFourierVector R w hw) :
    rankValue R F = rankForm R 1 w := by
  unfold rankValue coshPair sinhPair
  rw [profilePair_realVector F w hw hF _ (cosh_memLp R),
    profilePair_realVector F w hw hF _ (sinh_memLp R)]
  simp only [rankForm, moment, coshProfile, sinhProfile, profile, Real.sqrt_one, one_mul]

/-- Actual outward spatial vector equals dilation of the proved real physical
representative. Assigned representative values are changed only AE. -/
lemma outward_realVector {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace R) :
    physicalEmbedding (RhFlatCoreDilation.outwardMap hr F : WeightedSpace) =
      RhTail.physicalFourierVector (r * R) (dilate r (realPhysical F))
        (dilate_memLp_physical (by linarith : 0 < r) (realPhysical_memLp F)) := by
  apply Lp.ext
  have hr0 : 0 < r := by linarith
  have hf : physicalEmbedding (F : WeightedSpace) =ᵐ[volume]
      RhTail.complexExtension R (realPhysical F) := by
    rw [← physicalVector_realPhysical F]
    exact (RhTail.complexExtension_memLp (realPhysical_memLp F)).coeFn_toLp
  have h := (RhFlatCoreDilation.outwardMap_physical_ae hr F).trans
    (RhWeightedDilationInverse.complexDilate_congr_ae hr0 hf)
  rw [RhPulledPhysicalDictionary.complex_dilate_extension hr0] at h
  have hd : RhTail.physicalFourierVector (r * R) (dilate r (realPhysical F))
      (dilate_memLp_physical hr0 (realPhysical_memLp F)) =ᵐ[volume]
      RhTail.complexExtension (r * R) (dilate r (realPhysical F)) :=
    (RhTail.complexExtension_memLp (dilate_memLp_physical hr0 (realPhysical_memLp F))).coeFn_toLp
  exact h.trans hd.symm

/-- Genuine uniform rank perturbation on the ENTIRE actual real closed core.
The finite constant is imported from the proved compact-profile estimate. -/
theorem exists_flat_rank_graph_budget {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (hr1 : 1 ≤ r), r ≤ 2 → ∀ F : FlatCoreSpace R,
      |rankValue (r * R) (RhFlatCoreDilation.outwardMap (r := r) hr1 F : WeightedSpace) -
        rankValue R (F : WeightedSpace)| ≤ C * (r - 1) * ‖F‖^2 := by
  obtain ⟨C, hC, hbound⟩ := exists_physical_rank_perturbation_bound hR
  refine ⟨C, hC, ?_⟩
  intro r hr1 hr2 F
  rw [rankValue_realVector _ _ _ (outward_realVector hr1 F),
    rankValue_realVector _ _ _ (physicalVector_realPhysical F).symm]
  have h := hbound r hr1 hr2 (realPhysical F) (realPhysical_memLp F)
  rw [realPhysical_mass] at h
  have hm : ‖physicalEmbedding (F : WeightedSpace)‖^2 ≤ ‖F‖^2 := by
    have hn := physicalEmbedding_norm_apply_le (F : WeightedSpace)
    change ‖physicalEmbedding (F : WeightedSpace)‖ ≤ ‖F‖ at hn
    nlinarith [norm_nonneg (physicalEmbedding (F : WeightedSpace)), norm_nonneg F]
  exact h.trans (mul_le_mul_of_nonneg_left hm (mul_nonneg hC.le (sub_nonneg.mpr hr1)))

end RhNativeRankDilationControl
#print axioms RhNativeRankDilationControl.profilePair_realVector
#print axioms RhNativeRankDilationControl.rankValue_realVector
#print axioms RhNativeRankDilationControl.outward_realVector
#print axioms RhNativeRankDilationControl.exists_flat_rank_graph_budget
