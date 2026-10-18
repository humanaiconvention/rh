import RhModulatedCutoffProfiles001

/-! PRIVATE one-point removal of literal compact smooth representatives.
The weighted error is the actual cutoffVector proved small in the preceding
module. No finite-jet representation or arithmetic flux hypothesis occurs.
-/
set_option maxHeartbeats 150000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RhCutoffPointRemoval
open RhWeightedMeasureEmbedding RhModulatedCutoffProfiles RhTranslatedJetCapacity

 def removedFunction (f : ℝ → ℝ) (chi : ContDiffBump (0 : ℝ))
    (x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  f t - f t * chi ((t-x)*scale n)

lemma removed_contDiff (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (chi : ContDiffBump (0 : ℝ)) (x : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (removedFunction f chi x n) := by
  have hchi : ContDiff ℝ ∞ (chi : ℝ → ℝ) := chi.contDiff
  exact hf.sub (hf.mul (hchi.comp ((contDiff_id.sub contDiff_const).mul contDiff_const)))

/-- Removing a point cannot enlarge the original literal support. -/
lemma removed_tsupport_subset (f : ℝ → ℝ) (chi : ContDiffBump (0 : ℝ))
    (x : ℝ) (n : ℕ) : tsupport (removedFunction f chi x n) ⊆ tsupport f := by
  have he : removedFunction f chi x n =
      f * (fun t : ℝ => 1 - chi ((t-x)*scale n)) := by
    funext t
    simp only [removedFunction, Pi.mul_apply]
    ring
  rw [he]
  exact tsupport_mul_subset_left

lemma removed_compact (f : ℝ → ℝ) (hc : HasCompactSupport f)
    (chi : ContDiffBump (0 : ℝ)) (x : ℝ) (n : ℕ) :
    HasCompactSupport (removedFunction f chi x n) := by
  apply hc.mono'
  intro t ht
  exact removed_tsupport_subset f chi x n (subset_tsupport _ ht)

/-- Literal zero on an open neighborhood, not a point value of an L2 class. -/
lemma removed_zero_germ (f : ℝ → ℝ) (chi : ContDiffBump (0 : ℝ))
    (x : ℝ) (n : ℕ) : removedFunction f chi x n =ᶠ[𝓝 x] 0 := by
  have ht : Tendsto (fun t : ℝ => (t-x)*scale n) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => (t-x)*scale n) := by fun_prop
    simpa only [sub_self, zero_mul] using hc.tendsto x
  have hh := ht.eventually chi.eventuallyEq_one
  filter_upwards [hh] with t ht
  simp only [removedFunction, ht, Pi.one_apply, Pi.zero_apply, mul_one, sub_self]

lemma removed_not_mem_tsupport (f : ℝ → ℝ) (chi : ContDiffBump (0 : ℝ))
    (x : ℝ) (n : ℕ) : x ∉ tsupport (removedFunction f chi x n) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  exact removed_zero_germ f chi x n

/-- Actual ambient complete-domain approximation vector. -/
def removedVector (F : WeightedSpace) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (chi : ContDiffBump (0 : ℝ)) (x : ℝ) (n : ℕ) : WeightedSpace :=
  F - cutoffVector f hf chi x n

/-- The actual weighted vector agrees AE with the literal smooth function. -/
theorem removedVector_physical_ae (F : WeightedSpace) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hF : physicalEmbedding F =ᵐ[volume] fun t => (f t : ℂ))
    (chi : ContDiffBump (0 : ℝ)) (x : ℝ) (n : ℕ) :
    physicalEmbedding (removedVector F f hf chi x n) =ᵐ[volume]
      fun t => (removedFunction f chi x n t : ℂ) := by
  rw [removedVector, map_sub]
  have hcut := cutoffVector_physical_ae f hf chi x n
  filter_upwards [hF, hcut,
    Lp.coeFn_sub (physicalEmbedding F) (physicalEmbedding (cutoffVector f hf chi x n))]
    with t hFt hct hst
  rw [hst]
  simp only [Pi.sub_apply]
  rw [hFt, hct]
  simp only [removedFunction, Complex.ofReal_sub, Complex.ofReal_mul]

/-- Strong convergence is a consequence of the UNCONDITIONAL actual cutoff
norm bound, not an assumption equal to the point-removal target. -/
theorem removedVector_tendsto (F : WeightedSpace) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (chi : ContDiffBump (0 : ℝ)) (x : ℝ) :
    Tendsto (removedVector F f hf chi x) atTop (𝓝 F) := by
  have hz : Tendsto (cutoffVector f hf chi x) atTop (𝓝 (0 : WeightedSpace)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (cutoffVector_norm_tendsto f hf hc chi x)
  have hconst : Tendsto (fun _ : ℕ => F) atTop (𝓝 F) := tendsto_const_nhds
  change Tendsto (fun n => F - cutoffVector f hf chi x n) atTop (𝓝 F)
  simpa only [sub_zero] using hconst.sub hz

end RhCutoffPointRemoval
#print axioms RhCutoffPointRemoval.removed_contDiff
#print axioms RhCutoffPointRemoval.removed_tsupport_subset
#print axioms RhCutoffPointRemoval.removed_compact
#print axioms RhCutoffPointRemoval.removed_zero_germ
#print axioms RhCutoffPointRemoval.removed_not_mem_tsupport
#print axioms RhCutoffPointRemoval.removedVector_physical_ae
#print axioms RhCutoffPointRemoval.removedVector_tendsto
