import RhComplexWeightedBridge001
import RhActualWeightedClosure001

/-! Actual complex physical primitive core inclusion in the concrete weighted
Hilbert domain. Pairing the two real constructions uses the actual complex Lp
norm and native full-energy identity, never a pointwise Fourier norm split. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ContDiff BigOperators ENNReal
namespace RhActualComplexCore
open RhAnchored RhWeightedMeasureEmbedding RhWeightedEnergyIdentity
open RhWeightedPrimitiveLift RhComplexWeightedBridge

/-- The actual complex anchored primitive, defined by its Bochner components. -/
def complexPrimitive (R : ℝ) (v : ℝ → ℂ) (t : ℝ) : ℂ :=
  (primitive R (fun x => (v x).re) t : ℂ) +
    Complex.I * (primitive R (fun x => (v x).im) t : ℂ)

/-- Zero extension in physical space, before passage to L2 quotients. -/
def complexPrimitiveExtension (R : ℝ) (v : ℝ → ℂ) (t : ℝ) : ℂ :=
  (zeroExtension R (primitive R (fun x => (v x).re)) t : ℂ) +
    Complex.I * (zeroExtension R (primitive R (fun x => (v x).im)) t : ℂ)

lemma pair_supported {R : ℝ} {F G : WeightedSpace}
    (hF : F ∈ supportedSubspace R) (hG : G ∈ supportedSubspace R) :
    F + Complex.I • G ∈ supportedSubspace R := by
  rw [mem_supportedSubspace_iff] at hF hG ⊢
  rw [pair_physical]
  filter_upwards [hF, hG, Lp.coeFn_add (physicalEmbedding F)
    (Complex.I • physicalEmbedding G), Lp.coeFn_smul Complex.I (physicalEmbedding G)]
    with t htF htG htAdd htSmul
  intro ht
  rw [htAdd]
  dsimp only [Pi.add_apply]
  rw [htF ht, htSmul]
  dsimp only [Pi.smul_apply]
  rw [htG ht]
  simp

/-- A genuine supported weighted vector for any complex physical L2 input. -/
def actualComplexPrimitiveLift {R : ℝ} (hR : 0 < R) (v : ℝ → ℂ)
    (hv : MemLp v 2 (physicalMeasure R)) : WeightedSpace :=
  actualPrimitiveLift hR (fun t => (v t).re) hv.re +
    Complex.I • actualPrimitiveLift hR (fun t => (v t).im) hv.im

lemma actualComplexPrimitiveLift_supported {R : ℝ} (hR : 0 < R) (v : ℝ → ℂ)
    (hv : MemLp v 2 (physicalMeasure R)) :
    actualComplexPrimitiveLift hR v hv ∈ supportedSubspace R := by
  apply pair_supported
  · exact actualPrimitiveLift_supported hR _ hv.re
  · exact actualPrimitiveLift_supported hR _ hv.im

lemma actualComplexPrimitiveLift_physical_ae {R : ℝ} (hR : 0 < R) (v : ℝ → ℂ)
    (hv : MemLp v 2 (physicalMeasure R)) :
    physicalEmbedding (actualComplexPrimitiveLift hR v hv) =ᵐ[volume]
      complexPrimitiveExtension R v := by
  unfold actualComplexPrimitiveLift
  rw [pair_physical, actualPrimitiveLift_physical, actualPrimitiveLift_physical]
  let ur := RhTail.physicalFourierVector R (primitive R (fun t => (v t).re))
    (primitive_memLp hv.re)
  let ui := RhTail.physicalFourierVector R (primitive R (fun t => (v t).im))
    (primitive_memLp hv.im)
  have her : ur =ᵐ[volume] RhTail.complexExtension R (primitive R (fun t => (v t).re)) :=
    (RhTail.complexExtension_memLp (primitive_memLp hv.re)).coeFn_toLp
  have hei : ui =ᵐ[volume] RhTail.complexExtension R (primitive R (fun t => (v t).im)) :=
    (RhTail.complexExtension_memLp (primitive_memLp hv.im)).coeFn_toLp
  filter_upwards [Lp.coeFn_add ur (Complex.I • ui), Lp.coeFn_smul Complex.I ui, her, hei]
    with t htAdd htSmul htR htI
  rw [htAdd]
  dsimp only [Pi.add_apply]
  rw [htSmul]
  dsimp only [Pi.smul_apply]
  rw [htR, htI]
  rfl

/-- Finiteness is for the actual FULL complex native energy. -/
theorem actualComplexPrimitiveLift_energy_finite {R : ℝ} (hR : 0 < R) (v : ℝ → ℂ)
    (hv : MemLp v 2 (physicalMeasure R)) :
    RhTail.fullFrequencyEnergy (1 / 2)
      (physicalEmbedding (actualComplexPrimitiveLift hR v hv)) < ⊤ :=
  weighted_native_energy_finite _

/-- The complex primitive is a same-window smooth compact weighted-norm limit.
All scalar companions of the complete form remain continuous in this norm. -/
theorem actual_complex_smooth_weighted_approximation {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℂ} (hv : MemLp v 2 (physicalMeasure R)) :
    ∃ (f : ℕ → ℝ → ℂ) (X : ℕ → WeightedSpace),
      (∀ n, ContDiff ℝ ∞ (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      (∀ n, tsupport (f n) ⊆ Ioo (-R) R) ∧
      (∀ n, X n ∈ supportedSubspace R) ∧
      (∀ n, physicalEmbedding (X n) =ᵐ[volume] f n) ∧
      Tendsto (fun n => ‖X n - actualComplexPrimitiveLift hR v hv‖) atTop (𝓝 0) := by
  obtain ⟨fr, Xr, hrS, hrC, hrT, hrA, hr0⟩ :=
    RhActualWeightedClosure.actual_smooth_weighted_approximation hR hv.re
  obtain ⟨fi, Xi, hiS, hiC, hiT, hiA, hi0⟩ :=
    RhActualWeightedClosure.actual_smooth_weighted_approximation hR hv.im
  let f : ℕ → ℝ → ℂ := fun n t => (fr n t : ℂ) + Complex.I • (fi n t : ℂ)
  let X : ℕ → WeightedSpace := fun n => (Xr n : WeightedSpace) + Complex.I • (Xi n : WeightedSpace)
  have hsub (n : ℕ) : tsupport (f n) ⊆ tsupport (fr n) ∪ tsupport (fi n) := by
    apply closure_minimal _ (isClosed_closure.union isClosed_closure)
    intro t ht
    by_cases hr : fr n t = 0
    · by_cases hi : fi n t = 0
      · exact False.elim (ht (by simp [f, hr, hi]))
      · exact Or.inr (subset_tsupport (fi n) hi)
    · exact Or.inl (subset_tsupport (fr n) hr)
  have hImage (n : ℕ) : physicalEmbedding (X n) =ᵐ[volume] f n := by
    change physicalEmbedding ((Xr n : WeightedSpace) + Complex.I • (Xi n : WeightedSpace)) =ᵐ[volume] _
    rw [pair_physical]
    filter_upwards [hrA n, hiA n, Lp.coeFn_add (physicalEmbedding (Xr n : WeightedSpace))
      (Complex.I • physicalEmbedding (Xi n : WeightedSpace)),
      Lp.coeFn_smul Complex.I (physicalEmbedding (Xi n : WeightedSpace))]
      with t htR htI htAdd htSmul
    rw [htAdd]
    dsimp only [Pi.add_apply]
    rw [htSmul]
    dsimp only [Pi.smul_apply]
    rw [htR, htI]
  have hCost (n : ℕ) : ‖X n - actualComplexPrimitiveLift hR v hv‖ ≤
      ‖Xr n - actualPrimitiveSupportedLift hR (fun t => (v t).re) hv.re‖ +
      ‖Xi n - actualPrimitiveSupportedLift hR (fun t => (v t).im) hv.im‖ := by
    have he : X n - actualComplexPrimitiveLift hR v hv =
        ((Xr n : WeightedSpace) - actualPrimitiveLift hR (fun t => (v t).re) hv.re) +
        Complex.I • ((Xi n : WeightedSpace) - actualPrimitiveLift hR (fun t => (v t).im) hv.im) := by
      dsimp [X, actualComplexPrimitiveLift]
      rw [smul_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖(Xr n : WeightedSpace) - actualPrimitiveLift hR (fun t => (v t).re) hv.re‖ +
          ‖Complex.I • ((Xi n : WeightedSpace) - actualPrimitiveLift hR (fun t => (v t).im) hv.im)‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, Complex.norm_I, one_mul]; rfl
  have hZero : Tendsto (fun n => ‖X n - actualComplexPrimitiveLift hR v hv‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) hCost
    simpa only [zero_add, RCLike.re_eq_complex_re, RCLike.im_eq_complex_im] using hr0.add hi0
  refine ⟨f, X, ?_, ?_, ?_, ?_, hImage, hZero⟩
  · intro n
    exact (Complex.ofRealCLM.contDiff.comp (hrS n)).add
      ((Complex.ofRealCLM.contDiff.comp (hiS n)).const_smul Complex.I)
  · intro n
    exact ((hrC n).union (hiC n)).of_isClosed_subset isClosed_closure (hsub n)
  · intro n t ht
    rcases hsub n ht with hr | hi
    · exact hrT n hr
    · exact hiT n hi
  · intro n
    exact pair_supported (Xr n).property (Xi n).property

end RhActualComplexCore
#print axioms RhActualComplexCore.actualComplexPrimitiveLift_supported
#print axioms RhActualComplexCore.actualComplexPrimitiveLift_physical_ae
#print axioms RhActualComplexCore.actualComplexPrimitiveLift_energy_finite
#print axioms RhActualComplexCore.actual_complex_smooth_weighted_approximation
