import RhSmoothJetLifts001

/-! A continuous functional for the ACTUAL complete Fourier norm cannot be a
nonzero finite linear combination of point jets on compact smooth tests.
The finite-jet representation is the stated hypothesis; every isolating test,
its exact jets, its physical quotient, and its vanishing norm are constructed. -/
noncomputable section
set_option maxHeartbeats 150000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace RhFiniteJetFunctional
open RhWeightedMeasureEmbedding RhSmoothJetProfiles RhSmoothJetLifts
open RhTranslatedJetCapacity

/-- Exact action on genuine real compact smooth representatives. -/
def Represents {d K : ℕ} (T : WeightedSpace →L[ℝ] ℝ) (points : Fin d → ℝ)
    (a : Fin d → Fin (K+1) → ℝ) : Prop :=
  ∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
    ∀ F : WeightedSpace, (physicalEmbedding F =ᵐ[volume] fun t => (f t : ℂ)) →
      T F = ∑ i, ∑ k, a i k * iteratedDeriv k.val f (points i)

/-- The arithmetic complete-domain norm has zero finite-point jet capacity.
This does not assert that an arbitrary boundary distribution is already known
to have the stated finite-jet representation. -/
theorem coefficients_zero {d K : ℕ} (T : WeightedSpace →L[ℝ] ℝ)
    (points : Fin d → ℝ) (hp : Function.Injective points)
    (a : Fin d → Fin (K+1) → ℝ) (hT : Represents T points a) :
    ∀ i j, a i j = 0 := by
  let chi : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  intro i j
  have hg : ∀ᶠ n in atTop, ∀ l ∈ Finset.univ.erase i,
      scaledProfile chi j.val (scale n) (points i) =ᶠ[𝓝 (points l)] 0 := by
    rw [Filter.eventually_all_finset]
    intro l hl
    exact eventually_zero_germ chi j.val (points i) (points l)
      (fun he => (Finset.mem_erase.mp hl).1 (hp he))
  apply continuous_functional_constant_jet_zero j.val (profileLift chi j.val)
    (profileLift_supported chi j.val) (points i) T
  filter_upwards [hg] with n hn
  have hv := hT (scaledProfile chi j.val (scale n) (points i))
    (scaledProfile_contDiff chi j.val (scale n) (points i))
    (scaledProfile_compact chi j.val (scale_pos n).ne' (points i))
    (jetLift chi j.val (points i) n) (jetLift_physical chi j.val (points i) n)
  change T (jetLift chi j.val (points i) n) = a i j
  rw [hv]
  have hc (k : Fin (K+1)) : iteratedDeriv k.val
      (scaledProfile chi j.val (scale n) (points i)) (points i) =
        if k = j then 1 else 0 := by
    simpa only [Fin.ext_iff] using
      scaledProfile_jet chi j.val k.val (scale_pos n).ne' (points i)
  rw [Finset.sum_eq_single i]
  · simp only [hc, mul_ite, mul_one, mul_zero]
    simp
  · intro l hl hli
    apply Finset.sum_eq_zero
    intro k hk
    have he := (hn l (Finset.mem_erase.mpr ⟨hli, hl⟩)).iteratedDeriv_eq k.val
    simp only [iteratedDeriv_const_zero] at he
    simp only [he, mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Consequently the functional is zero on every represented smooth test;
no global support, arithmetic flux, or positivity conclusion is inferred. -/
theorem vanishes_on_smooth {d K : ℕ} (T : WeightedSpace →L[ℝ] ℝ)
    (points : Fin d → ℝ) (hp : Function.Injective points)
    (a : Fin d → Fin (K+1) → ℝ) (hT : Represents T points a)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (F : WeightedSpace) (hF : physicalEmbedding F =ᵐ[volume] fun t => (f t : ℂ)) :
    T F = 0 := by
  rw [hT f hf hc F hF]
  simp [coefficients_zero T points hp a hT]

end RhFiniteJetFunctional
#print axioms RhFiniteJetFunctional.coefficients_zero
#print axioms RhFiniteJetFunctional.vanishes_on_smooth

