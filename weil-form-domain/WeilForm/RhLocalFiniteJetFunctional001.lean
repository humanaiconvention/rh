import RhFiniteJetFunctional001

/-! Local finite-point jet exclusion. Only compact smooth tests supported in
the declared open set are required. The exact shrinking capacity tests are
proved eventually supported there; no cutoff multiplier theorem is assumed. -/
noncomputable section
set_option maxHeartbeats 150000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace RhLocalFiniteJetFunctional
open RhWeightedMeasureEmbedding RhSmoothJetProfiles RhSmoothJetLifts
open RhTranslatedJetCapacity

lemma scaledProfile_tsupport_subset (chi : ContDiffBump (0 : ℝ)) (j : ℕ)
    {r : ℝ} (hr : 0 < r) (x : ℝ) :
    tsupport (scaledProfile chi j r x) ⊆ Metric.closedBall x (chi.rOut / r) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro t ht
  have hn : chi ((t-x)*r) ≠ 0 := by
    intro hz
    apply ht
    simp [scaledProfile, profile, hz]
  have hb : |(t-x)*r| < chi.rOut := by
    have hm : (t-x)*r ∈ Function.support (chi : ℝ → ℝ) := hn
    rw [chi.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hm
    exact hm
  rw [Metric.mem_closedBall, Real.dist_eq]
  apply le_of_lt
  apply (lt_div_iff₀ hr).mpr
  simpa only [abs_mul, abs_of_pos hr] using hb

/-- Eventual support is literal topological support of the actual smooth
representative, rather than an AE support statement inferred from L2 values. -/
theorem eventually_tsupport_subset_open (chi : ContDiffBump (0 : ℝ)) (j : ℕ)
    {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) :
    ∀ᶠ n in atTop, tsupport (scaledProfile chi j (scale n) x) ⊆ U := by
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hh : ∀ᶠ n in atTop, chi.rOut / eps < scale n :=
    scale_tendsto.eventually (eventually_gt_atTop _)
  filter_upwards [hh] with n hn
  have hrad : chi.rOut / scale n < eps := by
    apply (div_lt_iff₀ (scale_pos n)).mpr
    have h := (div_lt_iff₀ heps).mp hn
    nlinarith
  intro t ht
  apply hball
  have hs := scaledProfile_tsupport_subset chi j (scale_pos n) x ht
  rw [Metric.mem_closedBall] at hs
  rw [Metric.mem_ball]
  exact hs.trans_lt hrad

/-- Local distributional representation on an open set. The ambient
functional need not vanish on smooth tests supported outside this set. -/
def RepresentsOn {d K : ℕ} (T : WeightedSpace →L[ℝ] ℝ) (U : Set ℝ)
    (points : Fin d → ℝ) (a : Fin d → Fin (K+1) → ℝ) : Prop :=
  ∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ U →
    ∀ F : WeightedSpace, (physicalEmbedding F =ᵐ[volume] fun t => (f t : ℂ)) →
      T F = ∑ i, ∑ k, a i k * iteratedDeriv k.val f (points i)

/-- A locally represented finite point-jet functional has every coefficient
zero. Exact capacity tests stay inside U eventually, so no global support or
localization assumption is smuggled into the conclusion. -/
theorem coefficients_zero {d K : ℕ} (T : WeightedSpace →L[ℝ] ℝ)
    (U : Set ℝ) (hU : IsOpen U) (points : Fin d → ℝ)
    (hpU : ∀ i, points i ∈ U) (hp : Function.Injective points)
    (a : Fin d → Fin (K+1) → ℝ) (hT : RepresentsOn T U points a) :
    ∀ i j, a i j = 0 := by
  let chi : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  intro i j
  have hg : ∀ᶠ n in atTop, ∀ l ∈ Finset.univ.erase i,
      scaledProfile chi j.val (scale n) (points i) =ᶠ[𝓝 (points l)] 0 := by
    rw [Filter.eventually_all_finset]
    intro l hl
    exact eventually_zero_germ chi j.val (points i) (points l)
      (fun he => (Finset.mem_erase.mp hl).1 (hp he))
  have hs := eventually_tsupport_subset_open chi j.val hU (hpU i)
  apply continuous_functional_constant_jet_zero j.val (profileLift chi j.val)
    (profileLift_supported chi j.val) (points i) T
  filter_upwards [hg, hs] with n hn hsN
  have hv := hT (scaledProfile chi j.val (scale n) (points i))
    (scaledProfile_contDiff chi j.val (scale n) (points i))
    (scaledProfile_compact chi j.val (scale_pos n).ne' (points i)) hsN
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

theorem vanishes_on_smooth {d K : ℕ} (T : WeightedSpace →L[ℝ] ℝ)
    (U : Set ℝ) (hU : IsOpen U) (points : Fin d → ℝ)
    (hpU : ∀ i, points i ∈ U) (hp : Function.Injective points)
    (a : Fin d → Fin (K+1) → ℝ) (hT : RepresentsOn T U points a)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ U) (F : WeightedSpace)
    (hF : physicalEmbedding F =ᵐ[volume] fun t => (f t : ℂ)) : T F = 0 := by
  rw [hT f hf hc hs F hF]
  simp [coefficients_zero T U hU points hpU hp a hT]

end RhLocalFiniteJetFunctional
#print axioms RhLocalFiniteJetFunctional.eventually_tsupport_subset_open
#print axioms RhLocalFiniteJetFunctional.coefficients_zero
#print axioms RhLocalFiniteJetFunctional.vanishes_on_smooth
