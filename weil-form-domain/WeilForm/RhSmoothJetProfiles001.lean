import RhTranslatedJetDictionary001
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Literal smooth jet profiles. Pointwise jets belong to these explicit smooth
representatives, never to arbitrary representatives of a physical L2 class. -/
noncomputable section
set_option maxHeartbeats 150000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace RhSmoothJetProfiles
open RhTranslatedJetCapacity

def profile (chi : ContDiffBump (0 : ℝ)) (j : ℕ) (t : ℝ) : ℝ :=
  t ^ j / (j.factorial : ℝ) * chi t

def scaledProfile (chi : ContDiffBump (0 : ℝ)) (j : ℕ) (r x t : ℝ) : ℝ :=
  (r ^ j)⁻¹ * profile chi j ((t-x)*r)

lemma profile_contDiff (chi : ContDiffBump (0 : ℝ)) (j : ℕ) :
    ContDiff ℝ ∞ (profile chi j) := by
  exact ((contDiff_id.pow j).div_const (j.factorial : ℝ)).mul chi.contDiff

lemma profile_eventually_polynomial (chi : ContDiffBump (0 : ℝ)) (j : ℕ) :
    profile chi j =ᶠ[𝓝 0] fun t => t ^ j / (j.factorial : ℝ) := by
  filter_upwards [chi.eventuallyEq_one] with t ht
  simp only [profile, ht, Pi.one_apply, mul_one]

lemma profile_jet (chi : ContDiffBump (0 : ℝ)) (j k : ℕ) :
    iteratedDeriv k (profile chi j) 0 = if k = j then 1 else 0 := by
  rw [(profile_eventually_polynomial chi j).iteratedDeriv_eq k]
  rw [iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero]
  split_ifs <;> simp_all [Nat.factorial_ne_zero]

lemma scaledProfile_contDiff (chi : ContDiffBump (0 : ℝ)) (j : ℕ) (r x : ℝ) :
    ContDiff ℝ ∞ (scaledProfile chi j r x) := by
  exact contDiff_const.mul ((profile_contDiff chi j).comp
    ((contDiff_id.sub contDiff_const).mul contDiff_const))

lemma scaledProfile_eventually_polynomial (chi : ContDiffBump (0 : ℝ))
    (j : ℕ) {r : ℝ} (hr : r ≠ 0) (x : ℝ) :
    scaledProfile chi j r x =ᶠ[𝓝 x]
      fun t => (t-x) ^ j / (j.factorial : ℝ) := by
  have hc : Tendsto (fun t : ℝ => (t-x)*r) (𝓝 x) (𝓝 0) := by
    have hc0 : Continuous (fun t : ℝ => (t-x)*r) :=
      (continuous_id.sub continuous_const).mul continuous_const
    simpa using hc0.tendsto x
  have hh := hc.eventually chi.eventuallyEq_one
  filter_upwards [hh] with t ht
  simp only [scaledProfile, profile, ht, Pi.one_apply, mul_one, mul_pow]
  field_simp

/-- Every order has the exact Kronecker jet; no numerical or asymptotic jet
condition is imported. -/
theorem scaledProfile_jet (chi : ContDiffBump (0 : ℝ)) (j k : ℕ)
    {r : ℝ} (hr : r ≠ 0) (x : ℝ) :
    iteratedDeriv k (scaledProfile chi j r x) x = if k = j then 1 else 0 := by
  rw [(scaledProfile_eventually_polynomial chi j hr x).iteratedDeriv_eq k]
  have he := congrFun (iteratedDeriv_comp_sub_const k
    (fun t : ℝ => t ^ j / (j.factorial : ℝ)) x) x
  rw [he, sub_self, iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero]
  split_ifs <;> simp_all [Nat.factorial_ne_zero]

lemma scaledProfile_eventually_zero (chi : ContDiffBump (0 : ℝ)) (j : ℕ)
    (r x y : ℝ) (hsep : chi.rOut < |(y-x)*r|) :
    scaledProfile chi j r x =ᶠ[𝓝 y] 0 := by
  have hc : Continuous (fun t : ℝ => |(t-x)*r|) :=
    ((continuous_id.sub continuous_const).mul continuous_const).abs
  have hh : ∀ᶠ t in 𝓝 y, chi.rOut < |(t-x)*r| :=
    (isOpen_lt continuous_const hc).mem_nhds hsep
  filter_upwards [hh] with t ht
  have hz : chi ((t-x)*r) = 0 := chi.zero_of_le_dist (by simpa [Real.dist_eq] using ht.le)
  simp [scaledProfile, profile, hz]

lemma scale_tendsto : Tendsto scale atTop atTop := by
  change Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

/-- A different fixed point eventually has an open neighborhood on which the
literal test profile vanishes. Thus all its jets vanish, not merely its value. -/
theorem eventually_zero_germ (chi : ContDiffBump (0 : ℝ)) (j : ℕ)
    (x y : ℝ) (hy : y ≠ x) :
    ∀ᶠ n in atTop, scaledProfile chi j (scale n) x =ᶠ[𝓝 y] 0 := by
  have ha : 0 < |y-x| := abs_pos.mpr (sub_ne_zero.mpr hy)
  have hh : ∀ᶠ n in atTop, chi.rOut / |y-x| < scale n :=
    scale_tendsto.eventually (eventually_gt_atTop _)
  filter_upwards [hh] with n hn
  apply scaledProfile_eventually_zero chi j (scale n) x y
  rw [abs_mul, abs_of_pos (scale_pos n)]
  simpa only [mul_comm] using (div_lt_iff₀ ha).mp hn

/-- Finite simultaneous avoidance keeps every prescribed point and jet
attached to a single shrinking test sequence. -/
theorem eventually_finite_jets_zero (chi : ContDiffBump (0 : ℝ)) (j : ℕ)
    (x : ℝ) (s : Finset ℝ) (hs : x ∉ s) (K : ℕ) :
    ∀ᶠ n in atTop, ∀ y ∈ s, ∀ k ≤ K,
      iteratedDeriv k (scaledProfile chi j (scale n) x) y = 0 := by
  have hg : ∀ᶠ n in atTop, ∀ y ∈ s,
      scaledProfile chi j (scale n) x =ᶠ[𝓝 y] 0 := by
    rw [Filter.eventually_all_finset]
    intro y hy
    exact eventually_zero_germ chi j x y (by intro he; subst y; exact hs hy)
  filter_upwards [hg] with n hn
  intro y hy k hk
  rw [(hn y hy).iteratedDeriv_eq k]
  simp

end RhSmoothJetProfiles
#print axioms RhSmoothJetProfiles.scaledProfile_jet
#print axioms RhSmoothJetProfiles.eventually_zero_germ
#print axioms RhSmoothJetProfiles.eventually_finite_jets_zero


