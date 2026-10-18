import RhAllPrimeKernel001
import RhFinitePrimitiveEndpoint001

set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RhAllPrime
open RhAnchored

/-- Every anchor companion vanishes at and below its exact support threshold. -/
lemma hinge_vanish_threshold {R L t u : ℝ} (hR : 0≤R) (hL : 2*R≤L)
    (ht : t∈interval R) (hu : u∈interval R) : hingeKernel L t u=0 := by
  have htR : |t|≤R := abs_le.mpr ht
  have huR : |u|≤R := abs_le.mpr hu
  have htu : |t-u|≤2*R := by
    have h : |t-u|≤|t|+|u| := by
      simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le t 0 u)
    linarith
  have hL0 : 0≤L := by linarith
  have hd : max (|t-u|-L) 0=0 := max_eq_right (by linarith)
  have hl : max (|t|-L) 0=0 := max_eq_right (by linarith)
  have hr : max (|-u|-L) 0=0 := max_eq_right (by rw [abs_neg];linarith)
  have hz : max (|0|-L) 0=0 := max_eq_right (by simpa using neg_nonpos.mpr hL0)
  unfold hingeKernel anchoredKernel
  dsimp only
  rw [hd,hl,hr,hz]
  ring

lemma log_above_radius_cutoff (R : ℝ) {n : ℕ} (hn : 0<n)
    (hcut : radiusCutoff R<n) : 2*R<Real.log (n:ℝ) := by
  have hnR : Real.exp (2*R)<(n:ℝ) :=
    (Nat.floor_lt (Real.exp_pos (2*R)).le).mp hcut
  exact (Real.lt_log_iff_exp_lt (by exact_mod_cast hn)).2 hnR

/-- Exact cutoff compatibility; no estimate or discarded nonzero tail is involved. -/
theorem cutoff_stability {R : ℝ} (hR : 0≤R) {M N : ℕ} (hMN : M≤N)
    (hMissing : ∀n∈Finset.Icc 2 N,M<n→2*R≤Real.log (n:ℝ))
    {t u : ℝ} (ht : t∈interval R) (hu : u∈interval R) :
    completeKernel M t u=completeKernel N t u := by
  unfold completeKernel
  congr 1
  unfold arithmeticKernel
  have hsub : Finset.Icc 2 M⊆Finset.Icc 2 N := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1,hn.2.trans hMN⟩
  apply Finset.sum_subset hsub
  intro n hn hnot
  have h2 : 2≤n := (Finset.mem_Icc.mp hn).1
  have hM : M<n := by
    by_contra h
    apply hnot
    exact Finset.mem_Icc.mpr ⟨h2,Nat.le_of_not_gt h⟩
  rw [hinge_vanish_threshold hR (hMissing n hn hM) ht hu,mul_zero]

lemma radiusCutoff_mono : Monotone radiusCutoff := by
  intro R S hRS
  apply Nat.floor_mono
  exact Real.exp_le_exp.mpr (by linarith)

theorem radius_cutoff_stability {R : ℝ} (hR : 0≤R) (N : ℕ)
    (hN : radiusCutoff R≤N) {t u : ℝ} (ht : t∈interval R) (hu : u∈interval R) :
    radiusKernel R t u=completeKernel N t u := by
  apply cutoff_stability hR hN _ ht hu
  intro n hn hcut
  exact (log_above_radius_cutoff R (by have h2:2≤n:=(Finset.mem_Icc.mp hn).1;omega) hcut).le

/-- All radius members are exact restrictions of every larger-radius member. -/
theorem radius_restriction {R S : ℝ} (hR : 0≤R) (hRS : R≤S)
    {t u : ℝ} (ht : t∈interval R) (hu : u∈interval R) :
    radiusKernel R t u=radiusKernel S t u :=
  radius_cutoff_stability hR (radiusCutoff S) (radiusCutoff_mono hRS) ht hu

/-- A convenient exact finite representative whenever the next integer threshold is not crossed. -/
theorem radius_eq_complete_of_next_threshold {R : ℝ} (hR : 0≤R) (M : ℕ) (hM : 1≤M)
    (hNext : 2*R≤Real.log ((M+1:ℕ):ℝ))
    {t u : ℝ} (ht : t∈interval R) (hu : u∈interval R) :
    radiusKernel R t u=completeKernel M t u := by
  by_cases hcut : radiusCutoff R≤M
  · exact radius_cutoff_stability hR M hcut ht hu
  · symm
    apply cutoff_stability hR (Nat.le_of_lt (Nat.lt_of_not_ge hcut)) _ ht hu
    intro n hn hMn
    have hcast : ((M+1:ℕ):ℝ)≤(n:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hMn)
    have hpos : (0:ℝ)<((M+1:ℕ):ℝ) := by positivity
    exact hNext.trans (Real.log_le_log hpos hcast)

theorem radius_first_prime_window {R : ℝ} (hR : 0≤R) (hA : R≤schurEndpoint)
    {t u : ℝ} (ht : t∈interval R) (hu : u∈interval R) :
    radiusKernel R t u=fullKernel archConstant firstPrimeWeight firstPrimeLog t u := by
  rw [radius_eq_complete_of_next_threshold hR 2 (by norm_num) _ ht hu,complete_two]
  change 2*R≤Real.log 3
  change R≤Real.log 3/2 at hA
  linarith

/-- Prime4 is the next threshold: the two-hinge window ends at log4/2. -/
theorem radius_prime_three_window {R : ℝ} (hR : 0≤R) (hFour : 2*R≤Real.log 4)
    {t u : ℝ} (ht : t∈interval R) (hu : u∈interval R) :
    radiusKernel R t u=completeKernel 2 t u+
      (Real.log 3/Real.sqrt 3)*hingeKernel (Real.log 3) t u := by
  rw [radius_eq_complete_of_next_threshold hR 3 (by norm_num) _ ht hu,complete_three]
  exact hFour

lemma endpoint_radius_two {t u : ℝ} (ht : t∈interval schurEndpoint) (hu : u∈interval schurEndpoint) :
    radiusKernel schurEndpoint t u=fullKernel archConstant firstPrimeWeight firstPrimeLog t u :=
  radius_first_prime_window schurEndpoint_geometry.1.le le_rfl ht hu
end RhAllPrime
#print axioms RhAllPrime.hinge_vanish_threshold
#print axioms RhAllPrime.cutoff_stability
#print axioms RhAllPrime.radius_restriction
#print axioms RhAllPrime.radius_first_prime_window
#print axioms RhAllPrime.radius_prime_three_window
#print axioms RhAllPrime.endpoint_radius_two

