module

public import Mathlib

/-!
# Obstructions to the unchanged one-half substitution

The specified local factor and architecture parameters are documented
in README.md. All definitions and proofs are contained in this file.
Scope: the particular exponents, moment range, and principal Euler factor
audited there. These are not impossibility theorems for RH, analytic
continuation, conditional products, or other parameter choices.

Target toolchain: Lean 4.35.0.
Mathlib commit: 6015dbbfc399f4548bafd46f9560ff61595fd328.
Compile from this repository with "lake env lean Obstructions.lean".

Every theorem has an explicit proof. The final axiom-printing commands
expose the dependency boundary. No additional mathematical assumption
is added. Prime-ideal harmonic divergence is proved below for every
number field using ideal-count asymptotics and exact ideal factorization.

IMPORTANT DOMAIN: the Euler lower bound is proved for
  1/2 < re(x) <= 2/3,
not for every re(x) <= 2/3. At the boundary 1/2 the source gives a
different obstruction involving a nonconvergent local geometric series.

"Diverges to positive infinity" is encoded by unbounded finite subsums.
For a nonnegative family this is precisely divergence of its unordered
sum to positive infinity, without any choice of prime enumeration.
The file never uses Lean's totalized tsum as an infinity value.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

/-! ## Supporting number-field theorem

Summable prime-ideal reciprocals would give summable positive prime
powers. Summability of finite products then controls every ideal
reciprocal through an injective exact factorization map. Tannery's
theorem and ideal-count asymptotics contradict that conclusion.
-/

namespace PrimeIdealDivergence

open scoped Topology nonZeroDivisors
open Filter UniqueFactorizationMonoid


variable (K : Type*) [Field K] [NumberField K]

abbrev NZIdeal := (Ideal (NumberField.RingOfIntegers K))⁰
abbrev PrimeIdeal := {I : Ideal (NumberField.RingOfIntegers K) // Prime I}

def normI (I : Ideal (NumberField.RingOfIntegers K)) : ℝ :=
  (Ideal.absNorm I : ℝ)

lemma normI_pos (I : NZIdeal K) : 0 < normI K I.val := by
  unfold normI
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I

lemma ideal_reciprocals_not_summable :
    ¬ Summable (fun I : NZIdeal K => 1 / normI K I.val) := by
  classical
  intro hsum
  let f : ℝ → NZIdeal K → ℝ :=
    fun x I => if normI K I.val ≤ x then 1 / x else 0
  have hpoint (I : NZIdeal K) :
      Tendsto (fun x => f x I) atTop (𝓝 0) := by
    apply (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).congr'
    filter_upwards [eventually_ge_atTop (normI K I.val)] with x hx
    simp [f, hx, one_div]
  have hbound : ∀ᶠ x : ℝ in atTop, ∀ I : NZIdeal K,
      ‖f x I‖ ≤ 1 / normI K I.val := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx I
    by_cases hIx : normI K I.val ≤ x
    · have hx0 : 0 < x := by linarith
      simp only [f, ite_eq_left hIx, Real.norm_eq_abs,
        abs_of_nonneg (one_div_nonneg.mpr hx0.le)]
      exact one_div_le_one_div_of_le (normI_pos K I) hIx
    · simp only [f, ite_eq_right hIx, norm_zero]
      exact one_div_nonneg.mpr (normI_pos K I).le
  have hz := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  simp only [tsum_zero] at hz
  have hcount : Tendsto
      (fun x : ℝ => (Nat.card {I : NZIdeal K // normI K I.val ≤ x} : ℝ) / x)
      atTop (𝓝 0) := by
    apply hz.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 ≤ x := by linarith
    let : Finite {I : NZIdeal K // normI K I.val ≤ x} := by
      simp only [normI, ← Nat.le_floor_iff hx0]
      exact Ideal.finite_setOfPred_absNorm_le₀ ⌊x⌋₊
    let := Fintype.ofFinite {I : NZIdeal K // normI K I.val ≤ x}
    have hsub := tsum_subtype {I : NZIdeal K | normI K I.val ≤ x}
      (fun _ => (1 : ℝ) / x)
    simp only [Set.indicator, Set.mem_ofPred_eq] at hsub
    rw [show (∑' I : NZIdeal K, f x I) =
        ∑' _ : {I : NZIdeal K // normI K I.val ≤ x}, (1 : ℝ) / x from hsub.symm]
    simp [Nat.card_eq_fintype_card, nsmul_eq_mul, div_eq_mul_inv]
  have hactual : Tendsto
      (fun x : ℝ => (Nat.card {I : NZIdeal K // normI K I.val ≤ x} : ℝ) / x)
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
    simpa only [NZIdeal, normI, NumberField.dedekindZeta_residue] using
      NumberField.Ideal.tendsto_norm_le_div_atTop₀ K
  have heq := tendsto_nhds_unique hcount hactual
  exact (NumberField.dedekindZeta_residue_ne_zero K) heq.symm


def rho (I : Ideal (NumberField.RingOfIntegers K)) : ℝ := by
  classical
  exact if Prime I then 1 / normI K I else 0

def tags (I : NZIdeal K) :
    Finset (Ideal (NumberField.RingOfIntegers K) × ℕ) := by
  classical
  exact (normalizedFactors I.val).toFinset.image
    (fun p => (p, (normalizedFactors I.val).count p - 1))

lemma tags_prod (I : NZIdeal K) :
    (∏ t ∈ tags K I, t.1 ^ (t.2 + 1)) = I.val := by
  classical
  unfold tags
  rw [Finset.prod_image]
  · calc
      (∏ p ∈ (normalizedFactors I.val).toFinset,
          p ^ ((normalizedFactors I.val).count p - 1 + 1)) =
        ∏ p ∈ (normalizedFactors I.val).toFinset,
          p ^ (normalizedFactors I.val).count p := by
            apply Finset.prod_congr rfl
            intro p hp
            rw [Nat.sub_add_cancel]
            exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
      _ = (normalizedFactors I.val).prod :=
        (Finset.prod_multiset_count _).symm
      _ = I.val := by
        rw [prod_normalizedFactors_eq
          (mem_nonZeroDivisors_iff_ne_zero.mp I.property)]
        simp
  · intro p hp q hq hpq
    exact congrArg Prod.fst hpq

lemma tags_injective : Function.Injective (tags K) := by
  intro I J h
  apply Subtype.ext
  calc
    I.val = ∏ t ∈ tags K I, t.1 ^ (t.2 + 1) := (tags_prod K I).symm
    _ = ∏ t ∈ tags K J, t.1 ^ (t.2 + 1) := by rw [h]
    _ = J.val := tags_prod K J

lemma tags_prime (I : NZIdeal K)
    (t : Ideal (NumberField.RingOfIntegers K) × ℕ)
    (ht : t ∈ tags K I) : Prime t.1 := by
  classical
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
  exact prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)

lemma tags_weight (I : NZIdeal K) :
    (∏ t ∈ tags K I, rho K t.1 ^ (t.2 + 1)) = 1 / normI K I.val := by
  classical
  have hn := congrArg (fun J => (Ideal.absNorm J : ℝ)) (tags_prod K I)
  simp only [map_prod, map_pow, Nat.cast_prod, Nat.cast_pow] at hn
  calc
    (∏ t ∈ tags K I, rho K t.1 ^ (t.2 + 1)) =
      ∏ t ∈ tags K I, (1 / normI K t.1) ^ (t.2 + 1) := by
        apply Finset.prod_congr rfl
        intro t ht
        simp [rho, tags_prime K I t ht]
    _ = 1 / normI K I.val := by
      simpa only [normI, one_div, inv_pow, Finset.prod_inv_distrib] using
        congrArg Inv.inv hn


lemma rho_range (I : Ideal (NumberField.RingOfIntegers K)) :
    0 ≤ rho K I ∧ rho K I ≤ 1 / 2 := by
  classical
  by_cases hp : Prime I
  · have h0 : Ideal.absNorm I ≠ 0 := by
      intro h
      exact hp.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
    have h1 : Ideal.absNorm I ≠ 1 := by
      intro h
      exact hp.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
    have hn : 2 ≤ Ideal.absNorm I := by omega
    have hnr : (2 : ℝ) ≤ normI K I := by
      unfold normI
      exact_mod_cast hn
    have hpos : 0 < normI K I := by linarith
    simp only [rho, ite_eq_left hp]
    constructor
    · positivity
    · apply (div_le_iff₀ hpos).2
      linarith
  · simp [rho, hp]

lemma prime_reciprocals_not_summable :
    ¬ Summable (fun p : PrimeIdeal K => 1 / normI K p.val) := by
  classical
  intro hprime
  have hrho : Summable (rho K) := by
    have h := (summable_subtype_iff_indicator
      (s := {I : Ideal (NumberField.RingOfIntegers K) | Prime I})
      (f := fun I => 1 / normI K I)).mp hprime
    exact h.congr (fun I => by
      by_cases hI : Prime I <;> simp [rho, hI])
  let a : (Ideal (NumberField.RingOfIntegers K) × ℕ) → ℝ :=
    fun t => rho K t.1 ^ (t.2 + 1)
  have ha0 (t) : 0 ≤ a t := pow_nonneg (rho_range K t.1).1 _
  have hgeo (I : Ideal (NumberField.RingOfIntegers K)) :
      Summable (fun n : ℕ => a (I, n)) := by
    have hlt : rho K I < 1 := by
      have := (rho_range K I).2
      linarith
    exact (summable_geometric_of_lt_one (rho_range K I).1 hlt).comp_injective
      Nat.succ_injective
  have hsumBound (I : Ideal (NumberField.RingOfIntegers K)) :
      (∑' n : ℕ, a (I, n)) ≤ 2 * rho K I := by
    have hlt : rho K I < 1 := by
      have := (rho_range K I).2
      linarith
    have hden : 0 < 1 - rho K I := by linarith
    have hformula : (∑' n : ℕ, a (I, n)) =
        rho K I / (1 - rho K I) := by
      simp only [a, pow_succ]
      rw [tsum_mul_right, tsum_geometric_of_lt_one (rho_range K I).1 hlt]
      ring
    rw [hformula]
    apply (div_le_iff₀ hden).2
    have h0 := (rho_range K I).1
    have hhalf := (rho_range K I).2
    nlinarith [mul_nonneg h0 (show 0 ≤ 1 - 2 * rho K I by linarith)]
  have ha : Summable a := by
    apply (summable_prod_of_nonneg ha0).mpr
    refine ⟨hgeo, ?_⟩
    exact (hrho.mul_left 2).of_nonneg_of_le
      (fun I => tsum_nonneg (fun n => ha0 (I, n))) hsumBound
  have hproducts : Summable
      (fun s : Finset (Ideal (NumberField.RingOfIntegers K) × ℕ) =>
        ∏ t ∈ s, a t) :=
    summable_finsetProd_of_summable_nonneg ha0 ha
  have hideals : Summable (fun I : NZIdeal K => 1 / normI K I.val) := by
    have h := hproducts.comp_injective (tags_injective K)
    exact h.congr (fun I => tags_weight K I)
  exact ideal_reciprocals_not_summable K hideals


lemma prime_tail_reciprocals_not_summable
    (S : Set (PrimeIdeal K)) (hS : S.Finite) :
    ¬ Summable (fun p : {p : PrimeIdeal K // p ∉ S ∧ 64 ≤ normI K p.val} =>
      1 / normI K p.val.val) := by
  classical
  intro htail
  let good : Set (PrimeIdeal K) := {p | p ∉ S ∧ 64 ≤ normI K p.val}
  let f : PrimeIdeal K → ℝ := fun p => 1 / normI K p.val
  have hsmall : {p : PrimeIdeal K | normI K p.val < 64}.Finite := by
    have hbase := Ideal.finite_setOfPred_absNorm_le
      (S := NumberField.RingOfIntegers K) 64
    have hpre := Set.Finite.preimage
      (f := (Subtype.val : PrimeIdeal K → Ideal (NumberField.RingOfIntegers K)))
      Subtype.val_injective.injOn hbase
    apply hpre.subset
    intro p hp
    change Ideal.absNorm p.val ≤ 64
    have hp' : (Ideal.absNorm p.val : ℝ) ≤ 64 := le_of_lt hp
    exact_mod_cast hp'
  have hbad : goodᶜ.Finite := by
    apply (hS.union hsmall).subset
    intro p hp
    by_cases hs : p ∈ S
    · exact Or.inl hs
    · exact Or.inr (lt_of_not_ge (fun h => hp ⟨hs, h⟩))
  have ht : Summable (good.indicator f) :=
    summable_subtype_iff_indicator.mp htail
  have hb : Summable (goodᶜ.indicator f) :=
    summable_subtype_iff_indicator.mp (hbad.summable f)
  apply prime_reciprocals_not_summable K
  exact (ht.add hb).congr (fun p => by
    by_cases hp : p ∈ good <;> simp [hp, f])

lemma prime_tail_reciprocals_unbounded
    (S : Set (PrimeIdeal K)) (hS : S.Finite) :
    ∀ B : ℝ, ∃ s : Finset {p : PrimeIdeal K // p ∉ S ∧ 64 ≤ normI K p.val},
      B < ∑ p ∈ s, 1 / normI K p.val.val := by
  classical
  intro B
  by_contra! h
  apply prime_tail_reciprocals_not_summable K S hS
  exact summable_of_sum_le (fun p => by
    have hp : 0 < normI K p.val.val := by linarith [p.property.2]
    exact one_div_nonneg.mpr hp.le) h


end PrimeIdealDivergence

namespace RHArchitectureObstructions

/-! ## 1. Physical exponents and moment parameter -/

-- These definitions encode the source's supplied geometry and moment
-- interval. They do not reprove the analytic low-side or moment estimates.

def lx : ℝ := 17 / 48
def amplifierExponent : ℝ := 1 / 8
def heightExponent : ℝ := 13 / 16
def lowExponent : ℝ := lx / 2 + amplifierExponent / 12
def signalExponent (σ : ℝ) : ℝ :=
  lx / 2 + σ - 1 + heightExponent / 6

theorem lowExponent_eq : lowExponent = (3 : ℝ) / 16 := by
  norm_num [lowExponent, lx, amplifierExponent]

theorem signalExponent_eq (σ : ℝ) :
    signalExponent σ = σ - 11 / 16 := by
  unfold signalExponent lx heightExponent
  ring

theorem physical_deficit (σ : ℝ) :
    lowExponent - signalExponent σ = 7 / 8 - σ := by
  rw [lowExponent_eq, signalExponent_eq]
  ring

theorem physical_deficit_at_half :
    lowExponent - signalExponent (1 / 2) = (3 : ℝ) / 8 := by
  rw [physical_deficit]
  norm_num

theorem unchanged_low_estimate_misses_half :
    ¬ lowExponent ≤ signalExponent (1 / 2) := by
  rw [lowExponent_eq, signalExponent_eq]
  norm_num

def dynamicKappa (β : ℝ) : ℝ := 2 * β - 1
def admissibleMomentParameter (κ : ℝ) : Prop :=
  (3 : ℝ) / 4 ≤ κ ∧ κ ≤ 1

theorem dynamicKappa_at_half : dynamicKappa (1 / 2) = 0 := by
  norm_num [dynamicKappa]

theorem dynamicKappa_at_seven_eighths :
    dynamicKappa (7 / 8) = (3 : ℝ) / 4 := by
  norm_num [dynamicKappa]

theorem dynamicKappa_admissible_iff (β : ℝ) :
    admissibleMomentParameter (dynamicKappa β) ↔
      (7 : ℝ) / 8 ≤ β ∧ β ≤ 1 := by
  unfold admissibleMomentParameter dynamicKappa
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    constructor <;> linarith

theorem half_outside_proved_moment_range :
    ¬ admissibleMomentParameter (dynamicKappa (1 / 2)) := by
  norm_num [admissibleMomentParameter, dynamicKappa]

theorem below_seven_eighths_outside_proved_moment_range
    (β : ℝ) (hβ : β < 7 / 8) :
    ¬ admissibleMomentParameter (dynamicKappa β) := by
  rw [dynamicKappa_admissible_iff]
  rintro ⟨hlo, _⟩
  linarith

/-! ## 2. Exact local Euler factor and defect decomposition

The phases are arbitrary unit complex numbers; every height is retained
in x. No randomness or independence of the phases is assumed.
Analytic uses of division require nonzero denominators.
-/

def localD (Q : ℝ) (x eta : ℂ) : ℂ :=
  eta * (Q : ℂ) ^ (-x)

def localR (Q : ℝ) (x alpha : ℂ) : ℂ :=
  alpha ^ 2 * (Q : ℂ) ^ (3 - 6 * x)

-- The argument called alpha in localR is the source's *combined* unit
-- phase a_p, not the underlying cubic coefficient also denoted alpha(p).

def eulerFactor (v : ℝ) (D R : ℂ) : ℂ :=
  ((1 - v ^ 2 : ℝ) : ℂ) *
    ((v : ℂ) / (1 - D) + ((1 - v : ℝ) : ℂ) / (1 - R))

def principalEulerFactor (Q : ℝ) (x eta alpha : ℂ) : ℂ :=
  eulerFactor (1 / Q) (localD Q x eta) (localR Q x alpha)

theorem euler_defect_identity (v : ℝ) (D R : ℂ)
    (hD : 1 - D ≠ 0) (hR : 1 - R ≠ 0) :
    eulerFactor v D R - 1 =
      (((1 - v ^ 2) * (1 - v) : ℝ) : ℂ) * R / (1 - R) +
      (((1 - v ^ 2) * v : ℝ) : ℂ) * D / (1 - D) -
      (v : ℂ) ^ 2 := by
  unfold eulerFactor
  push_cast
  field_simp [hD, hR]; ring

theorem localD_norm (Q : ℝ) (x eta : ℂ)
    (hQ : 0 < Q) (heta : ‖eta‖ = 1) :
    ‖localD Q x eta‖ = Q ^ (-x.re) := by
  unfold localD
  rw [norm_mul, heta, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp

theorem localR_norm (Q : ℝ) (x alpha : ℂ)
    (hQ : 0 < Q) (halpha : ‖alpha‖ = 1) :
    ‖localR Q x alpha‖ = Q ^ (3 - 6 * x.re) := by
  unfold localR
  rw [norm_mul, norm_pow, halpha, one_pow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  congr 1
  norm_num [Complex.mul_re]

theorem localR_norm_at_half (Q : ℝ) (x alpha : ℂ)
    (hQ : 0 < Q) (hx : x.re = 1 / 2) (halpha : ‖alpha‖ = 1) :
    ‖localR Q x alpha‖ = 1 := by
  rw [localR_norm Q x alpha hQ halpha, hx]
  norm_num

theorem boundary_geometric_terms_have_unit_norm
    (Q : ℝ) (x alpha : ℂ) (n : ℕ)
    (hQ : 0 < Q) (hx : x.re = 1 / 2) (halpha : ‖alpha‖ = 1) :
    ‖localR Q x alpha ^ n‖ = 1 := by
  rw [norm_pow, localR_norm_at_half Q x alpha hQ hx halpha, one_pow]

/-! ### Elementary complex estimate

The coarser coefficient 7/8 for (1-v^2)(1-v) still gives the source's
1/4 lower bound. These are local norm estimates for normal convergence,
not a magnitude bound on the finite signed arithmetic mass.
-/

theorem normalized_euler_defect_lower_bound
    (v : ℝ) (D R : ℂ)
    (hv0 : 0 ≤ v) (hv64 : v ≤ 1 / 64)
    (hDsmall : ‖D‖ ≤ 1 / 8)
    (hvR : v ≤ ‖R‖) (hRsmall : ‖R‖ < 1) :
    (1 : ℝ) / 4 * ‖R‖ ≤ ‖eulerFactor v D R - 1‖ := by
  have hv1 : v ≤ 1 := by linarith
  have hvSq : v ^ 2 ≤ v := by
    nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hv1)]
  have hA0 : 0 ≤ (1 - v ^ 2) * (1 - v) :=
    mul_nonneg (by nlinarith) (by linarith)
  have hAlo : (7 : ℝ) / 8 ≤ (1 - v ^ 2) * (1 - v) := by
    nlinarith [mul_nonneg hv0 (sq_nonneg v)]
  have hB0 : 0 ≤ (1 - v ^ 2) * v :=
    mul_nonneg (by nlinarith) hv0
  have hBle : (1 - v ^ 2) * v ≤ v := by
    nlinarith [mul_nonneg hv0 (sq_nonneg v)]
  have hDne : (1 : ℂ) - D ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have : ‖D‖ = 1 := by rw [← h]; norm_num
    linarith
  have hRne : (1 : ℂ) - R ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have : ‖R‖ = 1 := by rw [← h]; norm_num
    linarith
  have hDden : 0 < ‖(1 : ℂ) - D‖ := norm_pos_iff.mpr hDne
  have hRden : 0 < ‖(1 : ℂ) - R‖ := norm_pos_iff.mpr hRne
  have hDtriangle : (1 : ℝ) ≤ ‖(1 : ℂ) - D‖ + ‖D‖ := by
    calc
      1 = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖((1 : ℂ) - D) + D‖ := by congr 1; ring
      _ ≤ ‖(1 : ℂ) - D‖ + ‖D‖ := norm_add_le _ _
  have hDdenLo : (7 : ℝ) / 8 ≤ ‖(1 : ℂ) - D‖ := by
    linarith
  have hRdenHi : ‖(1 : ℂ) - R‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) R
    norm_num at h
    linarith
  let T : ℂ :=
    (((1 - v ^ 2) * (1 - v) : ℝ) : ℂ) * R / (1 - R)
  let U : ℂ :=
    (((1 - v ^ 2) * v : ℝ) : ℂ) * D / (1 - D)
  have hTnorm :
      ‖T‖ = ((1 - v ^ 2) * (1 - v)) * ‖R‖ / ‖(1 : ℂ) - R‖ := by
    dsimp [T]
    rw [norm_div, norm_mul, Complex.norm_of_nonneg hA0]
  have hUnorm :
      ‖U‖ = ((1 - v ^ 2) * v) * ‖D‖ / ‖(1 : ℂ) - D‖ := by
    dsimp [U]
    rw [norm_div, norm_mul, Complex.norm_of_nonneg hB0]
  have hTprod :
      ‖T‖ * ‖(1 : ℂ) - R‖ = ((1 - v ^ 2) * (1 - v)) * ‖R‖ := by
    rw [hTnorm, div_mul_cancel₀ _ (ne_of_gt hRden)]
  have hUprod :
      ‖U‖ * ‖(1 : ℂ) - D‖ = ((1 - v ^ 2) * v) * ‖D‖ := by
    rw [hUnorm, div_mul_cancel₀ _ (ne_of_gt hDden)]
  have hTlo : (7 : ℝ) / 8 * ‖R‖ ≤ 2 * ‖T‖ := by
    have h1 := mul_le_mul_of_nonneg_right hAlo (norm_nonneg R)
    have h2 := mul_le_mul_of_nonneg_left hRdenHi (norm_nonneg T)
    nlinarith [hTprod]
  have hUhi : ‖U‖ ≤ v / 7 := by
    have h1 := mul_le_mul_of_nonneg_left hDdenLo (norm_nonneg U)
    have h2 := mul_le_mul_of_nonneg_right hBle (norm_nonneg D)
    have h3 := mul_le_mul_of_nonneg_left hDsmall hv0
    nlinarith [hUprod]
  have hdefect : eulerFactor v D R - 1 = T + U - (v : ℂ) ^ 2 := by
    exact euler_defect_identity v D R hDne hRne
  have hTidentity :
      T = ((eulerFactor v D R - 1) - U) + (v : ℂ) ^ 2 := by
    rw [hdefect]
    ring
  have hvNorm : ‖(v : ℂ) ^ 2‖ = v ^ 2 := by
    rw [norm_pow, Complex.norm_of_nonneg hv0]
  have hreverse :
      ‖T‖ ≤ ‖eulerFactor v D R - 1‖ + ‖U‖ + v ^ 2 := by
    calc
      ‖T‖ = ‖((eulerFactor v D R - 1) - U) + (v : ℂ) ^ 2‖ :=
        congrArg norm hTidentity
      _ ≤ ‖(eulerFactor v D R - 1) - U‖ + ‖(v : ℂ) ^ 2‖ :=
        norm_add_le _ _
      _ ≤ ‖eulerFactor v D R - 1‖ + ‖U‖ + v ^ 2 := by
        rw [hvNorm]
        have h := norm_sub_le (eulerFactor v D R - 1) U
        linarith
  have hvSqSmall : v ^ 2 ≤ ‖R‖ / 64 := by
    have h := mul_nonneg hv0 (sub_nonneg.mpr hv64)
    nlinarith
  nlinarith [norm_nonneg R]

/-! ### Actual prime-norm and complex-height substitution -/

theorem norm_range_in_strip (Q σ : ℝ)
    (hQ : 64 ≤ Q) (hlo : 1 / 2 < σ) (hhi : σ ≤ 2 / 3) :
    0 ≤ 1 / Q ∧ 1 / Q ≤ 1 / 64 ∧
      Q ^ (-σ) ≤ 1 / 8 ∧
      1 / Q ≤ Q ^ (3 - 6 * σ) ∧ Q ^ (3 - 6 * σ) < 1 := by
  have hQpos : 0 < Q := by linarith
  have hQone : 1 < Q := by linarith
  have hv0 : (0 : ℝ) ≤ 1 / Q := by positivity
  have hv64 : (1 : ℝ) / Q ≤ 1 / 64 := by
    apply (div_le_iff₀ hQpos).2
    linarith
  have hDsq : (Q ^ (-σ)) ^ (2 : ℕ) ≤ 1 / Q := by
    calc
      (Q ^ (-σ)) ^ (2 : ℕ) = Q ^ ((-σ) * 2) := by
        rw [Real.rpow_mul hQpos.le, Real.rpow_two]
      _ ≤ Q ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hQone.le (by linarith)
      _ = 1 / Q := by rw [Real.rpow_neg_one, one_div]
  have hDsmall : Q ^ (-σ) ≤ 1 / 8 := by
    nlinarith [sq_nonneg (Q ^ (-σ) - 1 / 8)]
  have hRlo : (1 : ℝ) / Q ≤ Q ^ (3 - 6 * σ) := by
    calc
      1 / Q = Q ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ Q ^ (3 - 6 * σ) :=
        Real.rpow_le_rpow_of_exponent_le hQone.le (by linarith)
  have hRhi : Q ^ (3 - 6 * σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hQone (by linarith)
  exact ⟨hv0, hv64, hDsmall, hRlo, hRhi⟩

theorem principal_euler_defect_lower_bound
    (Q : ℝ) (x eta alpha : ℂ)
    (hQ : 64 ≤ Q) (hlo : 1 / 2 < x.re) (hhi : x.re ≤ 2 / 3)
    (heta : ‖eta‖ = 1) (halpha : ‖alpha‖ = 1) :
    (1 : ℝ) / 4 * Q ^ (3 - 6 * x.re) ≤
      ‖principalEulerFactor Q x eta alpha - 1‖ := by
  have hQpos : 0 < Q := by linarith
  obtain ⟨hv0, hv64, hDsmall, hRlo, hRhi⟩ :=
    norm_range_in_strip Q x.re hQ hlo hhi
  have hDn := localD_norm Q x eta hQpos heta
  have hRn := localR_norm Q x alpha hQpos halpha
  have h :=
    normalized_euler_defect_lower_bound (1 / Q)
      (localD Q x eta) (localR Q x alpha)
      hv0 hv64 (by rwa [hDn]) (by rwa [hRn]) (by rwa [hRn])
  simpa only [principalEulerFactor, hRn] using h

/-! ## 3. Prime-ideal divergence and its exact comparison

CyclotomicField 3 ℚ is the Eisenstein field Q(omega).
Indices are actual nonzero prime ideals of its ring of integers.
The inert-prime subsum alone would not prove divergence at exponent one.
-/

abbrev EisensteinField := CyclotomicField 3 ℚ
abbrev EisensteinIntegers := NumberField.RingOfIntegers EisensteinField
-- Monoid-prime ideals are precisely the nonzero ring-prime ideals here.
abbrev EisensteinPrime := PrimeIdealDivergence.PrimeIdeal EisensteinField

def primeNorm (p : EisensteinPrime) : ℝ :=
  (Ideal.absNorm p.val : ℝ)

def GoodPrime (S : Set EisensteinPrime) :=
  {p : EisensteinPrime // p ∉ S ∧ 64 ≤ primeNorm p}

def UnboundedFiniteSubsums {ι : Type*} (f : ι → ℝ) : Prop :=
  ∀ B : ℝ, ∃ s : Finset ι, B < ∑ i ∈ s, f i

/-- Prime-ideal harmonic divergence with all fixed exclusions retained.
The supporting argument above proves this without zero-location
hypotheses. The cutoff 64 remains explicit in the indexing type.
-/
theorem eisenstein_prime_reciprocal_unbounded
    (S : Set EisensteinPrime) (hS : S.Finite) :
    UnboundedFiniteSubsums
      (fun p : GoodPrime S => 1 / primeNorm p.val) := by
  exact PrimeIdealDivergence.prime_tail_reciprocals_unbounded
    EisensteinField S hS

/-- Modular divergence transfer, with the prime-divergence input exposed.
The following unconditional theorem discharges that hypothesis.
-/
theorem principal_defects_unbounded_of_prime_reciprocals
    (S : Set EisensteinPrime)
    (hprime : UnboundedFiniteSubsums
      (fun p : GoodPrime S => 1 / primeNorm p.val))
    (x : ℂ) (hlo : 1 / 2 < x.re) (hhi : x.re ≤ 2 / 3)
    (eta alpha : GoodPrime S → ℂ)
    (heta : ∀ p, ‖eta p‖ = 1) (halpha : ∀ p, ‖alpha p‖ = 1) :
    UnboundedFiniteSubsums (fun p : GoodPrime S =>
      ‖principalEulerFactor (primeNorm p.val) x (eta p) (alpha p) - 1‖) := by
  classical
  intro B
  obtain ⟨s, hs⟩ := hprime (4 * B)
  have hpoint (p : GoodPrime S) :
      1 / primeNorm p.val ≤
        4 * ‖principalEulerFactor (primeNorm p.val) x (eta p) (alpha p) - 1‖ := by
    have hlocal := principal_euler_defect_lower_bound
      (primeNorm p.val) x (eta p) (alpha p)
      p.property.2 hlo hhi (heta p) (halpha p)
    obtain ⟨_, _, _, hpower, _⟩ :=
      norm_range_in_strip (primeNorm p.val) x.re p.property.2 hlo hhi
    linarith
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ s) => hpoint p)
  rw [← Finset.mul_sum] at hsum
  refine ⟨s, ?_⟩
  linarith

/-- The source's divergence on the proved open strip.
Every dependency is proved in this file or imported from pinned mathlib.
-/
theorem principal_prime_defects_unbounded
    (S : Set EisensteinPrime) (hS : S.Finite)
    (x : ℂ) (hlo : 1 / 2 < x.re) (hhi : x.re ≤ 2 / 3)
    (eta alpha : GoodPrime S → ℂ)
    (heta : ∀ p, ‖eta p‖ = 1) (halpha : ∀ p, ‖alpha p‖ = 1) :
    UnboundedFiniteSubsums (fun p : GoodPrime S =>
      ‖principalEulerFactor (primeNorm p.val) x (eta p) (alpha p) - 1‖) :=
  principal_defects_unbounded_of_prime_reciprocals S
    (eisenstein_prime_reciprocal_unbounded S hS)
    x hlo hhi eta alpha heta halpha

/-- Explicit non-summability of the norm-defect tail. -/
theorem principal_prime_defects_not_summable
    (S : Set EisensteinPrime) (hS : S.Finite)
    (x : ℂ) (hlo : 1 / 2 < x.re) (hhi : x.re ≤ 2 / 3)
    (eta alpha : GoodPrime S → ℂ)
    (heta : ∀ p, ‖eta p‖ = 1) (halpha : ∀ p, ‖alpha p‖ = 1) :
    ¬ Summable (fun p : GoodPrime S =>
      ‖principalEulerFactor (primeNorm p.val) x (eta p) (alpha p) - 1‖) := by
  classical
  intro hsum
  obtain ⟨s, hs⟩ := principal_prime_defects_unbounded S hS x hlo hhi
    eta alpha heta halpha
    (∑' p : GoodPrime S,
      ‖principalEulerFactor (primeNorm p.val) x (eta p) (alpha p) - 1‖)
  have hle := hsum.sum_le_tsum s (fun p _ => norm_nonneg _)
  exact (not_lt_of_ge hle) hs

set_option maxHeartbeats 5000000 in
/-- Non-summability over every prime outside S, including the finitely
many prime ideals of norm below 64. Summability of a full family would
imply summability of the injectively indexed tail, contradicting the
preceding theorem. No small-prime term is discarded from this statement.
-/
theorem principal_all_prime_defects_not_summable
    (S : Set EisensteinPrime) (hS : S.Finite)
    (x : ℂ) (hlo : 1 / 2 < x.re) (hhi : x.re ≤ 2 / 3)
    (eta alpha : {p : EisensteinPrime // p ∉ S} → ℂ)
    (heta : ∀ p, ‖eta p‖ = 1) (halpha : ∀ p, ‖alpha p‖ = 1) :
    ¬ Summable (fun p : {p : EisensteinPrime // p ∉ S} =>
      ‖principalEulerFactor (primeNorm p.val) x (eta p) (alpha p) - 1‖) := by
  classical
  let inclusion : GoodPrime S → {p : EisensteinPrime // p ∉ S} :=
    fun p => ⟨p.val, p.property.1⟩
  have hinj : Function.Injective inclusion := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun z : {p : EisensteinPrime // p ∉ S} => z.val) h
  let etaTail : GoodPrime S → ℂ := fun p => eta (inclusion p)
  let alphaTail : GoodPrime S → ℂ := fun p => alpha (inclusion p)
  have hetaTail : ∀ p : GoodPrime S, ‖etaTail p‖ = 1 :=
    fun p => heta (inclusion p)
  have halphaTail : ∀ p : GoodPrime S, ‖alphaTail p‖ = 1 :=
    fun p => halpha (inclusion p)
  have hno := principal_prime_defects_not_summable S hS x hlo hhi
    etaTail alphaTail hetaTail halphaTail
  intro hsum
  have hcomp := hsum.comp_injective (i := inclusion) hinj
  apply hno
  exact hcomp

/-! ## Dependency audit

All displayed declarations must depend only on the standard Lean/mathlib
logical axioms: propext, Classical.choice, and Quot.sound.
The verification log records the compiler's actual output.
-/

#print axioms physical_deficit_at_half
#print axioms eisenstein_prime_reciprocal_unbounded
#print axioms half_outside_proved_moment_range
#print axioms principal_euler_defect_lower_bound
#print axioms principal_defects_unbounded_of_prime_reciprocals
#print axioms principal_prime_defects_unbounded
#print axioms principal_all_prime_defects_not_summable

end RHArchitectureObstructions
