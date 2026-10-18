import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import RhZeroModeSchur001
import Mathlib.Tactic.Positivity

/-!
Quantitative real form-space complement inversion. The inverse is constructed
by Lax-Milgram from a coercivity gap, and is then substituted into the accepted
Schur algebra. No arithmetic form, form-domain identification, or spectral gap
for the actual kernel is instantiated in this module.
-/
noncomputable section
namespace RhCoerciveSchurInverse

open InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The diagonal perturbation budget preserves a quantitative coercivity gap. -/
theorem perturbed_isCoercive (B₀ D : V →L[ℝ] V →L[ℝ] ℝ)
    {tau eta : ℝ} (hlt : eta < tau)
    (hbase : ∀ q : V, tau * ‖q‖ ^ 2 ≤ B₀ q q)
    (hpert : ∀ q : V, |D q q| ≤ eta * ‖q‖ ^ 2) :
    IsCoercive (B₀ + D) := by
  refine ⟨tau - eta, sub_pos.mpr hlt, ?_⟩
  intro q
  have hb := hbase q
  have hd := (abs_le.mp (hpert q)).1
  simp only [add_apply]
  nlinarith

/-- Actual inverse of the Riesz operator supplied by Lax-Milgram. -/
def inverse (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) : V →L[ℝ] V :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap

/-- The constructed inverse solves the operator equation for every right side. -/
theorem inverse_equation (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (b : V) :
    continuousLinearMapOfBilin B (inverse B hB b) = b := by
  change hB.continuousLinearEquivOfBilin
    (hB.continuousLinearEquivOfBilin.symm b) = b
  exact hB.continuousLinearEquivOfBilin.apply_symm_apply b

/-- The weak inverse equation does not assume an unknown solution exists. -/
theorem inverse_weak_equation (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (b q : V) :
    B (inverse B hB b) q = inner ℝ b q := by
  rw [← continuousLinearMapOfBilin_apply, inverse_equation]

lemma riesz_symmetric (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hsym : ∀ x y : V, B x y = B y x) :
    ∀ x y : V, inner ℝ (continuousLinearMapOfBilin B x) y =
      inner ℝ x (continuousLinearMapOfBilin B y) := by
  intro x y
  calc
    inner ℝ (continuousLinearMapOfBilin B x) y = B x y :=
      continuousLinearMapOfBilin_apply B x y
    _ = B y x := hsym x y
    _ = inner ℝ (continuousLinearMapOfBilin B y) x :=
      (continuousLinearMapOfBilin_apply B y x).symm
    _ = inner ℝ x (continuousLinearMapOfBilin B y) :=
      (real_inner_comm (continuousLinearMapOfBilin B y) x).symm

lemma riesz_nonnegative (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) :
    ∀ y : V, 0 ≤ inner ℝ (continuousLinearMapOfBilin B y) y := by
  intro y
  obtain ⟨c, hc, hco⟩ := hB
  rw [continuousLinearMapOfBilin_apply]
  exact (by positivity : 0 ≤ c * ‖y‖ * ‖y‖).trans (hco y)

/-- Exact square completion with a constructed inverse, not an inverse premise. -/
theorem completion_square (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsym : ∀ x y : V, B x y = B y x) (a : ℝ) (b y : V) :
    a + 2 * inner ℝ b y + B y y =
      (a - inner ℝ b (inverse B hB b)) +
        B (y + inverse B hB b) (y + inverse B hB b) := by
  have h := RhZeroModeSchur.completion_square (continuousLinearMapOfBilin B)
    (riesz_symmetric B hsym) a b (inverse B hB b) y (inverse_equation B hB b)
  simpa only [continuousLinearMapOfBilin_apply] using h

/-- The residual subtracts an actual nonnegative inverse energy payment. -/
theorem cross_payment_nonnegative (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (b : V) : 0 ≤ inner ℝ b (inverse B hB b) := by
  exact RhZeroModeSchur.cross_payment_nonnegative (continuousLinearMapOfBilin B)
    (riesz_nonnegative B hB) b (inverse B hB b) (inverse_equation B hB b)

/-- Quantitative upper payment bound for a declared positive coercivity constant. -/
theorem cross_payment_le (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    {c : ℝ} (hc : 0 < c) (hco : ∀ q : V, c * ‖q‖ ^ 2 ≤ B q q) (b : V) :
    inner ℝ b (inverse B hB b) ≤ ‖b‖ ^ 2 / c := by
  let z : V := inverse B hB b
  have hcz : c * ‖z‖ ^ 2 ≤ inner ℝ b z := by
    calc
      c * ‖z‖ ^ 2 ≤ B z z := hco z
      _ = inner ℝ b z := inverse_weak_equation B hB b z
  have hcs : inner ℝ b z ≤ ‖b‖ * ‖z‖ := real_inner_le_norm b z
  have hzbound : c * ‖z‖ ≤ ‖b‖ := by
    by_cases hz : ‖z‖ = 0
    · simp only [hz, mul_zero]
      exact norm_nonneg b
    · have hzp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hzp).mp
      nlinarith
  change inner ℝ b z ≤ ‖b‖ ^ 2 / c
  apply (le_div_iff₀ hc).2
  calc
    inner ℝ b z * c ≤ (‖b‖ * ‖z‖) * c := mul_le_mul_of_nonneg_right hcs hc.le
    _ = ‖b‖ * (c * ‖z‖) := by ring
    _ ≤ ‖b‖ * ‖b‖ := mul_le_mul_of_nonneg_left hzbound (norm_nonneg b)
    _ = ‖b‖ ^ 2 := by ring

/-- Whole complement nonnegativity is exactly the Schur residual sign condition. -/
theorem nonnegative_iff_residual (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsym : ∀ x y : V, B x y = B y x) (a : ℝ) (b : V) :
    (∀ y : V, 0 ≤ a + 2 * inner ℝ b y + B y y) ↔
      0 ≤ a - inner ℝ b (inverse B hB b) := by
  have h := RhZeroModeSchur.nonnegative_iff_residual (continuousLinearMapOfBilin B)
    (riesz_symmetric B hsym) (riesz_nonnegative B hB)
    a b (inverse B hB b) (inverse_equation B hB b)
  simpa only [continuousLinearMapOfBilin_apply] using h

/-- Every family member uses the same constructed complement inverse. -/
theorem whole_space_nonnegative_iff {E : Type*}
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsym : ∀ x y : V, B x y = B y x) (a : E → ℝ) (b : E → V) :
    (∀ p y, 0 ≤ a p + 2 * inner ℝ (b p) y + B y y) ↔
      ∀ p, 0 ≤ a p - inner ℝ (b p) (inverse B hB (b p)) := by
  constructor
  · intro h p
    exact (nonnegative_iff_residual B hB hsym (a p) (b p)).mp (h p)
  · intro h p
    exact (nonnegative_iff_residual B hB hsym (a p) (b p)).mpr (h p)

/-- Complete perturbation consequence: inverse existence and payment from the gap. -/
theorem quantitative_inverse_and_payment (B₀ D : V →L[ℝ] V →L[ℝ] ℝ)
    {tau eta : ℝ} (hlt : eta < tau)
    (hbase : ∀ q : V, tau * ‖q‖ ^ 2 ≤ B₀ q q)
    (hpert : ∀ q : V, |D q q| ≤ eta * ‖q‖ ^ 2) :
    ∃ R : V →L[ℝ] V,
      (∀ b : V, continuousLinearMapOfBilin (B₀ + D) (R b) = b) ∧
      (∀ b : V, 0 ≤ inner ℝ b (R b) ∧
        inner ℝ b (R b) ≤ ‖b‖ ^ 2 / (tau - eta)) := by
  let hB : IsCoercive (B₀ + D) := perturbed_isCoercive B₀ D hlt hbase hpert
  refine ⟨inverse (B₀ + D) hB, inverse_equation (B₀ + D) hB, ?_⟩
  intro b
  refine ⟨cross_payment_nonnegative (B₀ + D) hB b, ?_⟩
  apply cross_payment_le (B₀ + D) hB (sub_pos.mpr hlt)
  intro q
  have hb := hbase q
  have hd := (abs_le.mp (hpert q)).1
  simp only [add_apply]
  nlinarith

/-- Quantitative hypotheses construct the inverse used by the exact Schur theorem. -/
theorem perturbed_nonnegative_iff (B₀ D : V →L[ℝ] V →L[ℝ] ℝ)
    {tau eta : ℝ} (hlt : eta < tau)
    (hbase : ∀ q : V, tau * ‖q‖ ^ 2 ≤ B₀ q q)
    (hpert : ∀ q : V, |D q q| ≤ eta * ‖q‖ ^ 2)
    (hsym₀ : ∀ x y : V, B₀ x y = B₀ y x)
    (hsymD : ∀ x y : V, D x y = D y x) (a : ℝ) (b : V) :
    let hB : IsCoercive (B₀ + D) := perturbed_isCoercive B₀ D hlt hbase hpert
    (∀ y : V, 0 ≤ a + 2 * inner ℝ b y + (B₀ + D) y y) ↔
      0 ≤ a - inner ℝ b (inverse (B₀ + D) hB b) := by
  dsimp only
  apply nonnegative_iff_residual
  intro x y
  simp only [add_apply]
  rw [hsym₀ x y, hsymD x y]

end RhCoerciveSchurInverse
#print axioms RhCoerciveSchurInverse.perturbed_isCoercive
#print axioms RhCoerciveSchurInverse.inverse_equation
#print axioms RhCoerciveSchurInverse.inverse_weak_equation
#print axioms RhCoerciveSchurInverse.completion_square
#print axioms RhCoerciveSchurInverse.cross_payment_nonnegative
#print axioms RhCoerciveSchurInverse.cross_payment_le
#print axioms RhCoerciveSchurInverse.nonnegative_iff_residual
#print axioms RhCoerciveSchurInverse.whole_space_nonnegative_iff
#print axioms RhCoerciveSchurInverse.quantitative_inverse_and_payment
#print axioms RhCoerciveSchurInverse.perturbed_nonnegative_iff
