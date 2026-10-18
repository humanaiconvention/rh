import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Exact real Hilbert-space Schur algebra. These declarations do not construct
an arithmetic operator, its domain, a complement inverse, or a spectral gap.
All symmetry, complement positivity, and inverse equations are explicit inputs.
-/
noncomputable section
namespace RhZeroModeSchur

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Exact completion of the square, requiring an actual solution C z = b. -/
theorem completion_square (C : F →L[ℝ] F)
    (hsym : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (a : ℝ) (b z y : F) (hz : C z = b) :
    a + 2 * inner ℝ b y + inner ℝ (C y) y =
      (a - inner ℝ b z) + inner ℝ (C (y + z)) (y + z) := by
  have hcross : inner ℝ (C y) z = inner ℝ b y := by
    rw [hsym y z, hz, real_inner_comm y b]
  simp only [map_add, inner_add_left, inner_add_right]
  rw [hz, hcross]
  ring

/-- The inverse cross-payment is nonnegative if the complement form is. -/
theorem cross_payment_nonnegative (C : F →L[ℝ] F)
    (hC : ∀ y, 0 ≤ inner ℝ (C y) y) (b z : F) (hz : C z = b) :
    0 ≤ inner ℝ b z := by
  rw [← hz]
  exact hC z

/-- A nonzero coupling costs strictly positive energy on a positive complement. -/
theorem cross_payment_positive (C : F →L[ℝ] F)
    (hC : ∀ y, y ≠ 0 → 0 < inner ℝ (C y) y)
    (b z : F) (hz : C z = b) (hb : b ≠ 0) :
    0 < inner ℝ b z := by
  have hzne : z ≠ 0 := by
    intro hzero
    apply hb
    rw [← hz, hzero, map_zero]
  rw [← hz]
  exact hC z hzne

/-- All complement directions are nonnegative exactly when the Schur residual is.
No positivity of that residual is supplied here. -/
theorem nonnegative_iff_residual (C : F →L[ℝ] F)
    (hsym : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (hC : ∀ y, 0 ≤ inner ℝ (C y) y)
    (a : ℝ) (b z : F) (hz : C z = b) :
    (∀ y : F, 0 ≤ a + 2 * inner ℝ b y + inner ℝ (C y) y) ↔
      0 ≤ a - inner ℝ b z := by
  constructor
  · intro hall
    have h := hall (-z)
    rw [completion_square C hsym a b z (-z) hz] at h
    simpa using h
  · intro hres y
    rw [completion_square C hsym a b z y hz]
    exact add_nonneg hres (hC (y + z))

/-- Operator-valued inverse notation, with the required inverse equation explicit. -/
def residual {E : Type*} (a : E → ℝ) (B : E → F) (R : F →L[ℝ] F)
    (p : E) : ℝ :=
  a p - inner ℝ (B p) (R (B p))

theorem whole_space_nonnegative_iff {E : Type*}
    (C R : F →L[ℝ] F)
    (hsym : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (hC : ∀ y, 0 ≤ inner ℝ (C y) y)
    (a : E → ℝ) (B : E → F) (hright : ∀ p, C (R (B p)) = B p) :
    (∀ p y, 0 ≤ a p + 2 * inner ℝ (B p) y + inner ℝ (C y) y) ↔
      ∀ p, 0 ≤ residual a B R p := by
  constructor
  · intro h p
    exact (nonnegative_iff_residual C hsym hC (a p) (B p) (R (B p))
      (hright p)).mp (h p)
  · intro h p
    exact (nonnegative_iff_residual C hsym hC (a p) (B p) (R (B p))
      (hright p)).mpr (h p)

/-- The exact residual subtracts, rather than adds, the complement payment. -/
theorem residual_le_diagonal {E : Type*}
    (C R : F →L[ℝ] F) (hC : ∀ y, 0 ≤ inner ℝ (C y) y)
    (a : E → ℝ) (B : E → F) (hright : ∀ p, C (R (B p)) = B p)
    (p : E) : residual a B R p ≤ a p := by
  have h := cross_payment_nonnegative C hC (B p) (R (B p)) (hright p)
  unfold residual
  linarith

/-- The matrix [[0,h],[h,1]] has a zero diagonal null-axis for every h. -/
def toyForm (h x y : ℝ) : ℝ := 2 * h * x * y + y ^ 2

lemma toy_null_axis (h : ℝ) : toyForm h 1 0 = 0 := by
  simp [toyForm]

/-- Even the derivative along the former null axis is identically zero. -/
theorem toy_null_axis_derivative (h : ℝ) :
    HasDerivAt (fun r : ℝ => toyForm r 1 0) 0 h := by
  simpa [toyForm] using (hasDerivAt_const h (0 : ℝ))

lemma toy_exact_residual (h : ℝ) : toyForm h 1 (-h) = -(h ^ 2) := by
  unfold toyForm
  ring

/-- Nevertheless every nonzero outward coupling makes a negative direction. -/
theorem toy_negative_direction {h : ℝ} (hh : h ≠ 0) :
    toyForm h 1 (-h) < 0 := by
  rw [toy_exact_residual]
  nlinarith [sq_pos_of_ne_zero hh]

/-- A positive diagonal of second order can still be smaller than the payment. -/
def positiveDiagonalForm (h x y : ℝ) : ℝ :=
  (h ^ 2 / 2) * x ^ 2 + toyForm h x y

theorem positive_diagonal_but_negative_residual {h : ℝ} (hh : h ≠ 0) :
    0 < positiveDiagonalForm h 1 0 ∧ positiveDiagonalForm h 1 (-h) < 0 := by
  have hs : 0 < h ^ 2 := sq_pos_of_ne_zero hh
  constructor
  · simp only [positiveDiagonalForm, toyForm]
    nlinarith
  · rw [positiveDiagonalForm, toy_exact_residual]
    nlinarith

end RhZeroModeSchur
#print axioms RhZeroModeSchur.completion_square
#print axioms RhZeroModeSchur.cross_payment_nonnegative
#print axioms RhZeroModeSchur.cross_payment_positive
#print axioms RhZeroModeSchur.nonnegative_iff_residual
#print axioms RhZeroModeSchur.whole_space_nonnegative_iff
#print axioms RhZeroModeSchur.residual_le_diagonal
#print axioms RhZeroModeSchur.toy_null_axis_derivative
#print axioms RhZeroModeSchur.toy_negative_direction
#print axioms RhZeroModeSchur.positive_diagonal_but_negative_residual
