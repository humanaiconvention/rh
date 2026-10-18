import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact zero-diagonal cross-coupling obstruction. This is bilinear algebra,
not an assertion that the native arithmetic total flux is nonzero. -/
noncomputable section
namespace RhZeroDiagonalPairing
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A nonzero TOTAL cross term at a zero diagonal gives a literal negative
witness. There is no first-derivative argument and no smallness assumption. -/
theorem negative_witness_exact (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (p g : V) (hp : B p p = 0)
    (hb : B p g ≠ 0) :
    B ((-(B g g + 1) / (2 * B p g)) • p + g)
      ((-(B g g + 1) / (2 * B p g)) • p + g) = -1 := by
  have he (c : ℝ) : B (c • p + g) (c • p + g) =
      c ^ 2 * B p p + c * B p g + c * B g p + B g g := by
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [he, hp, hsym g p]
  field_simp
  <;> ring

/-- Positivity forces exact vanishing, not merely a small cross term. -/
theorem positive_zero_forces_cross_zero (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hpos : ∀ x, 0 ≤ B x x)
    (p : V) (hp : B p p = 0) : ∀ g : V, B p g = 0 := by
  intro g
  by_contra hb
  have hn := negative_witness_exact B hsym p g hp hb
  have hh := hpos ((-(B g g + 1) / (2 * B p g)) • p + g)
  rw [hn] at hh
  norm_num at hh

end RhZeroDiagonalPairing
#print axioms RhZeroDiagonalPairing.negative_witness_exact
#print axioms RhZeroDiagonalPairing.positive_zero_forces_cross_zero
