import RhCoerciveSchurInverse001
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Exact finite-source covariance for a coercive complement. The one inverse below
is shared by the ENTIRE family; no source-by-source inverse is substituted.
The sources can carry signed prime-power, rank and multiplier contributions.
Instantiation with the actual arithmetic form and its gap is a separate task.
-/
noncomputable section
open scoped BigOperators
namespace RhSchurCovariance
open InnerProductSpace RhCoerciveSchurInverse
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The common inverse covariance, bilinear in its signed sources. -/
def covariance (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (b c : V) : ℝ :=
  inner ℝ b (inverse B hB c)

lemma covariance_symmetric (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsym : ∀ x y : V, B x y = B y x) (b c : V) :
    covariance B hB b c = covariance B hB c b := by
  rw [covariance, covariance, ← inverse_weak_equation B hB b,
    hsym, inverse_weak_equation]

/-- Exact aggregate expansion: all ordered mixed covariances are present. -/
theorem aggregate_covariance {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (b : ι → V) (c : κ → V) :
    covariance B hB (∑ i ∈ s, b i) (∑ j ∈ t, c j) =
      ∑ i ∈ s, ∑ j ∈ t, covariance B hB (b i) (c j) := by
  simp only [covariance, map_sum, sum_inner, inner_sum]
  exact Finset.sum_comm

/-- The source labels do not change the inverse covariance. -/
theorem regrouping_invariant {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (b : ι → V) (c : κ → V)
    (heq : ∑ i ∈ s, b i = ∑ j ∈ t, c j) :
    (∑ i ∈ s, ∑ j ∈ s, covariance B hB (b i) (b j)) =
      ∑ i ∈ t, ∑ j ∈ t, covariance B hB (c i) (c j) := by
  rw [← aggregate_covariance s s B hB b b,
    ← aggregate_covariance t t B hB c c, heq]

lemma inverse_cross_strict (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    {b : V} (hb : b ≠ 0) : 0 < covariance B hB b b := by
  apply RhZeroModeSchur.cross_payment_positive (continuousLinearMapOfBilin B) _ b
    (inverse B hB b) (inverse_equation B hB b) hb
  intro y hy
  obtain ⟨c, hc, hco⟩ := hB
  rw [continuousLinearMapOfBilin_apply]
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  exact (by positivity : 0 < c * ‖y‖ * ‖y‖).trans_le (hco y)

/-- A zero diagonal is compatible with positivity only if the TOTAL coupling vanishes. -/
theorem zero_diagonal_iff_total_coupling_zero
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsym : ∀ x y : V, B x y = B y x) (b : V) :
    (∀ y : V, 0 ≤ 2 * inner ℝ b y + B y y) ↔ b = 0 := by
  constructor
  · intro h
    by_contra hb
    have hp := inverse_cross_strict B hB hb
    have hn := (nonnegative_iff_residual B hB hsym 0 b).mp (by
      intro y
      simpa using h y)
    change 0 < inner ℝ b (inverse B hB b) at hp
    linarith
  · intro hb y
    subst b
    simpa using riesz_nonnegative B hB y

/-- An explicit optimized negative direction for nonzero total coupling. -/
theorem exact_negative_witness (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsym : ∀ x y : V, B x y = B y x) {b : V} (hb : b ≠ 0) :
    2 * inner ℝ b (-inverse B hB b) +
      B (-inverse B hB b) (-inverse B hB b) = -covariance B hB b b ∧
    2 * inner ℝ b (-inverse B hB b) +
      B (-inverse B hB b) (-inverse B hB b) < 0 := by
  have hid := completion_square B hB hsym 0 b (-inverse B hB b)
  have heq : 2 * inner ℝ b (-inverse B hB b) +
      B (-inverse B hB b) (-inverse B hB b) = -covariance B hB b b := by
    simpa [covariance] using hid
  exact ⟨heq, heq.trans_lt (neg_neg_of_pos (inverse_cross_strict B hB hb))⟩

/-- The full residual target with all signed source interactions displayed. -/
theorem finite_source_schur_iff {ι : Type*} (s : Finset ι)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsym : ∀ x y : V, B x y = B y x) (a : ℝ) (b : ι → V) :
    (∀ y : V, 0 ≤ a + 2 * inner ℝ (∑ i ∈ s, b i) y + B y y) ↔
      ∑ i ∈ s, ∑ j ∈ s, covariance B hB (b i) (b j) ≤ a := by
  rw [nonnegative_iff_residual B hB hsym a (∑ i ∈ s, b i)]
  rw [sub_nonneg]
  change covariance B hB (∑ i ∈ s, b i) (∑ i ∈ s, b i) ≤ a ↔ _
  rw [aggregate_covariance]

end RhSchurCovariance
#print axioms RhSchurCovariance.covariance_symmetric
#print axioms RhSchurCovariance.aggregate_covariance
#print axioms RhSchurCovariance.regrouping_invariant
#print axioms RhSchurCovariance.inverse_cross_strict
#print axioms RhSchurCovariance.zero_diagonal_iff_total_coupling_zero
#print axioms RhSchurCovariance.exact_negative_witness
#print axioms RhSchurCovariance.finite_source_schur_iff
