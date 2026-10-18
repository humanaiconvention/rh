import RhFourierTailLimit001
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval BigOperators

namespace RhDilationScalar

/-- Logarithmic-frequency derivative of one native multiplier. -/
def scaleDerivative (x s : ℝ) : ℝ := 4 * x * s / (s ^ 2 + x) ^ 2

def derivativePotential (x s : ℝ) : ℝ := x / (s ^ 2 + x) + 2 / s

lemma scaleDerivative_nonneg {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    0 ≤ scaleDerivative x s := by
  unfold scaleDerivative
  positivity

/-- Exact rational majorant. Its positive numerator replaces a sampled-integral bound. -/
lemma scaleDerivative_le_potential_difference {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    scaleDerivative x s ≤ derivativePotential x s - derivativePotential x (s + 2) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hs2 : s + 2 ≠ 0 := ne_of_gt (by linarith : 0 < s + 2)
  have hA : s ^ 2 + x ≠ 0 := ne_of_gt (by positivity : 0 < s ^ 2 + x)
  have hB : (s + 2) ^ 2 + x ≠ 0 := ne_of_gt (by positivity : 0 < (s + 2) ^ 2 + x)
  have he : derivativePotential x s - derivativePotential x (s + 2) - scaleDerivative x s =
      4 * ((s ^ 3 - x) ^ 2 + 4 * s ^ 5 + 4 * s ^ 4 +
        (4 * s ^ 2 + 6 * s + 3) * x ^ 2 + x ^ 3) /
        (s * (s + 2) * (s ^ 2 + x) ^ 2 * ((s + 2) ^ 2 + x)) := by
    unfold derivativePotential scaleDerivative
    field_simp
    <;> ring
  have hn : 0 ≤ 4 * ((s ^ 3 - x) ^ 2 + 4 * s ^ 5 + 4 * s ^ 4 +
        (4 * s ^ 2 + 6 * s + 3) * x ^ 2 + x ^ 3) /
        (s * (s + 2) * (s ^ 2 + x) ^ 2 * ((s + 2) ^ 2 + x)) := by
    positivity
  linarith

lemma finite_scaleDerivative_telescope {x b : ℝ} (hx : 0 ≤ x) (hb : 0 < b) (K : ℕ) :
    (∑ k ∈ Finset.range K, scaleDerivative x (b + 2 * k)) ≤
      derivativePotential x b - derivativePotential x (b + 2 * K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hs : 0 < b + 2 * (K : ℝ) := by positivity
    have hc := scaleDerivative_le_potential_difference hx hs
    rw [Finset.sum_range_succ]
    push_cast
    have he : b + 2 * ((K : ℝ) + 1) = b + 2 * K + 2 := by ring
    rw [he]
    linarith

/-- The exact uniform derivative budget, for every finite native head. -/
theorem finite_scaleDerivative_bound {x b : ℝ} (hx : 0 ≤ x) (hb : 0 < b) (K : ℕ) :
    (∑ k ∈ Finset.range K, scaleDerivative x (b + 2 * k)) ≤ 1 + 2 / b := by
  have ht := finite_scaleDerivative_telescope hx hb K
  have hp : 0 ≤ derivativePotential x (b + 2 * K) := by
    unfold derivativePotential
    positivity
  have hq : x / (b ^ 2 + x) ≤ 1 := (div_le_one (by positivity)).2 (by nlinarith)
  unfold derivativePotential at ht hp
  linarith

end RhDilationScalar
#print axioms RhDilationScalar.scaleDerivative_le_potential_difference
#print axioms RhDilationScalar.finite_scaleDerivative_bound

