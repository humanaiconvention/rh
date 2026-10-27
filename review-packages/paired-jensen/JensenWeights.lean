import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Proposed finite Jensen weights: static draft, NOT COMPILED

This file is a first pilot only. No Lean process has been run for this round.
It uses the zero extension and exact finite-product constants of
`SIGNED-JENSEN-EXTRACTION-001/THEOREM.md`, equation (6).
It does not assert the signed-measure integral theorem.
-/

noncomputable section

open scoped BigOperators

namespace SignedJensenPrep

def rawWeight (d j : ℕ) : ℝ :=
  ∏ v ∈ Finset.range j, (1 - (v : ℝ) / (d : ℝ))

/-- The prescribed finite falling weight, extended by zero above degree `d`. -/
def weight (d j : ℕ) : ℝ :=
  if j ≤ d then rawWeight d j else 0

theorem rawWeight_zero (d : ℕ) : rawWeight d 0 = 1 := by
  simp [rawWeight]

theorem rawWeight_succ (d j : ℕ) :
    rawWeight d (j + 1) = rawWeight d j * (1 - (j : ℝ) / (d : ℝ)) := by
  exact Finset.prod_range_succ _ _

/-- Simultaneous induction avoids any appeal to infinite products or series. -/
theorem rawWeight_bounds (d : ℕ) (hd : 1 ≤ d) :
    ∀ j : ℕ, j ≤ d →
      0 ≤ rawWeight d j ∧ rawWeight d j ≤ 1 ∧
        1 - rawWeight d j ≤ (j : ℝ) * ((j : ℝ) - 1) / (2 * (d : ℝ)) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    simpa using (Nat.cast_lt (α := ℝ)).2 (lt_of_lt_of_le Nat.zero_lt_one hd)
  intro j
  induction j with
  | zero =>
      intro _
      norm_num [rawWeight]
  | succ j ih =>
      intro hj
      have hjd : j ≤ d := le_trans (Nat.le_succ j) hj
      obtain ⟨hp0, hp1, hpdef⟩ := ih hjd
      have hjreal : (j : ℝ) ≤ (d : ℝ) := (Nat.cast_le (α := ℝ)).2 hjd
      have hfrac0 : (0 : ℝ) ≤ (j : ℝ) / (d : ℝ) :=
        div_nonneg (Nat.cast_nonneg j) hdpos.le
      have hfrac1 : (j : ℝ) / (d : ℝ) ≤ 1 :=
        (div_le_one hdpos).2 hjreal
      have hfactor0 : (0 : ℝ) ≤ 1 - (j : ℝ) / (d : ℝ) := sub_nonneg.2 hfrac1
      have hfactor1 : 1 - (j : ℝ) / (d : ℝ) ≤ (1 : ℝ) := sub_le_self _ hfrac0
      rw [rawWeight_succ]
      refine ⟨mul_nonneg hp0 hfactor0, ?_, ?_⟩
      · calc
          rawWeight d j * (1 - (j : ℝ) / (d : ℝ)) ≤
              1 * (1 - (j : ℝ) / (d : ℝ)) :=
            mul_le_mul_of_nonneg_right hp1 hfactor0
          _ ≤ 1 := by simpa using hfactor1
      · have hprod : rawWeight d j * ((j : ℝ) / (d : ℝ)) ≤
            (j : ℝ) / (d : ℝ) := by
          simpa using mul_le_mul_of_nonneg_right hp1 hfrac0
        have hstep :
            1 - rawWeight d j * (1 - (j : ℝ) / (d : ℝ)) ≤
              (1 - rawWeight d j) + (j : ℝ) / (d : ℝ) := by
          nlinarith only [hprod]
        have hid :
            (j : ℝ) * ((j : ℝ) - 1) / (2 * (d : ℝ)) + (j : ℝ) / (d : ℝ) =
              ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1) /
                (2 * (d : ℝ)) := by
          simp only [Nat.cast_add, Nat.cast_one]
          field_simp [ne_of_gt hdpos]
          <;> ring
        calc
          1 - rawWeight d j * (1 - (j : ℝ) / (d : ℝ)) ≤
              (1 - rawWeight d j) + (j : ℝ) / (d : ℝ) := hstep
          _ ≤ (j : ℝ) * ((j : ℝ) - 1) / (2 * (d : ℝ)) +
              (j : ℝ) / (d : ℝ) := by linarith only [hpdef]
          _ = _ := hid

theorem weight_zero (d : ℕ) : weight d 0 = 1 := by
  simp [weight, rawWeight]

theorem weight_one (d : ℕ) (hd : 1 ≤ d) : weight d 1 = 1 := by
  simp [weight, hd, rawWeight]

theorem weight_eq_zero_of_lt {d j : ℕ} (h : d < j) : weight d j = 0 := by
  simp [weight, not_le_of_gt h]

/-- The exact finite coefficient discrepancy, including all `j > d`. -/
theorem weight_bounds (d j : ℕ) (hd : 1 ≤ d) :
    0 ≤ weight d j ∧ weight d j ≤ 1 ∧
      1 - weight d j ≤ (j : ℝ) * ((j : ℝ) - 1) / (2 * (d : ℝ)) := by
  by_cases hj : j ≤ d
  · simpa [weight, hj] using rawWeight_bounds d hd j hj
  · have hdpos : (0 : ℝ) < (d : ℝ) := by
      simpa using (Nat.cast_lt (α := ℝ)).2 (lt_of_lt_of_le Nat.zero_lt_one hd)
    have hdreal : (1 : ℝ) ≤ (d : ℝ) := by
      simpa using (Nat.cast_le (α := ℝ)).2 hd
    have hjreal : (d : ℝ) + 1 ≤ (j : ℝ) := by
      simpa only [Nat.cast_succ] using
        (Nat.cast_le (α := ℝ)).2 (Nat.succ_le_of_lt (lt_of_not_ge hj))
    have hgap : (0 : ℝ) ≤ ((j : ℝ) - (d : ℝ) - 1) * ((j : ℝ) + (d : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    have hdd : (0 : ℝ) ≤ ((d : ℝ) - 1) * (d : ℝ) :=
      mul_nonneg (sub_nonneg.2 hdreal) hdpos.le
    have hproduct : 2 * (d : ℝ) ≤ (j : ℝ) * ((j : ℝ) - 1) := by
      nlinarith only [hgap, hdd]
    have hdef : (1 : ℝ) ≤ (j : ℝ) * ((j : ℝ) - 1) / (2 * (d : ℝ)) :=
      (le_div_iff₀ (mul_pos (by norm_num) hdpos)).2 (by simpa using hproduct)
    simpa [weight, hj] using (show (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 ∧
        1 - (0 : ℝ) ≤ (j : ℝ) * ((j : ℝ) - 1) / (2 * (d : ℝ)) from
      ⟨le_rfl, zero_le_one, by simpa using hdef⟩)

/-- Sharp second coefficient, with `d = 1` handled by the zero extension. -/
theorem weight_two (d : ℕ) (hd : 1 ≤ d) :
    weight d 2 = 1 - 1 / (d : ℝ) := by
  by_cases hd2 : 2 ≤ d
  · simp [weight, hd2, rawWeight, Finset.prod_range_succ]
  · have hd1 : d = 1 :=
      Nat.le_antisymm (Nat.le_of_lt_succ (lt_of_not_ge hd2)) hd
    subst d
    norm_num [weight]

end SignedJensenPrep

#print axioms SignedJensenPrep.weight_zero
#print axioms SignedJensenPrep.weight_one
#print axioms SignedJensenPrep.weight_eq_zero_of_lt
#print axioms SignedJensenPrep.weight_bounds
#print axioms SignedJensenPrep.weight_two
