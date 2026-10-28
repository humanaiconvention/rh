import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic

/-!
Finite counting core for RH-COUNTING-AUDIT-001.

This module proves finite ordered counting and polynomial degree exhaustion.
It contains no Jensen limit, entire-function, zeta, or RH assertion.  The
analytic existence of the cell witnesses is outside this module.
-/

namespace RhCountingAudit

open Finset

/-- Count the first `n` entries at or below a threshold, with multiplicity
of indices.  For an injective root list this is the distinct-root count. -/
noncomputable def prefixCount {α : Type*} [LinearOrder α]
    (n : ℕ) (r : ℕ → α) (t : α) : ℕ := by
  classical
  exact ((range n).filter (fun i => r i ≤ t)).card

/-- Local strict interleaving alone bounds the finite prefix discrepancy.
There are `n + 1` root entries and `n` separator entries. -/
theorem interleaved_prefix_bounds {α : Type*} [LinearOrder α]
    (n : ℕ) (r c : ℕ → α)
    (h : ∀ i < n, r i < c i ∧ c i < r (i + 1)) (t : α) :
    prefixCount n c t ≤ prefixCount (n + 1) r t ∧
      prefixCount (n + 1) r t ≤ prefixCount n c t + 1 := by
  classical
  let A := (range (n + 1)).filter (fun i => r i ≤ t)
  let C := (range n).filter (fun i => c i ≤ t)
  change C.card ≤ A.card ∧ A.card ≤ C.card + 1
  have hCA : C ⊆ A := by
    intro i hi
    obtain ⟨hin, hit⟩ := mem_filter.mp hi
    have hi' : i < n := mem_range.mp hin
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_lt hi'), (h i hi').1.le.trans hit⟩
  have hAC : A ⊆ insert 0 (C.image Nat.succ) := by
    intro i hi
    obtain ⟨hin, hit⟩ := mem_filter.mp hi
    have hi' : i < n + 1 := mem_range.mp hin
    cases i with
    | zero => exact mem_insert_self _ _
    | succ j =>
      have hj : j < n := Nat.lt_of_succ_lt_succ hi'
      apply mem_insert_of_mem
      exact mem_image.mpr ⟨j,
        mem_filter.mpr ⟨mem_range.mpr hj, (h j hj).2.le.trans hit⟩, rfl⟩
  exact ⟨card_le_card hCA,
    (card_le_card hAC).trans ((card_insert_le _ _).trans
      (Nat.add_le_add_right (card_image_le) 1))⟩

/-- Two lists occupying the same complete cells have prefix counts differing
by at most one.  No height limit is taken here. -/
theorem common_cells_prefix_discrepancy {α : Type*} [LinearOrder α]
    (n : ℕ) (p b c : ℕ → α)
    (hp : ∀ i < n, p i < c i ∧ c i < p (i + 1))
    (hb : ∀ i < n, b i < c i ∧ c i < b (i + 1)) (t : α) :
    prefixCount (n + 1) p t ≤ prefixCount (n + 1) b t + 1 ∧
      prefixCount (n + 1) b t ≤ prefixCount (n + 1) p t + 1 := by
  obtain ⟨hpl, hpu⟩ := interleaved_prefix_bounds n p c hp t
  obtain ⟨hbl, hbu⟩ := interleaved_prefix_bounds n b c hb t
  exact ⟨hpu.trans (Nat.add_le_add_right hbl 1),
    hbu.trans (Nat.add_le_add_right hpl 1)⟩

/-- A degree budget turns `d` distinct real root witnesses into the complete
multiset of real roots, so no spare roots or multiplicities remain.  This
uses mathlib's existing degree-exhaustion theorem. -/
theorem roots_eq_of_distinct_witnesses (P : Polynomial ℝ) (hP : P ≠ 0)
    (d : ℕ) (x : Fin d → ℝ) (hx : Function.Injective x)
    (hz : ∀ i, P.eval (x i) = 0) (hdeg : P.natDegree ≤ d) :
    P.roots = (univ.image x).val := by
  classical
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro a ha
    obtain ⟨i, _, rfl⟩ := mem_image.mp ha
    exact hz i
  · simpa only [card_image_of_injective _ hx, card_univ, Fintype.card_fin] using hdeg
  · exact hP

/-- Witnesses in disjoint ordered open cells are distinct.  Consequently,
once their number exhausts the degree budget, they are all real roots with
multiplicity one.  The endpoints can be arbitrary increasing separators. -/
theorem roots_eq_of_ordered_cell_witnesses (P : Polynomial ℝ) (hP : P ≠ 0)
    (d : ℕ) (b : ℕ → ℝ) (hb : Monotone b) (x : Fin d → ℝ)
    (hcell : ∀ i, b i.val < x i ∧ x i < b (i.val + 1))
    (hz : ∀ i, P.eval (x i) = 0) (hdeg : P.natDegree ≤ d) :
    P.roots = (univ.image x).val := by
  have hx : StrictMono x := by
    intro i j hij
    have hij' : i.val + 1 ≤ j.val := by exact Nat.succ_le_of_lt hij
    exact (hcell i).2.trans_le (hb hij') |>.trans (hcell j).1
  exact roots_eq_of_distinct_witnesses P hP d x hx.injective hz hdeg

end RhCountingAudit

#print axioms RhCountingAudit.interleaved_prefix_bounds
#print axioms RhCountingAudit.common_cells_prefix_discrepancy
#print axioms RhCountingAudit.roots_eq_of_distinct_witnesses
#print axioms RhCountingAudit.roots_eq_of_ordered_cell_witnesses
