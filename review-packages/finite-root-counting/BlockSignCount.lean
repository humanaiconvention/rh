import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Finite disjoint sign witnesses and nonuniform block counts

Strict sign changes construct the root witnesses by IVT. Disjoint open
intervals make them distinct, and the polynomial degree budget exhausts
the roots including multiplicities. Block counts are then consequences,
not input assumptions. There is no RH or entire-function assertion.
-/

noncomputable section

namespace BlockSignCount

open Set Finset

/-- A root count retaining multiplicity, with classical membership decisions. -/
noncomputable def rootCountIn (P : Polynomial ℝ) (U : Set ℝ) : ℕ := by
  classical
  exact (P.roots.filter (fun x => x ∈ U)).card

/-- The number of sign-witness intervals assigned a given block label. -/
noncomputable def labelCount {ι κ : Type*} [Fintype ι]
    (label : ι → κ) (j : κ) : ℕ := by
  classical
  exact ((univ : Finset ι).filter (fun i => label i = j)).card

private theorem positive_of_error_margin (p f E : ℝ)
    (herr : |p - f| ≤ E) (hmargin : E < f) : 0 < p := by
  have hlow : -E + f ≤ p := (le_sub_iff_add_le).mp (abs_le.mp herr).1
  have hpos : 0 < -E + f := by
    simpa only [sub_eq_add_neg, add_comm] using (sub_pos.mpr hmargin)
  exact hpos.trans_le hlow

private theorem negative_of_error_margin (p f E : ℝ)
    (herr : |p - f| ≤ E) (hmargin : f < -E) : p < 0 := by
  have hupp : p ≤ E + f := (sub_le_iff_le_add).mp (abs_le.mp herr).2
  have hneg : E + f < 0 := calc
    E + f = f + E := add_comm E f
    _ < -E + E := add_lt_add_left hmargin E
    _ = 0 := neg_add_cancel E
  exact hupp.trans_lt hneg

/-- Arbitrarily indexed disjoint strict sign changes construct and exhaust
all real roots. Witness intervals can share endpoints, and no fixed number
of witnesses in a larger reference cell is required. -/
theorem roots_of_disjoint_sign_changes {ι : Type*} [Fintype ι]
    (P : Polynomial ℝ) (hP : P ≠ 0) (a b : ι → ℝ)
    (hab : ∀ i, a i < b i)
    (hdisj : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hsign : ∀ i, (P.eval (a i) < 0 ∧ 0 < P.eval (b i)) ∨
      (P.eval (b i) < 0 ∧ 0 < P.eval (a i)))
    (hdegree : P.natDegree ≤ Fintype.card ι) :
    ∃ x : ι → ℝ,
      (∀ i, x i ∈ Ioo (a i) (b i) ∧ P.eval (x i) = 0) ∧
      Function.Injective x ∧
      P.roots = (Finset.univ.image x).val ∧
      P.natDegree = Fintype.card ι := by
  classical
  have hex (i : ι) : ∃ x ∈ Ioo (a i) (b i), P.eval x = 0 := by
    rcases hsign i with h | h
    · exact intermediate_value_Ioo (hab i).le P.continuousOn ⟨h.1, h.2⟩
    · exact intermediate_value_Ioo' (hab i).le P.continuousOn ⟨h.1, h.2⟩
  let x : ι → ℝ := fun i => Classical.choose (hex i)
  have hx (i : ι) : x i ∈ Ioo (a i) (b i) ∧ P.eval (x i) = 0 :=
    Classical.choose_spec (hex i)
  have hinj : Function.Injective x := by
    intro i j heq
    by_contra hne
    have hj : x i ∈ Ioo (a j) (b j) := by rw [heq]; exact (hx j).1
    exact Set.disjoint_left.mp (hdisj hne) (hx i).1 hj
  have hroots : P.roots = (Finset.univ.image x).val := by
    apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    · intro z hz
      obtain ⟨i, _, rfl⟩ := mem_image.mp hz
      exact (hx i).2
    · simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ] using hdegree
    · exact hP
  have hcard : P.roots.card = Fintype.card ι := by
    rw [hroots]
    exact (Finset.card_image_of_injective _ hinj).trans (Finset.card_univ)
  have hdegree' : P.natDegree = Fintype.card ι :=
    le_antisymm hdegree (hcard ▸ P.card_roots')
  exact ⟨x, hx, hinj, hroots, hdegree'⟩

/-- Endpoint error bounds and strict margins of an arbitrary approximant
produce the actual opposite signs, then construct and exhaust the roots.
The errors are only finite pointwise bounds; no analytic/global premise
or conclusion is formalized here. Nonnegativity of the errors already
follows from their absolute-error bounds. -/
theorem roots_of_robust_margins {ι : Type*} [Fintype ι]
    (P : Polynomial ℝ) (hP : P ≠ 0) (a b : ι → ℝ)
    (hab : ∀ i, a i < b i)
    (hdisj : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (F E : ℝ → ℝ)
    (herr : ∀ i, |P.eval (a i) - F (a i)| ≤ E (a i) ∧
      |P.eval (b i) - F (b i)| ≤ E (b i))
    (hmargin : ∀ i, (E (a i) < F (a i) ∧ F (b i) < -E (b i)) ∨
      (E (b i) < F (b i) ∧ F (a i) < -E (a i)))
    (hdegree : P.natDegree ≤ Fintype.card ι) :
    ∃ x : ι → ℝ,
      (∀ i, x i ∈ Ioo (a i) (b i) ∧ P.eval (x i) = 0) ∧
      Function.Injective x ∧
      P.roots = (Finset.univ.image x).val ∧
      P.natDegree = Fintype.card ι := by
  apply roots_of_disjoint_sign_changes P hP a b hab hdisj _ hdegree
  intro i
  rcases hmargin i with h | h
  · exact Or.inr ⟨negative_of_error_margin _ _ _ (herr i).2 h.2,
      positive_of_error_margin _ _ _ (herr i).1 h.1⟩
  · exact Or.inl ⟨negative_of_error_margin _ _ _ (herr i).1 h.2,
      positive_of_error_margin _ _ _ (herr i).2 h.1⟩

/-- After the global degree budget is exhausted, the root count in each
pairwise-disjoint block equals its number of assigned witness intervals.
Blocks with no assigned witness have zero roots. Capacities can be arbitrary. -/
theorem exact_block_counts {ι κ : Type*} [Fintype ι]
    (P : Polynomial ℝ) (hP : P ≠ 0) (a b : ι → ℝ)
    (hab : ∀ i, a i < b i)
    (hdisj : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hsign : ∀ i, (P.eval (a i) < 0 ∧ 0 < P.eval (b i)) ∨
      (P.eval (b i) < 0 ∧ 0 < P.eval (a i)))
    (hdegree : P.natDegree ≤ Fintype.card ι)
    (label : ι → κ) (U : κ → Set ℝ)
    (hU : Pairwise (fun j k => Disjoint (U j) (U k)))
    (hloc : ∀ i, Ioo (a i) (b i) ⊆ U (label i)) :
    ∀ j, rootCountIn P (U j) = labelCount label j := by
  classical
  obtain ⟨x, hx, hinj, hroots, _⟩ :=
    roots_of_disjoint_sign_changes P hP a b hab hdisj hsign hdegree
  intro j
  have hlabel (i : ι) : x i ∈ U j ↔ label i = j := by
    constructor
    · intro hij
      by_contra hne
      exact Set.disjoint_left.mp (hU hne) (hloc i (hx i).1) hij
    · intro hij
      rw [← hij]
      exact hloc i (hx i).1
  unfold rootCountIn labelCount
  rw [hroots, ← Finset.filter_val, Finset.filter_image]
  change (Finset.image x ((Finset.univ : Finset ι).filter (fun i => x i ∈ U j))).card =
    ((Finset.univ : Finset ι).filter (fun i => label i = j)).card
  rw [Finset.card_image_of_injective _ hinj]
  congr 1
  apply Finset.filter_congr
  intro i hi
  exact hlabel i

end BlockSignCount

#print axioms BlockSignCount.roots_of_disjoint_sign_changes
#print axioms BlockSignCount.roots_of_robust_margins
#print axioms BlockSignCount.exact_block_counts
