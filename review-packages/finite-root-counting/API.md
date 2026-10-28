# Exact API and hypothesis boundary

All declarations below are in namespace `BlockSignCount`. The authoritative
unchanged proof is [BlockSignCount.lean](BlockSignCount.lean). These are its
public declarations, transcribed without changing hypotheses.

## Definitions

```lean
noncomputable def rootCountIn (P : Polynomial ℝ) (U : Set ℝ) : ℕ := by
  classical
  exact (P.roots.filter (fun x => x ∈ U)).card

noncomputable def labelCount {ι κ : Type*} [Fintype ι]
    (label : ι → κ) (j : κ) : ℕ := by
  classical
  exact ((univ : Finset ι).filter (fun i => label i = j)).card
```

`rootCountIn` counts the real-root multiset with multiplicity. These classical
definitions do not supply an executable root-location procedure.

## Construct and exhaust roots from actual signs

```lean
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
      P.natDegree = Fintype.card ι
```

The complete root-multiset equality and degree equality are conclusions.
The hypothesis is an upper degree budget, not supplied root reality.

## Obtain the signs from finite endpoint errors

```lean
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
      P.natDegree = Fintype.card ι
```

`F` and `E` are arbitrary functions. No continuity, uniform error bound or
analytic representation is required or concluded. Nonnegativity of the errors
at the selected endpoints follows from `herr`.

## Count roots in nonuniform blocks

```lean
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
    ∀ j, rootCountIn P (U j) = labelCount label j
```

The label type `κ` need not be finite, blocks need not cover the line, and
capacities need not be uniform. The selected intervals exhaust the degree before
the block counts are deduced. For robust margins, first use the preceding
theorem's elementary sign argument or the corresponding actual-sign hypotheses;
the block theorem itself states its signs explicitly.

## Dependency boundary

Only three Mathlib modules are imported:

- `Mathlib.Algebra.Polynomial.Roots`
- `Mathlib.Topology.Algebra.Polynomial`
- `Mathlib.Topology.Order.IntermediateValue`

There is no local RH provider import. Existing IVT and polynomial root/degree
theorems do the underlying classical mathematics; the contribution presented
for review is this combined finite interface.
