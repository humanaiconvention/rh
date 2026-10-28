# Exact ordered-counting API

The following definition and four theorem types are transcribed from the unchanged [FiniteCellCount.lean](FiniteCellCount.lean), in namespace `RhCountingAudit`. The source imports `Mathlib.Algebra.Polynomial.Roots` and `Mathlib.Data.Real.Basic`.

## Inclusive finite prefix count

```lean
namespace RhCountingAudit

open Finset

noncomputable def prefixCount {α : Type*} [LinearOrder α]
    (n : ℕ) (r : ℕ → α) (t : α) : ℕ := by
  classical
  exact ((range n).filter (fun i => r i ≤ t)).card
```

This counts indices in `range n`. No injectivity is built into the definition. The threshold test is `≤`, not `<`.

## Interleaved prefixes

```lean
theorem interleaved_prefix_bounds {α : Type*} [LinearOrder α]
    (n : ℕ) (r c : ℕ → α)
    (h : ∀ i < n, r i < c i ∧ c i < r (i + 1)) (t : α) :
    prefixCount n c t ≤ prefixCount (n + 1) r t ∧
      prefixCount (n + 1) r t ≤ prefixCount n c t + 1

theorem common_cells_prefix_discrepancy {α : Type*} [LinearOrder α]
    (n : ℕ) (p b c : ℕ → α)
    (hp : ∀ i < n, p i < c i ∧ c i < p (i + 1))
    (hb : ∀ i < n, b i < c i ∧ c i < b (i + 1)) (t : α) :
    prefixCount (n + 1) p t ≤ prefixCount (n + 1) b t + 1 ∧
      prefixCount (n + 1) b t ≤ prefixCount (n + 1) p t + 1
```

The first theorem compares n separators with n+1 entries. The second compares two n+1-entry prefixes sharing n separators. Both apply to any `LinearOrder`; there is no polynomial or root premise. For n = 0, all interleaving premises are vacuous and each entry prefix contains one index.

## Exhaustion by distinct root witnesses

```lean
theorem roots_eq_of_distinct_witnesses (P : Polynomial ℝ) (hP : P ≠ 0)
    (d : ℕ) (x : Fin d → ℝ) (hx : Function.Injective x)
    (hz : ∀ i, P.eval (x i) = 0) (hdeg : P.natDegree ≤ d) :
    P.roots = (univ.image x).val
```

The conclusion is equality of the complete real-root **multiset**, not merely equality of root sets. Injectivity and the degree budget leave no additional root multiplicities. The witnesses are assumptions here; this theorem does not construct them from signs.

## Exhaustion from ordered open-cell witnesses

```lean
theorem roots_eq_of_ordered_cell_witnesses (P : Polynomial ℝ) (hP : P ≠ 0)
    (d : ℕ) (b : ℕ → ℝ) (hb : Monotone b) (x : Fin d → ℝ)
    (hcell : ∀ i, b i.val < x i ∧ x i < b (i.val + 1))
    (hz : ∀ i, P.eval (x i) = 0) (hdeg : P.natDegree ≤ d) :
    P.roots = (univ.image x).val

end RhCountingAudit
```

The hypothesis is `Monotone b`, with strict inequalities inside each occupied open cell. Injectivity is proved, not added as another premise. For d = 0, the witness type is empty and the nonzero-polynomial degree bound gives an empty root multiset.

These types do not state an infinite counting estimate or discharge an application's root/sign/ordering hypotheses. The [companion essay](INTERLEAVING.md) explains their relation to the separate sign-witness and block-counting interface.
