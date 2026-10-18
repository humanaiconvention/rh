import RhCutoffPointRemoval001
import RhFlatSmoothCore001

/-! PRIVATE complete-norm density of genuine smooth representatives avoiding
any prescribed FINITE set of points. This does not assume a finite-jet
representation or a bounded extension of a restricted functional. -/
set_option maxHeartbeats 150000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RhPuncturedSmoothCore
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhCutoffPointRemoval

/-- Actual smooth representatives, same window, avoiding the declared points. -/
def puncturedWeightedSet (R : ℝ) (F : Finset ℝ) : Set WeightedSpace :=
  {X | ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    tsupport f ⊆ Ioo (-R) R ∧ (∀ x ∈ F, x ∉ tsupport f) ∧
    physicalEmbedding X =ᵐ[volume] fun t => (f t : ℂ)}

def puncturedCore (R : ℝ) (F : Finset ℝ) : Submodule ℝ WeightedSpace :=
  (Submodule.span ℝ (puncturedWeightedSet R F)).topologicalClosure

lemma puncturedCore_isClosed (R : ℝ) (F : Finset ℝ) :
    IsClosed (puncturedCore R F : Set WeightedSpace) :=
  (Submodule.span ℝ (puncturedWeightedSet R F)).isClosed_topologicalClosure

lemma puncturedCore_le_flat (R : ℝ) (F : Finset ℝ) : puncturedCore R F ≤ flatCore R := by
  apply (Submodule.span ℝ (puncturedWeightedSet R F)).topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro X ⟨f,hf,hc,hs,_ha,hAE⟩
    exact smooth_generator_mem ⟨f,hf,hc,hs,hAE⟩
  · exact flatCore_isClosed R

lemma puncturedCore_empty (R : ℝ) : puncturedCore R ∅ = flatCore R := by
  have he : puncturedWeightedSet R ∅ = smoothWeightedSet R := by
    ext X
    constructor
    · rintro ⟨f,hf,hc,hs,_ha,hAE⟩
      exact ⟨f,hf,hc,hs,hAE⟩
    · rintro ⟨f,hf,hc,hs,hAE⟩
      exact ⟨f,hf,hc,hs,by simp,hAE⟩
  simp only [puncturedCore, flatCore, he]

/-- One-point removal preserves every earlier avoided point because the
literal topological support only shrinks. The convergence is already proved. -/
theorem puncturedCore_le_insert (R : ℝ) (F : Finset ℝ) (x : ℝ) :
    puncturedCore R F ≤ puncturedCore R (insert x F) := by
  classical
  apply (Submodule.span ℝ (puncturedWeightedSet R F)).topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro X ⟨f,hf,hc,hs,ha,hAE⟩
    let chi : ContDiffBump (0 : ℝ) := ⟨1,2,by norm_num,by norm_num⟩
    have hseq (n : ℕ) : removedVector X f hf chi x n ∈ puncturedCore R (insert x F) := by
      apply Submodule.le_topologicalClosure _
      apply Submodule.subset_span
      refine ⟨removedFunction f chi x n,removed_contDiff f hf chi x n,
        removed_compact f hc chi x n,(removed_tsupport_subset f chi x n).trans hs,?_,
        removedVector_physical_ae X f hf hAE chi x n⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with he | hyF
      · subst y
        exact removed_not_mem_tsupport f chi x n
      · intro hm
        exact ha y hyF (removed_tsupport_subset f chi x n hm)
    exact (puncturedCore_isClosed R (insert x F)).mem_of_tendsto
      (removedVector_tendsto X f hf hc chi x) (Eventually.of_forall hseq)
  · exact puncturedCore_isClosed R (insert x F)

/-- Full real complete-domain equality. No larger support window is used. -/
theorem puncturedCore_eq_flat (R : ℝ) (F : Finset ℝ) : puncturedCore R F = flatCore R := by
  classical
  apply le_antisymm (puncturedCore_le_flat R F)
  induction F using Finset.induction_on with
  | empty => rw [puncturedCore_empty]
  | @insert x F _hx ih => exact ih.trans (puncturedCore_le_insert R F x)

end RhPuncturedSmoothCore
#print axioms RhPuncturedSmoothCore.puncturedCore_le_insert
#print axioms RhPuncturedSmoothCore.puncturedCore_eq_flat