import RhFinitePrimitiveIntegrability001
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RhAnchored

def archTerm (k : ℕ) (x : ℝ) : ℝ :=
  (1-Real.exp (-(beta k)*|x|))/(4*(archIndex k)^2)
def archKernelTerm (k : ℕ) : ℝ → ℝ → ℝ := anchoredKernel (archTerm k)
def archMajorant (k : ℕ) : ℝ := 1/(archIndex k)^2
def fullKernel (C α L : ℝ) (t u : ℝ) : ℝ :=
  finiteKernel C α L 0 t u - ∑' k : ℕ, archKernelTerm k t u

lemma archMajorant_nonneg (k : ℕ) : 0 ≤ archMajorant k := by
  unfold archMajorant
  positivity

lemma archMajorant_summable : Summable archMajorant := by
  have h := (Real.summable_one_div_nat_add_rpow (1/4) 2).mpr (by norm_num)
  convert h using 1
  ext k
  simp [archMajorant, archIndex, Real.rpow_natCast, sq_abs]

lemma archTerm_norm_le (k : ℕ) (x : ℝ) :
    ‖archTerm k x‖ ≤ 1/(4*(archIndex k)^2) := by
  have hd : 0 < 4*(archIndex k)^2 := by unfold archIndex; positivity
  have he : Real.exp (-(beta k)*|x|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (beta_pos k).le) (abs_nonneg x))
  unfold archTerm
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hd.le)]
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-(beta k)*|x|)]) hd.le

lemma archKernelTerm_norm_le (k : ℕ) (t u : ℝ) :
    ‖archKernelTerm k t u‖ ≤ archMajorant k := by
  unfold archKernelTerm anchoredKernel
  calc
    _ ≤ ‖archTerm k (t-u)‖+‖archTerm k t‖+‖archTerm k (-u)‖+‖archTerm k 0‖ := by
      calc
        _ ≤ ‖archTerm k (t-u)-archTerm k t-archTerm k (-u)‖+‖archTerm k 0‖ := norm_add_le _ _
        _ ≤ (‖archTerm k (t-u)-archTerm k t‖+‖archTerm k (-u)‖)+‖archTerm k 0‖ :=
          by linarith [norm_sub_le (archTerm k (t-u)-archTerm k t) (archTerm k (-u))]
        _ ≤ _ := by linarith [norm_sub_le (archTerm k (t-u)) (archTerm k t)]
    _ ≤ 4*(1/(4*(archIndex k)^2)) := by
      linarith [archTerm_norm_le k (t-u), archTerm_norm_le k t,
        archTerm_norm_le k (-u), archTerm_norm_le k 0]
    _ = archMajorant k := by unfold archMajorant; ring

lemma archKernelTerm_summable (t u : ℝ) :
    Summable (fun k : ℕ => archKernelTerm k t u) :=
  archMajorant_summable.of_norm_bounded (fun k => archKernelTerm_norm_le k t u)

lemma finiteKernel_series (C α L : ℝ) (J : ℕ) (t u : ℝ) :
    finiteKernel C α L J t u = finiteKernel C α L 0 t u -
      ∑ k ∈ Finset.range J, archKernelTerm k t u := by
  unfold finiteKernel anchoredKernel finitePotential archKernelTerm anchoredKernel archTerm
  simp only [Finset.sum_range_zero, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

theorem finiteKernel_tendsto (C α L t u : ℝ) :
    Tendsto (fun J : ℕ => finiteKernel C α L J t u) atTop (𝓝 (fullKernel C α L t u)) := by
  have heq : (fun J : ℕ => finiteKernel C α L J t u) =
      (fun J : ℕ => finiteKernel C α L 0 t u-
        ∑ k ∈ Finset.range J, archKernelTerm k t u) := by
    funext J
    exact finiteKernel_series C α L J t u
  rw [heq]
  exact tendsto_const_nhds.sub (archKernelTerm_summable t u).hasSum.tendsto_sum_nat

lemma finiteKernel_uniform_bound {A : ℝ} (C α L : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (J : ℕ) (t u : ℝ), t ∈ interval A → u ∈ interval A →
      ‖finiteKernel C α L J t u‖ ≤ B := by
  have hc : Continuous (fun p : ℝ×ℝ => finiteKernel C α L 0 p.1 p.2) := by
    unfold finiteKernel anchoredKernel finitePotential
    simp only [Finset.sum_range_zero]
    fun_prop
  have hcompact : IsCompact ((interval A) ×ˢ (interval A)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B,hB⟩ := hcompact.bddAbove_image hc.norm.continuousOn
  refine ⟨max B 0+∑' k : ℕ, archMajorant k, ?_, ?_⟩
  · exact add_nonneg (le_max_right _ _) (tsum_nonneg archMajorant_nonneg)
  · intro J t u ht hu
    rw [finiteKernel_series]
    calc
      _ ≤ ‖finiteKernel C α L 0 t u‖+‖∑ k ∈ Finset.range J, archKernelTerm k t u‖ := norm_sub_le _ _
      _ ≤ max B 0+∑ k ∈ Finset.range J, archMajorant k := add_le_add
        ((hB (mem_image_of_mem _ (show (t,u) ∈ (interval A) ×ˢ (interval A) from
          ⟨ht,hu⟩))).trans (le_max_left _ _))
        (norm_sum_le_of_le _ (fun k _ => archKernelTerm_norm_le k t u))
      _ ≤ _ := by
        linarith [archMajorant_summable.sum_le_tsum (Finset.range J)
          (fun k _ => archMajorant_nonneg k)]

end RhAnchored
#print axioms RhAnchored.finiteKernel_tendsto
#print axioms RhAnchored.finiteKernel_uniform_bound
