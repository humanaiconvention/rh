import RhAnchoredKernel001

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

def finiteKernelExpanded (C α L : ℝ) (J : ℕ) (t u : ℝ) : ℝ :=
  8*Real.sinh (t/2)*Real.sinh (u/2)
  -8*(Real.cosh (t/2)-1)*(Real.cosh (u/2)-1)
  -(C/2)*(|t|+|u|-|t-u|)
  + (∑ k ∈ Finset.range J,
      (Real.exp (-(beta k)*|t-u|)-Real.exp (-(beta k)*|t|)
        -Real.exp (-(beta k)*|u|)+1)/(4*(archIndex k)^2))
  + α*(max (|t-u|-L) 0-max (|t|-L) 0-max (|u|-L) 0+max (-L) 0)

theorem finiteKernel_expansion (C α L : ℝ) (J : ℕ) (t u : ℝ) :
    finiteKernel C α L J t u = finiteKernelExpanded C α L J t u := by
  have hsum :
      -(∑ k ∈ Finset.range J, (1-Real.exp (-(beta k)*|t-u|))/(4*(archIndex k)^2))
      +(∑ k ∈ Finset.range J, (1-Real.exp (-(beta k)*|t|))/(4*(archIndex k)^2))
      +(∑ k ∈ Finset.range J, (1-Real.exp (-(beta k)*|u|))/(4*(archIndex k)^2))
      = ∑ k ∈ Finset.range J,
        (Real.exp (-(beta k)*|t-u|)-Real.exp (-(beta k)*|t|)
          -Real.exp (-(beta k)*|u|)+1)/(4*(archIndex k)^2) := by
    calc
      _ = ∑ k ∈ Finset.range J,
          (-(1-Real.exp (-(beta k)*|t-u|))/(4*(archIndex k)^2)
          +(1-Real.exp (-(beta k)*|t|))/(4*(archIndex k)^2)
          +(1-Real.exp (-(beta k)*|u|))/(4*(archIndex k)^2)) := by
            simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_div]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        ring
  unfold finiteKernel anchoredKernel finitePotential finiteKernelExpanded
  simp only [zero_sub, abs_neg, neg_div, Real.cosh_neg, abs_zero, zero_div,
    Real.cosh_zero, sub_self, mul_zero, neg_zero, Real.exp_zero, Finset.sum_const_zero,
    zero_add, add_zero, sub_zero]
  rw [show (t-u)/2=t/2-u/2 by ring, Real.cosh_sub]
  linear_combination hsum

theorem finiteKernel_first_window_expansion {A L : ℝ} (hL : 0 ≤ L) (hAL : A ≤ L)
    (C α : ℝ) (J : ℕ) {t u : ℝ} (ht : t ∈ interval A) (hu : u ∈ interval A) :
    finiteKernel C α L J t u =
    8*Real.sinh (t/2)*Real.sinh (u/2)
    -8*(Real.cosh (t/2)-1)*(Real.cosh (u/2)-1)
    -(C/2)*(|t|+|u|-|t-u|)
    +(∑ k ∈ Finset.range J,
      (Real.exp (-(beta k)*|t-u|)-Real.exp (-(beta k)*|t|)
        -Real.exp (-(beta k)*|u|)+1)/(4*(archIndex k)^2))
    +α*max (|t-u|-L) 0 := by
  have htL : |t| ≤ L := (abs_le.mpr ⟨ht.1, ht.2⟩).trans hAL
  have huL : |u| ≤ L := (abs_le.mpr ⟨hu.1, hu.2⟩).trans hAL
  rw [finiteKernel_expansion]
  simp only [finiteKernelExpanded, max_eq_right (sub_nonpos.mpr htL),
    max_eq_right (sub_nonpos.mpr huL), max_eq_right (neg_nonpos.mpr hL),
    sub_zero, add_zero]

end RhAnchored
#print axioms RhAnchored.finiteKernel_expansion
#print axioms RhAnchored.finiteKernel_first_window_expansion
