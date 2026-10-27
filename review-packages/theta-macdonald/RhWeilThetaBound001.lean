import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Tactic

/-! An unconditional exponential bound for the actual even theta kernel,
including the full compact head t>=1. No explicit-formula hypothesis is used. -/
set_option maxHeartbeats 1000000
noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Topology
namespace RhWeilTheta

/-- Upgrade mathlib's actual theta-kernel asymptotic estimate to every t>=1
using its continuous compact head. No numerical constant is assumed. -/
theorem evenKernel_head_bound :
    ∃ C : ℝ, 0<C ∧ ∃ p : ℝ, 0<p ∧ ∀ t : ℝ, 1≤t →
      |HurwitzZeta.evenKernel 0 t-1|≤C*Real.exp (-p*t) := by
  obtain ⟨p,hp,hO⟩ := HurwitzZeta.isBigO_atTop_evenKernel_sub (0:UnitAddCircle)
  have hO' : (fun t : ℝ=>HurwitzZeta.evenKernel 0 t-1) =O[atTop]
      (fun t : ℝ=>Real.exp (-p*t)) := by simpa using hO
  obtain ⟨C0,hC0⟩ := hO'.bound
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp hC0
  let T : ℝ := max T0 1
  let ratio : ℝ → ℝ := fun t=>|HurwitzZeta.evenKernel 0 t-1|/Real.exp (-p*t)
  have htpos : Icc 1 T ⊆ Ioi (0:ℝ) := by
    intro t ht
    exact lt_of_lt_of_le zero_lt_one ht.1
  have hc : ContinuousOn ratio (Icc 1 T) := by
    apply ContinuousOn.div
    · exact ((HurwitzZeta.continuousOn_evenKernel 0).mono htpos).sub continuousOn_const |>.abs
    · fun_prop
    · intro t _
      exact (Real.exp_pos _).ne'
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image hc
  let C : ℝ := max (max B C0) 0+1
  have hC : 0<C := by dsimp only [C];linarith [le_max_right (max B C0) 0]
  have hBC : B≤C := by
    dsimp only [C]
    linarith [le_max_left B C0,le_max_left (max B C0) 0]
  have h0C : C0≤C := by
    dsimp only [C]
    linarith [le_max_right B C0,le_max_left (max B C0) 0]
  refine ⟨C,hC,p,hp,fun t ht=>?_⟩
  by_cases htT : t≤T
  · have hb : ratio t≤B := hB (mem_image_of_mem _ ⟨ht,htT⟩)
    have hab : |HurwitzZeta.evenKernel 0 t-1|≤B*Real.exp (-p*t) :=
      (div_le_iff₀ (Real.exp_pos _)).mp hb
    exact hab.trans (mul_le_mul_of_nonneg_right hBC (Real.exp_pos _).le)
  · have hT0t : T0≤t := le_trans (le_max_left T0 1) (lt_of_not_ge htT).le
    have hb := hT0 t hT0t
    have hab : |HurwitzZeta.evenKernel 0 t-1|≤C0*Real.exp (-p*t) := by
      simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hb
    exact hab.trans (mul_le_mul_of_nonneg_right h0C (Real.exp_pos _).le)

/-- The actual modified FE kernel is zero at t=1 and theta(t)-1 above 1.
This theorem retains that endpoint convention exactly. -/
theorem fePair_modif_head_bound :
    ∃ C : ℝ, 0<C ∧ ∃ p : ℝ, 0<p ∧ ∀ t : ℝ, 1≤t →
      ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖≤C*Real.exp (-p*t) := by
  obtain ⟨C,hC,p,hp,hb⟩ := evenKernel_head_bound
  refine ⟨C,hC,p,hp,fun t ht=>?_⟩
  rcases ht.eq_or_lt with hte|htt
  · subst t
    simp only [WeakFEPair.f_modif,Pi.add_apply]
    simp
    positivity
  · have he : (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t=
        (HurwitzZeta.evenKernel 0 t-1:ℝ) := by
      simp [WeakFEPair.f_modif,HurwitzZeta.hurwitzEvenFEPair,
        Set.indicator_of_mem (show t∈Ioi (1:ℝ) from htt),
        Set.indicator_of_notMem (show t∉Ioo (0:ℝ) 1 from fun h=>not_lt_of_ge ht h.2)]
    rw [he,Complex.norm_real]
    exact hb t ht

end RhWeilTheta
#print axioms RhWeilTheta.evenKernel_head_bound
#print axioms RhWeilTheta.fePair_modif_head_bound
