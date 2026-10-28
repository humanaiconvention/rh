import RhWeilThetaBound001
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Strong measurability of the actual modified theta kernel after the
logarithmic change of variables. Its isolated value at t=1 is retained. -/
set_option maxHeartbeats 1000000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhWeilTheta

lemma theta_exp_continuous :
    Continuous (fun u : ℝ => (HurwitzZeta.evenKernel 0 (Real.exp (-u)):ℂ)) := by
  apply Complex.continuous_ofReal.comp
  exact (HurwitzZeta.continuousOn_evenKernel 0).comp_continuous
    (by fun_prop) (fun u=>Real.exp_pos _)

/-- The open branches of the actual FE modification are Borel measurable.
No continuity at its assigned zero value t=1 is asserted. -/
theorem modif_exp_stronglyMeasurable :
    StronglyMeasurable (fun u : ℝ =>
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (-u))) := by
  have he : Continuous (fun u : ℝ=>Real.exp (-u)) := by fun_prop
  have hpow : Continuous (fun u : ℝ=>(Real.exp (-u))^(-(1/2:ℝ))) := by
    exact he.rpow_const (fun _ => Or.inl (Real.exp_pos _).ne')
  have hleft : Continuous (fun u : ℝ=>
      (HurwitzZeta.evenKernel 0 (Real.exp (-u)):ℂ)-1) :=
    theta_exp_continuous.sub continuous_const
  have hright : Continuous (fun u : ℝ=>
      (HurwitzZeta.evenKernel 0 (Real.exp (-u)):ℂ)-
      ((Real.exp (-u))^(-(1/2:ℝ)):ℝ)) :=
    theta_exp_continuous.sub (Complex.continuous_ofReal.comp hpow)
  have hsleft : MeasurableSet {u : ℝ | 1<Real.exp (-u)} :=
    (isOpen_lt continuous_const he).measurableSet
  have hsright : MeasurableSet {u : ℝ | 0<Real.exp (-u) ∧ Real.exp (-u)<1} :=
    ((isOpen_lt continuous_const he).inter (isOpen_lt he continuous_const)).measurableSet
  have hm := (hleft.stronglyMeasurable.indicator hsleft).add
    (hright.stronglyMeasurable.indicator hsright)
  convert hm using 1
  funext u
  simp [WeakFEPair.f_modif,HurwitzZeta.hurwitzEvenFEPair,
    Set.indicator,smul_eq_mul]

/-- The actual weighted logarithmic theta integrand is strongly measurable
for every complex Mellin parameter. -/
theorem weighted_modif_stronglyMeasurable (s : ℂ) :
    StronglyMeasurable (fun u : ℝ=>Real.exp (-s.re*u) •
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (-u))) := by
  exact (by fun_prop : Continuous (fun u : ℝ=>Real.exp (-s.re*u))).stronglyMeasurable.smul
    modif_exp_stronglyMeasurable

theorem weighted_modif_aestronglyMeasurable (s : ℂ) :
    AEStronglyMeasurable (fun u : ℝ=>Real.exp (-s.re*u) •
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (-u))) volume :=
  (weighted_modif_stronglyMeasurable s).aestronglyMeasurable

end RhWeilTheta
#print axioms RhWeilTheta.theta_exp_continuous
#print axioms RhWeilTheta.modif_exp_stronglyMeasurable
#print axioms RhWeilTheta.weighted_modif_stronglyMeasurable
#print axioms RhWeilTheta.weighted_modif_aestronglyMeasurable


