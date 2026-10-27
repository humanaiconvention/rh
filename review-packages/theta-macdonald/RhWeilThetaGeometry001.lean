import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-! Exact logarithmic-variable bounds for the actual modified theta kernel.
The head exponential bound is kept explicit here and discharged separately. -/
set_option maxHeartbeats 0
noncomputable section
open Set Filter MeasureTheory
open scoped Topology FourierTransform
namespace RhWeilThetaGeometry

def modif (t : ℝ) : ℂ := (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t

lemma modif_one : modif 1=0 := by
  simp [modif,WeakFEPair.f_modif]

lemma modif_inv {t : ℝ} (ht : 0<t) :
    modif (1/t)=((t^(1/2:ℝ):ℝ):ℂ)*modif t := by
  have h := (HurwitzZeta.hurwitzEvenFEPair 0).hf_modif_FE t ht
  have hg : (HurwitzZeta.hurwitzEvenFEPair 0).g_modif t=modif t := by
    simp [WeakFEPair.g_modif,modif,WeakFEPair.f_modif,
      HurwitzZeta.hurwitzEvenFEPair,HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  rw [hg] at h
  simpa only [modif,HurwitzZeta.hurwitzEvenFEPair,one_mul,smul_eq_mul] using h

lemma modif_log_bound {C p : ℝ} (hC : 0≤C)
    (hh : ∀t:ℝ,1≤t→‖modif t‖≤C*Real.exp (-p*t)) (u : ℝ) :
    ‖modif (Real.exp (-u))‖≤C*Real.exp (|u|/2-p*Real.exp |u|) := by
  by_cases hu : 0≤u
  · have ht : 1≤Real.exp u := Real.one_le_exp_iff.mpr hu
    have hi := modif_inv (Real.exp_pos u)
    rw [one_div,←Real.exp_neg] at hi
    rw [hi,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos u) _),
      Real.rpow_def_of_pos (Real.exp_pos u),Real.log_exp,abs_of_nonneg hu]
    calc
      _ ≤ Real.exp (u*(1/2))* (C*Real.exp (-p*Real.exp u)) :=
        mul_le_mul_of_nonneg_left (hh _ ht) (Real.exp_pos _).le
      _ = _ := by rw [show Real.exp (u*(1/2))*(C*Real.exp (-p*Real.exp u))=
        C*(Real.exp (u*(1/2))*Real.exp (-p*Real.exp u)) by ring,←Real.exp_add];congr 2;ring
  · have hu0 : u≤0 := le_of_not_ge hu
    have ht : 1≤Real.exp (-u) := Real.one_le_exp_iff.mpr (by linarith)
    rw [abs_of_nonpos hu0]
    exact (hh _ ht).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) hC)

lemma square_le_four_exp {x : ℝ} (hx : 0≤x) : x^2≤4*Real.exp x := by
  have he := Real.add_one_le_exp (x/2)
  have hh : x/2≤Real.exp (x/2) := by linarith
  have hs := mul_self_le_mul_self (by positivity : (0:ℝ)≤x/2) hh
  have hxexp : Real.exp (x/2)*Real.exp (x/2)=Real.exp x := by
    rw [←Real.exp_add];congr 1;ring
  rw [hxexp] at hs
  nlinarith

lemma linear_double_exponential_le_gaussian {p r u : ℝ} (hp : 0<p) :
    r*|u|-p*Real.exp |u|≤2*r^2/p-(p/8)*u^2 := by
  have he := square_le_four_exp (abs_nonneg u)
  have hphe := mul_le_mul_of_nonneg_left he hp.le
  have hy : r*|u|-p*|u|^2/8≤2*r^2/p := by
    apply (le_div_iff₀ hp).mpr
    nlinarith [sq_nonneg (p*|u|-4*r)]
  rw [sq_abs] at hphe hy
  nlinarith

lemma twisted_gaussian_bound {C p : ℝ} (hC : 0≤C) (hp : 0<p)
    (hh : ∀t:ℝ,1≤t→‖modif t‖≤C*Real.exp (-p*t)) (s : ℂ) (u : ℝ) :
    ‖Real.exp (-s.re*u) • modif (Real.exp (-u))‖≤
      (C*Real.exp (2*(|s.re|+1/2)^2/p))*Real.exp (-(p/8)*u^2) := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-s.re*u)*(C*Real.exp (|u|/2-p*Real.exp |u|)) :=
      mul_le_mul_of_nonneg_left (modif_log_bound hC hh u) (Real.exp_pos _).le
    _ = C*Real.exp (-s.re*u+|u|/2-p*Real.exp |u|) := by
      rw [show Real.exp (-s.re*u)*(C*Real.exp (|u|/2-p*Real.exp |u|))=
        C*(Real.exp (-s.re*u)*Real.exp (|u|/2-p*Real.exp |u|)) by ring,←Real.exp_add]
      congr 2;ring
    _ ≤ C*Real.exp (2*(|s.re|+1/2)^2/p-(p/8)*u^2) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      have hprod : -s.re*u≤|s.re| *|u| := by
        calc
          _ ≤ |s.re*u| := by simpa only [neg_mul] using neg_le_abs (s.re*u)
          _ = _ := abs_mul _ _
      have hhg := linear_double_exponential_le_gaussian (p:=p) (r:=|s.re|+1/2) (u:=u) hp
      linarith
    _ = _ := by
      rw [show 2*(|s.re|+1/2)^2/p-(p/8)*u^2 =
        2*(|s.re|+1/2)^2/p+(-(p/8)*u^2) by ring,Real.exp_add]
      ring

end RhWeilThetaGeometry
#print axioms RhWeilThetaGeometry.modif_inv
#print axioms RhWeilThetaGeometry.modif_log_bound
#print axioms RhWeilThetaGeometry.twisted_gaussian_bound
