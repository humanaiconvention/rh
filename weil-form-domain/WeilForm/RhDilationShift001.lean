import RhDilationNorm001
import RhEndpointParityShift001

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhDilation
open RhAnchored

def realShift (w : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∫t:ℝ,(w (t+L)+w (t-L))*w t

/-- Exact actual physical pairing; the zero extension is attached to both factors. -/
theorem actual_shift_pairing (A L : ℝ) (w : ℝ → ℝ) :
    (∫t in interval A,primeShift A L w t*w t)=
      realShift (zeroExtension A w) L := by
  unfold realShift
  calc
    _ = ∫t:ℝ,(interval A).indicator (fun t=>primeShift A L w t*w t) t :=
      (integral_indicator measurableSet_Icc).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t=>by
        by_cases ht:t∈interval A
        · simp only [indicator_of_mem ht,primeShift,zeroExtension,ht]
        · simp [ht,zeroExtension])

/-- Exact translation length after unitary dilation, without a norm estimate. -/
theorem realShift_dilate {r : ℝ} (hr : 0 < r) (w : ℝ → ℝ) (L : ℝ) :
    realShift (dilate r w) L=realShift w (L/r) := by
  have he : (fun t:ℝ=>(dilate r w (t+L)+dilate r w (t-L))*dilate r w t)=
      (fun t:ℝ=>r⁻¹*((w (t/r+L/r)+w (t/r-L/r))*w (t/r))) := by
    funext t
    simp only [dilate,add_div,sub_div]
    have hsq:=Real.sq_sqrt hr.le
    have hn:Real.sqrt r≠0 := (Real.sqrt_pos.2 hr).ne'
    field_simp
    rw [hsq]
  unfold realShift
  rw [he,integral_const_mul]
  have hi:=Measure.integral_comp_div
    (fun t:ℝ=>(w (t+L/r)+w (t-L/r))*w t) r
  rw [hi,abs_of_pos hr]
  simp only [smul_eq_mul]
  field_simp

/-- Exact interval shift dilation. Both signed translations remain present. -/
theorem shift_dilation {r : ℝ} (hr : 0 < r) (A L : ℝ) (w : ℝ → ℝ) :
    (∫t in interval (r*A),primeShift (r*A) L (dilate r w) t*dilate r w t)=
      ∫t in interval A,primeShift A (L/r) w t*w t := by
  rw [actual_shift_pairing,actual_shift_pairing]
  have he : zeroExtension (r*A) (dilate r w)=dilate r (zeroExtension A w) := by
    funext t
    exact zeroExtension_dilate hr A w t
  rw [he,realShift_dilate hr]

lemma realShift_integrable {w : ℝ → ℝ} (hw : MemLp w 2 volume) (L : ℝ) :
    Integrable (fun t:ℝ=>(w (t+L)+w (t-L))*w t) := by
  have hp:=hw.comp_measurePreserving (measurePreserving_add_right volume L)
  have hm:=hw.comp_measurePreserving (measurePreserving_add_right volume (-L))
  have h := (hp.add hm).integrable_mul hw
  change Integrable (fun t:ℝ=>(w (t+L)+w (t+ -L))*w t) volume at h
  simpa only [sub_eq_add_neg] using h

/-- Whole-space two-shift norm bound, derived directly from L2 integrability. -/
theorem realShift_abs_bound {w : ℝ → ℝ} (hw : MemLp w 2 volume) (L : ℝ) :
    |realShift w L| ≤ 2*(∫t:ℝ,(w t)^2) := by
  have hp:=hw.comp_measurePreserving (measurePreserving_add_right volume L)
  have hm:=hw.comp_measurePreserving (measurePreserving_add_right volume (-L))
  have hiP:Integrable (fun t:ℝ=>(w (t+L))^2) := by
    simpa only [Function.comp_def] using hp.integrable_sq
  have hiM:Integrable (fun t:ℝ=>(w (t-L))^2) := by
    simpa only [Function.comp_def,sub_eq_add_neg] using hm.integrable_sq
  have hiW:=hw.integrable_sq
  have hiU:=((hiP.add hiM).div_const 2).add hiW
  have hpoint (t:ℝ) : |(w (t+L)+w (t-L))*w t|≤
      ((w (t+L))^2+(w (t-L))^2)/2+(w t)^2 := by
    rw [abs_mul]
    have h1:=abs_add_le (w (t+L)) (w (t-L))
    have h2:=mul_le_mul_of_nonneg_right h1 (abs_nonneg (w t))
    nlinarith [sq_nonneg (|w (t+L)|-|w t|),
      sq_nonneg (|w (t-L)|-|w t|),sq_abs (w (t+L)),sq_abs (w (t-L)),sq_abs (w t)]
  have hmono:=integral_mono (realShift_integrable hw L).abs hiU hpoint
  simp only [Pi.add_apply] at hmono
  have hnorm:=norm_integral_le_integral_norm (μ:=volume) (f:=fun t:ℝ=>(w (t+L)+w (t-L))*w t)
  simp only [Real.norm_eq_abs] at hnorm
  have hpint:(∫t:ℝ,(w (t+L))^2)=∫t:ℝ,(w t)^2 := by
    exact integral_add_right_eq_self (fun t:ℝ=>(w t)^2) L
  have hmint:(∫t:ℝ,(w (t-L))^2)=∫t:ℝ,(w t)^2 := by
    simpa only [sub_eq_add_neg] using
      integral_add_right_eq_self (fun t:ℝ=>(w t)^2) (-L)
  have he:(∫t:ℝ,((w (t+L))^2+(w (t-L))^2)/2+(w t)^2)=
      2*(∫t:ℝ,(w t)^2) := by
    have hadd := integral_add ((hiP.add hiM).div_const 2) hiW
    have hadd2 := integral_add hiP hiM
    simp only [Pi.add_apply] at hadd hadd2
    rw [hadd,integral_div,hadd2,hpint,hmint]
    ring
  unfold realShift
  exact hnorm.trans (hmono.trans_eq he)

/-- Actual physical two-shift bound with exact mass normalization. -/
theorem actual_shift_abs_bound {A : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure A)) (L : ℝ) :
    |∫t in interval A,primeShift A L w t*w t|≤2*(∫t in interval A,(w t)^2) := by
  rw [actual_shift_pairing]
  have hb:=realShift_abs_bound (zeroExtension_memLp hw) L
  rw [zeroExtension_square_integral] at hb
  exact hb
end RhDilation
#print axioms RhDilation.actual_shift_pairing
#print axioms RhDilation.realShift_dilate
#print axioms RhDilation.shift_dilation
#print axioms RhDilation.realShift_abs_bound
#print axioms RhDilation.actual_shift_abs_bound
