import RhDilationDefs001
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Actual physical L2 and anchored-primitive dilation. The nontrivial
Jacobian is supplied by map_volume_mul_left and interval substitution. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval ENNReal NNReal
namespace RhDilation
open RhAnchored

lemma mem_interval_mul_iff {r : ℝ} (hr : 0<r) (A x : ℝ) :
    r*x∈interval (r*A) ↔ x∈interval A := by
  change (-(r*A)≤r*x ∧ r*x≤r*A) ↔ (-A≤x ∧ x≤A)
  rw [show -(r*A)=r*(-A) by ring]
  exact and_congr (mul_le_mul_iff_right₀ hr) (mul_le_mul_iff_right₀ hr)

lemma mem_interval_div_iff {r : ℝ} (hr : 0<r) (A t : ℝ) :
    t/r∈interval A ↔ t∈interval (r*A) := by
  have he : r*(t/r)=t := by field_simp
  simpa only [he] using (mem_interval_mul_iff hr A (t/r)).symm

lemma zeroExtension_pullback {r : ℝ} (hr : 0<r) (A : ℝ) (v : ℝ → ℝ) (x : ℝ) :
    zeroExtension A (pullback r v) x=
      (r*Real.sqrt r)*zeroExtension (r*A) v (r*x) := by
  by_cases hx : x∈interval A
  · have hrx := (mem_interval_mul_iff hr A x).2 hx
    simp [zeroExtension,pullback,hx,hrx]
  · have hrx : r*x∉interval (r*A) := fun h=>hx ((mem_interval_mul_iff hr A x).1 h)
    simp [zeroExtension,pullback,hx,hrx]

lemma zeroExtension_dilate {r : ℝ} (hr : 0<r) (A : ℝ) (w : ℝ → ℝ) (t : ℝ) :
    zeroExtension (r*A) (dilate r w) t=dilate r (zeroExtension A w) t := by
  by_cases ht : t/r∈interval A
  · have hrt := (mem_interval_div_iff hr A t).1 ht
    simp [zeroExtension,dilate,ht,hrt]
  · have hrt : t∉interval (r*A) := fun h=>ht ((mem_interval_div_iff hr A t).2 h)
    simp [zeroExtension,dilate,ht,hrt]

/-- A positive scalar multiplication has the inverse scalar Jacobian. -/
lemma memLp_comp_mul {p : ℝ≥0∞} {r : ℝ} (hr : 0<r) {w : ℝ → ℝ}
    (hw : MemLp w p volume) : MemLp (fun x:ℝ=>w (r*x)) p volume := by
  have hMap : MemLp w p (Measure.map (fun x:ℝ=>r*x) volume) := by
    rw [Real.map_volume_mul_left hr.ne']
    exact hw.smul_measure (by finiteness)
  simpa only [Function.comp_def] using
    hMap.comp_of_map (measurable_const_mul r).aemeasurable

lemma memLp_comp_div {p : ℝ≥0∞} {r : ℝ} (hr : 0<r) {w : ℝ → ℝ}
    (hw : MemLp w p volume) : MemLp (fun t:ℝ=>w (t/r)) p volume := by
  have h := memLp_comp_mul (inv_pos.mpr hr) hw
  simpa only [div_eq_mul_inv,mul_comm] using h

lemma dilate_memLp {p : ℝ≥0∞} {r : ℝ} (hr : 0<r) {w : ℝ → ℝ}
    (hw : MemLp w p volume) : MemLp (dilate r w) p volume :=
  (memLp_comp_div hr hw).const_mul (Real.sqrt r)⁻¹

lemma zeroExtension_memLp {p : ℝ≥0∞} {A : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w p (physicalMeasure A)) : MemLp (zeroExtension A w) p volume :=
  (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 hw

/-- Actual physical pullback membership, with the Jacobian handled before
restriction to the smaller interval. -/
theorem pullback_memLp {p : ℝ≥0∞} {r A : ℝ} (hr : 0<r) {v : ℝ → ℝ}
    (hv : MemLp v p (physicalMeasure (r*A))) :
    MemLp (pullback r v) p (physicalMeasure A) := by
  have h := (memLp_comp_mul hr (zeroExtension_memLp hv)).const_mul (r*Real.sqrt r)
  have hz : MemLp (zeroExtension A (pullback r v)) p volume := by
    apply (memLp_congr_ae ?_).1 h
    exact Eventually.of_forall (fun x=>(zeroExtension_pullback hr A v x).symm)
  exact (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).1 hz

lemma dilate_memLp_physical {p : ℝ≥0∞} {r A : ℝ} (hr : 0<r) {w : ℝ → ℝ}
    (hw : MemLp w p (physicalMeasure A)) :
    MemLp (dilate r w) p (physicalMeasure (r*A)) := by
  have h := dilate_memLp hr (zeroExtension_memLp hw)
  have hz : MemLp (zeroExtension (r*A) (dilate r w)) p volume := by
    apply (memLp_congr_ae ?_).1 h
    exact Eventually.of_forall (fun t=>(zeroExtension_dilate hr A w t).symm)
  exact (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).1 hz

lemma leftPrimitive_pullback {r : ℝ} (hr : 0<r) (A : ℝ) (v : ℝ → ℝ) (x : ℝ) :
    leftPrimitive A (pullback r v) x=Real.sqrt r*leftPrimitive (r*A) v (r*x) := by
  unfold leftPrimitive
  simp_rw [zeroExtension_pullback hr A v]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left _ hr.ne']
  simp only [smul_eq_mul]
  rw [show r*(-A)= -(r*A) by ring]
  field_simp
  <;> ring

lemma rightPrimitive_pullback {r : ℝ} (hr : 0<r) (A : ℝ) (v : ℝ → ℝ) (x : ℝ) :
    rightPrimitive A (pullback r v) x=Real.sqrt r*rightPrimitive (r*A) v (r*x) := by
  unfold rightPrimitive
  simp_rw [zeroExtension_pullback hr A v]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left _ hr.ne']
  simp only [smul_eq_mul]
  field_simp
  <;> ring

/-- Exact equality on both sides and at zero. No global absolute continuity
or pointwise derivative equality is presumed for the anchored primitive. -/
theorem primitive_pullback {r : ℝ} (hr : 0<r) (A : ℝ) (v : ℝ → ℝ) (x : ℝ) :
    primitive A (pullback r v) x=Real.sqrt r*primitive (r*A) v (r*x) := by
  by_cases hx : x<0
  · have hrx : r*x<0 := mul_neg_of_pos_of_neg hr hx
    rw [primitive_eq_left _ hx,primitive_eq_left _ hrx,leftPrimitive_pullback hr]
  · by_cases hx' : 0<x
    · have hrx : 0<r*x := mul_pos hr hx'
      rw [primitive_eq_right _ hx',primitive_eq_right _ hrx,rightPrimitive_pullback hr]
    · have hx0 : x=0 := le_antisymm (le_of_not_gt hx') (le_of_not_gt hx)
      subst x
      simp [primitive_zero]

theorem dilate_primitive_pullback {r : ℝ} (hr : 0<r) (A : ℝ) (v : ℝ → ℝ) (t : ℝ) :
    dilate r (primitive A (pullback r v)) t=primitive (r*A) v t := by
  unfold dilate
  rw [primitive_pullback hr]
  rw [show r*(t/r)=t by field_simp]
  have hs : Real.sqrt r≠0 := (Real.sqrt_pos.2 hr).ne'
  field_simp

end RhDilation
#print axioms RhDilation.zeroExtension_pullback
#print axioms RhDilation.zeroExtension_dilate
#print axioms RhDilation.pullback_memLp
#print axioms RhDilation.dilate_memLp_physical
#print axioms RhDilation.primitive_pullback
#print axioms RhDilation.dilate_primitive_pullback


