import RhAnchoredKernel001

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

def massNorm (A : ℝ) (v : ℝ → ℝ) : ℝ := ∫ t, ‖zeroExtension A v t‖

lemma massNorm_nonneg (A : ℝ) (v : ℝ → ℝ) : 0 ≤ massNorm A v :=
  integral_nonneg (fun _ => norm_nonneg _)

lemma zeroExtension_primitive_norm_le {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (t : ℝ) :
    ‖zeroExtension A (primitive A v) t‖ ≤ massNorm A v := by
  by_cases ht : t ∈ interval A
  · rw [zeroExtension_eq ht]
    exact primitive_norm_le hv t
  · rw [zeroExtension_eq_zero ht, norm_zero]
    exact massNorm_nonneg A v

lemma cumulative_primitive_lipschitz {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) :
    LipschitzWith (Real.toNNReal (massNorm A v)) (leftPrimitive A (primitive A v)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |leftPrimitive A (primitive A v) x-leftPrimitive A (primitive A v) y| ≤
    (Real.toNNReal (massNorm A v) : ℝ)*|x-y|
  rw [Real.toNNReal_of_nonneg (massNorm_nonneg A v), ← Real.norm_eq_abs]
  unfold leftPrimitive
  rw [intervalIntegral.integral_interval_sub_left
    (zeroExtension_integrable (primitive_memLp hv)).intervalIntegrable
    (zeroExtension_integrable (primitive_memLp hv)).intervalIntegrable]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t _ => zeroExtension_primitive_norm_le hv t)

lemma weighted_primitive_integrable {A : ℝ} (hA : 0 < A) {v g : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (hg : Continuous g) :
    Integrable (zeroExtension A (fun t => g t*primitive A v t)) := by
  have hw : IntervalIntegrable (primitive A v) volume (-A) A :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -A ≤ A)).2
      (primitive_integrableOn hv)
  have hp := hw.continuousOn_mul hg.continuousOn
  apply (integrable_indicator_iff measurableSet_Icc).2
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -A ≤ A)).1 hp

lemma zeroExtension_primitive_measurable {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) : Measurable (zeroExtension A (primitive A v)) :=
  (primitive_measurable hv).indicator measurableSet_Icc

lemma zeroExtension_primitive_continuousAt {A x : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (hx0 : x ≠ 0) (hxL : x ≠ -A) (hxR : x ≠ A) :
    ContinuousAt (zeroExtension A (primitive A v)) x := by
  by_cases hleft : x < -A
  · have hx : x ∉ interval A := by intro hx; linarith [hx.1]
    change Tendsto _ (𝓝 x) (𝓝 _)
    rw [zeroExtension_eq_zero hx]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_nhds hleft] with t ht
    symm
    exact zeroExtension_eq_zero (by intro htI; linarith [htI.1])
  by_cases hright : A < x
  · have hx : x ∉ interval A := by intro hx; linarith [hx.2]
    change Tendsto _ (𝓝 x) (𝓝 _)
    rw [zeroExtension_eq_zero hx]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_nhds hright] with t ht
    symm
    exact zeroExtension_eq_zero (by intro htI; linarith [htI.2])
  have hxIL : -A < x := by rcases lt_or_eq_of_le (le_of_not_gt hleft) with h|h; exact h; exact False.elim (hxL h.symm)
  have hxIR : x < A := by rcases lt_or_eq_of_le (le_of_not_gt hright) with h|h; exact h; exact False.elim (hxR h)
  by_cases hxneg : x < 0
  · have hx : x ∈ interval A := ⟨hxIL.le, hxIR.le⟩
    change Tendsto _ (𝓝 x) (𝓝 _)
    rw [zeroExtension_eq hx, primitive_eq_left v hxneg]
    apply (leftPrimitive_continuous hv).continuousAt.tendsto.congr'
    filter_upwards [Ioo_mem_nhds hxIL hxneg] with t ht
    symm
    rw [zeroExtension_eq (show t ∈ interval A from ⟨ht.1.le, by linarith [ht.2]⟩),
      primitive_eq_left v ht.2]
  · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hxneg) (Ne.symm hx0)
    have hx : x ∈ interval A := ⟨hxIL.le, hxIR.le⟩
    change Tendsto _ (𝓝 x) (𝓝 _)
    rw [zeroExtension_eq hx, primitive_eq_right v hxpos]
    apply (rightPrimitive_continuous hv).continuousAt.tendsto.congr'
    filter_upwards [Ioo_mem_nhds hxpos hxIR] with t ht
    symm
    rw [zeroExtension_eq (show t ∈ interval A from ⟨by linarith [ht.1], ht.2.le⟩),
      primitive_eq_right v ht.1]

def weightedCumulative (A ν : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (-A)..t, zeroExtension A (fun u => Real.exp (ν*u)*w u) u

lemma weighted_zeroExtension (A ν : ℝ) (w : ℝ → ℝ) (x : ℝ) :
    zeroExtension A (fun u => Real.exp (ν*u)*w u) x =
    Real.exp (ν*x)*zeroExtension A w x := by
  by_cases hx : x ∈ interval A <;> simp [zeroExtension, hx]

lemma weightedCumulative_ac {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (ν : ℝ) :
    AbsolutelyContinuousOnInterval (weightedCumulative A ν (primitive A v)) (-A) A := by
  exact (weighted_primitive_integrable hA hv (by fun_prop : Continuous (fun u => Real.exp (ν*u)))).intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (by simp)

lemma weightedCumulative_hasDerivAt {A x : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (ν : ℝ)
    (hx0 : x ≠ 0) (hxL : x ≠ -A) (hxR : x ≠ A) :
    HasDerivAt (weightedCumulative A ν (primitive A v))
      (Real.exp (ν*x)*zeroExtension A (primitive A v) x) x := by
  have hf := weighted_primitive_integrable hA hv
    (by fun_prop : Continuous (fun u => Real.exp (ν*u)))
  have heq : zeroExtension A (fun u => Real.exp (ν*u)*primitive A v u) =
      (fun u => Real.exp (ν*u)*zeroExtension A (primitive A v) u) := by
    funext u
    exact weighted_zeroExtension A ν (primitive A v) u
  have hc : ContinuousAt (zeroExtension A (fun u => Real.exp (ν*u)*primitive A v u)) x := by
    rw [heq]
    exact (by fun_prop : ContinuousAt (fun u => Real.exp (ν*u)) x).mul
      (zeroExtension_primitive_continuousAt hA hv hx0 hxL hxR)
  unfold weightedCumulative
  simpa only [weighted_zeroExtension] using
    intervalIntegral.integral_hasDerivAt_right (a := -A) (b := x) hf.intervalIntegrable
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hc

def exponentialEnergyFormula (A ν : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-ν*t)*weightedCumulative A ν w t
  +Real.exp (ν*t)*(weightedCumulative A (-ν) w A-weightedCumulative A (-ν) w t)

def exponentialFlux (A ν : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-ν*t)*weightedCumulative A ν w t
  -Real.exp (ν*t)*(weightedCumulative A (-ν) w A-weightedCumulative A (-ν) w t)

lemma exponentialFlux_ac {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (ν : ℝ) :
    AbsolutelyContinuousOnInterval (exponentialFlux A ν (primitive A v)) (-A) A := by
  have hp : AbsolutelyContinuousOnInterval (fun t => Real.exp (ν*t)) (-A) A := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hm : AbsolutelyContinuousOnInterval (fun t => Real.exp (-ν*t)) (-A) A := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hc : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => weightedCumulative A (-ν) (primitive A v) A) (-A) A := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  exact (hm.fun_mul (weightedCumulative_ac hA hv ν)).fun_sub
    (hp.fun_mul (hc.fun_sub (weightedCumulative_ac hA hv (-ν))))

lemma exponentialFlux_hasDerivAt {A x : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (ν : ℝ)
    (hx0 : x ≠ 0) (hxL : x ≠ -A) (hxR : x ≠ A) :
    HasDerivAt (exponentialFlux A ν (primitive A v))
      (2*zeroExtension A (primitive A v) x
        -ν*exponentialEnergyFormula A ν (primitive A v) x) x := by
  have hp := weightedCumulative_hasDerivAt hA hv ν hx0 hxL hxR
  have hm := weightedCumulative_hasDerivAt hA hv (-ν) hx0 hxL hxR
  have hep := ((hasDerivAt_id x).const_mul ν).exp
  have hem := ((hasDerivAt_id x).const_mul (-ν)).exp
  have hc := hasDerivAt_const x (weightedCumulative A (-ν) (primitive A v) A)
  have hd := (hem.mul hp).sub (hep.mul (hc.sub hm))
  have he : Real.exp (-ν*x)*Real.exp (ν*x) = 1 := by
    rw [← Real.exp_add]
    simp only [show -ν*x+ν*x=0 by ring, Real.exp_zero]
  convert hd using 1
  · rfl
  · unfold exponentialEnergyFormula
    simp only [id_eq, Pi.sub_apply, mul_one, zero_sub]
    nlinarith [congrArg (fun r => r*zeroExtension A (primitive A v) x) he]

end RhAnchored
#print axioms RhAnchored.cumulative_primitive_lipschitz
#print axioms RhAnchored.zeroExtension_primitive_continuousAt
#print axioms RhAnchored.exponentialFlux_hasDerivAt
