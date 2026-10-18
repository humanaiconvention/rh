import RhAnchoredConvolution001

/-!
The first-window shift geometry is partitioned at A-L and L-A. Derivatives
are proved on the three open cells; the two trace locations are handled
separately. No derivative of the primitive is asserted at a support boundary.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

def shiftFlux (A L : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  leftPrimitive A w (t-L)+leftPrimitive A w (t+L)
    -leftPrimitive A w (-L)-leftPrimitive A w L

def shiftLeftCell (A L : ℝ) : Set ℝ := Ioo (-A) (A-L)
def shiftMiddleCell (A L : ℝ) : Set ℝ := Ioo (A-L) (L-A)
def shiftRightCell (A L : ℝ) : Set ℝ := Ioo (L-A) A

lemma cumulative_zero_before {A x : ℝ} (w : ℝ → ℝ) (hx : x ≤ -A) :
    leftPrimitive A w x = 0 := by
  unfold leftPrimitive
  calc
    _ = ∫ u in (-A)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_uIoo
      intro u hu
      rw [uIoo_of_ge hx] at hu
      exact zeroExtension_eq_zero (by intro huI; linarith [hu.2, huI.1])
    _ = 0 := by simp

lemma cumulative_mass_after {A x : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (hx : A ≤ x) :
    leftPrimitive A (primitive A v) x = totalMass A (primitive A v) := by
  have hz : (∫ u in A..x, zeroExtension A (primitive A v) u) = 0 := by
    calc
      _ = ∫ u in A..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        intro u hu
        rw [uIoo_of_le hx] at hu
        exact zeroExtension_eq_zero (by intro huI; linarith [hu.1, huI.2])
      _ = 0 := by simp
  have h := intervalIntegral.integral_add_adjacent_intervals
    (zeroExtension_integrable (primitive_memLp hv)).intervalIntegrable
    (zeroExtension_integrable (primitive_memLp hv)).intervalIntegrable
      (a := -A) (b := A) (c := x)
  rw [hz, add_zero, interval_zeroExtension_mass hA (primitive A v)] at h
  exact h.symm

lemma cumulative_primitive_hasDerivAt {A x : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (hx0 : x ≠ 0) (hxL : x ≠ -A) (hxR : x ≠ A) :
    HasDerivAt (leftPrimitive A (primitive A v)) (zeroExtension A (primitive A v) x) x := by
  have h := weightedCumulative_hasDerivAt hA hv 0 hx0 hxL hxR
  unfold weightedCumulative at h
  unfold leftPrimitive
  simpa only [zero_mul, Real.exp_zero, one_mul] using h

lemma cumulative_shift_ac {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (d : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => leftPrimitive A (primitive A v) (t+d)) (-A) A := by
  have h := (cumulative_primitive_lipschitz hv).comp_absolutelyContinuousOnInterval
    (affine_ac 1 d (-A) A)
  simpa only [Function.comp_def, one_mul, add_comm] using h

lemma shiftFlux_ac {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (L : ℝ) :
    AbsolutelyContinuousOnInterval (shiftFlux A L (primitive A v)) (-A) A := by
  have hm := cumulative_shift_ac hv (-L)
  have hp := cumulative_shift_ac hv L
  have hc1 : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => leftPrimitive A (primitive A v) (-L)) (-A) A := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hc2 : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => leftPrimitive A (primitive A v) L) (-A) A := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  unfold shiftFlux
  simpa only [sub_eq_add_neg] using ((hm.fun_add hp).fun_sub hc1).fun_sub hc2

lemma shiftFlux_zero (A L : ℝ) (w : ℝ → ℝ) : shiftFlux A L w 0 = 0 := by
  simp [shiftFlux]

lemma shiftFlux_zero_middle {A L t : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A))
    (ht : t ∈ Icc (A-L) (L-A)) : shiftFlux A L (primitive A v) t = 0 := by
  rcases ht with ⟨htL, htR⟩
  unfold shiftFlux
  rw [cumulative_zero_before _ (by linarith : t-L ≤ -A),
    cumulative_mass_after hA hv (by linarith : A ≤ t+L),
    cumulative_zero_before _ (by linarith : -L ≤ -A),
    cumulative_mass_after hA hv hAL.le]
  ring

lemma primeShift_left {A L t : ℝ} (hAL : A < L) {v : ℝ → ℝ}
    (ht : t ∈ shiftLeftCell A L) :
    primeShift A L (primitive A v) t = primitive A v (t+L) := by
  have hp : t+L ∈ interval A := by constructor <;> linarith [ht.1, ht.2]
  have hm : t-L ∉ interval A := by intro hm; linarith [ht.2, hm.1]
  simp only [primeShift, zeroExtension_eq hp, zeroExtension_eq_zero hm, add_zero]

lemma primeShift_middle {A L t : ℝ} {w : ℝ → ℝ}
    (ht : t ∈ shiftMiddleCell A L) : primeShift A L w t = 0 := by
  have hp : t+L ∉ interval A := by intro hp; linarith [ht.1, hp.2]
  have hm : t-L ∉ interval A := by intro hm; linarith [ht.2, hm.1]
  simp only [primeShift, zeroExtension_eq_zero hp, zeroExtension_eq_zero hm, add_zero]

lemma primeShift_right {A L t : ℝ} (hAL : A < L) {v : ℝ → ℝ}
    (ht : t ∈ shiftRightCell A L) :
    primeShift A L (primitive A v) t = primitive A v (t-L) := by
  have hp : t+L ∉ interval A := by intro hp; linarith [ht.1, hp.2]
  have hm : t-L ∈ interval A := by constructor <;> linarith [ht.1, ht.2]
  simp only [primeShift, zeroExtension_eq_zero hp, zeroExtension_eq hm, zero_add]

lemma shiftFlux_hasDerivAt_regular {A L t : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A))
    (hm0 : t-L ≠ 0) (hmL : t-L ≠ -A) (hmR : t-L ≠ A)
    (hp0 : t+L ≠ 0) (hpL : t+L ≠ -A) (hpR : t+L ≠ A) :
    HasDerivAt (shiftFlux A L (primitive A v)) (primeShift A L (primitive A v) t) t := by
  have hm := (cumulative_primitive_hasDerivAt hA hv hm0 hmL hmR).comp t
    ((hasDerivAt_id t).sub_const L)
  have hp := (cumulative_primitive_hasDerivAt hA hv hp0 hpL hpR).comp t
    ((hasDerivAt_id t).add_const L)
  have hc1 := hasDerivAt_const t (leftPrimitive A (primitive A v) (-L))
  have hc2 := hasDerivAt_const t (leftPrimitive A (primitive A v) L)
  have hd := ((hm.add hp).sub hc1).sub hc2
  simp only [Function.comp_def, id_eq, mul_one, sub_zero] at hd
  unfold shiftFlux
  convert hd using 1
  unfold primeShift
  ring

theorem shiftFlux_hasDerivAt_left {A L t : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (ht : t ∈ shiftLeftCell A L) :
    HasDerivAt (shiftFlux A L (primitive A v)) (primitive A v (t+L)) t := by
  rw [← primeShift_left hAL ht]
  apply shiftFlux_hasDerivAt_regular hA hv <;>
    (intro he; linarith [ht.1, ht.2])

theorem shiftFlux_hasDerivAt_middle {A L t : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (ht : t ∈ shiftMiddleCell A L) :
    HasDerivAt (shiftFlux A L (primitive A v)) 0 t := by
  rw [← primeShift_middle (w := primitive A v) ht]
  apply shiftFlux_hasDerivAt_regular hA hv <;>
    (intro he; linarith [ht.1, ht.2])

theorem shiftFlux_hasDerivAt_right {A L t : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (ht : t ∈ shiftRightCell A L) :
    HasDerivAt (shiftFlux A L (primitive A v)) (primitive A v (t-L)) t := by
  rw [← primeShift_right hAL ht]
  apply shiftFlux_hasDerivAt_regular hA hv <;>
    (intro he; linarith [ht.1, ht.2])

end RhAnchored
#print axioms RhAnchored.shiftFlux_ac
#print axioms RhAnchored.shiftFlux_zero_middle
#print axioms RhAnchored.shiftFlux_hasDerivAt_left
#print axioms RhAnchored.shiftFlux_hasDerivAt_middle
#print axioms RhAnchored.shiftFlux_hasDerivAt_right
