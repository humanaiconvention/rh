import RhDilationPhysical001

/-! Exact square-norm isometries for the actual real dilation. Explicit L2
membership accompanies the physical norm statements. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhDilation
open RhAnchored

lemma dilate_square {r : ℝ} (hr : 0<r) (w : ℝ → ℝ) (t : ℝ) :
    (dilate r w t)^2=r⁻¹*(w (t/r))^2 := by
  simp only [dilate,mul_pow,inv_pow,Real.sq_sqrt hr.le]

lemma integral_square_dilate {r : ℝ} (hr : 0<r) (w : ℝ → ℝ) :
    (∫t:ℝ,(dilate r w t)^2)=∫t:ℝ,(w t)^2 := by
  simp_rw [dilate_square hr]
  rw [integral_const_mul,Measure.integral_comp_div (fun t:ℝ=>(w t)^2) r]
  simp only [smul_eq_mul,abs_of_pos hr]
  field_simp

lemma dilate_square_integrable {r : ℝ} (hr : 0<r) {w : ℝ → ℝ}
    (hw : MemLp w 2 volume) : Integrable (fun t:ℝ=>(dilate r w t)^2) :=
  (dilate_memLp hr hw).integrable_sq

lemma zeroExtension_square_integral (A : ℝ) (w : ℝ → ℝ) :
    (∫t:ℝ,(zeroExtension A w t)^2)=∫t in interval A,(w t)^2 := by
  calc
    _ = ∫t:ℝ,(interval A).indicator (fun t:ℝ=>(w t)^2) t := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t=>by
        by_cases ht : t∈interval A <;> simp [zeroExtension,ht])
    _ = _ := integral_indicator measurableSet_Icc

/-- The exact interval square-norm isometry, with genuine physical L2
membership. It does not assert that x↦r*x preserves volume. -/
theorem physical_square_isometry {r A : ℝ} (hr : 0<r) {w : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure A)) :
    (∫t in interval (r*A),(dilate r w t)^2)=∫t in interval A,(w t)^2 := by
  calc
    _ = ∫t:ℝ,(zeroExtension (r*A) (dilate r w) t)^2 :=
      (zeroExtension_square_integral (r*A) (dilate r w)).symm
    _ = ∫t:ℝ,(dilate r (zeroExtension A w) t)^2 := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t=>by dsimp only; rw [zeroExtension_dilate hr])
    _ = ∫t:ℝ,(zeroExtension A w t)^2 := integral_square_dilate hr _
    _ = _ := zeroExtension_square_integral A w

lemma dilate_pullback {r : ℝ} (hr : 0<r) (v : ℝ → ℝ) (t : ℝ) :
    dilate r (pullback r v) t=r*v t := by
  unfold dilate pullback
  rw [show r*(t/r)=t by field_simp]
  have hs : Real.sqrt r≠0 := (Real.sqrt_pos.2 hr).ne'
  field_simp

/-- Physical input norm scaling is r^2; primitive dilation itself is unitary. -/
theorem pullback_square_norm {r A : ℝ} (hr : 0<r) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure (r*A))) :
    (∫x in interval A,(pullback r v x)^2)=r^2*(∫t in interval (r*A),(v t)^2) := by
  calc
    _ = ∫t in interval (r*A),(dilate r (pullback r v) t)^2 :=
      (physical_square_isometry hr (pullback_memLp hr hv)).symm
    _ = ∫t in interval (r*A),r^2*(v t)^2 := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t=>by dsimp only; rw [dilate_pullback hr];ring)
    _ = _ := integral_const_mul _ _

/-- The actual anchored primitive has exactly the same square norm after
pullback, with both half-line traces and the jump retained. -/
theorem primitive_square_pullback {r A : ℝ} (hr : 0<r) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure (r*A))) :
    (∫x in interval A,(primitive A (pullback r v) x)^2)=
      ∫t in interval (r*A),(primitive (r*A) v t)^2 := by
  have h := physical_square_isometry hr (primitive_memLp (pullback_memLp hr hv))
  simp_rw [dilate_primitive_pullback hr] at h
  exact h.symm

end RhDilation
#print axioms RhDilation.integral_square_dilate
#print axioms RhDilation.dilate_square_integrable
#print axioms RhDilation.physical_square_isometry
#print axioms RhDilation.pullback_square_norm
#print axioms RhDilation.primitive_square_pullback


