import RhAnchoredWeak001

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace RhAnchored

lemma intervalPrimitive_norm_le {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (a b : ℝ) :
    ‖∫ t in a..b, zeroExtension A v t‖ ≤ ∫ t, ‖zeroExtension A v t‖ := by
  exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
    (setIntegral_le_integral (zeroExtension_integrable hv).norm
      (Eventually.of_forall fun _ => norm_nonneg _))

lemma primitive_norm_le {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (t : ℝ) :
    ‖primitive A v t‖ ≤ ∫ u, ‖zeroExtension A v u‖ := by
  by_cases ht : t < 0
  · rw [primitive_eq_left v ht]
    exact intervalPrimitive_norm_le hv _ _
  · by_cases ht' : 0 < t
    · rw [primitive_eq_right v ht']
      exact intervalPrimitive_norm_le hv _ _
    · simp only [primitive, ite_eq_right ht, ite_eq_right ht', norm_zero]
      exact integral_nonneg (fun _ => norm_nonneg _)

lemma primitive_measurable {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) : Measurable (primitive A v) := by
  exact (leftPrimitive_continuous hv).measurable.piecewise measurableSet_Iio
    ((rightPrimitive_continuous hv).measurable.piecewise measurableSet_Ioi measurable_const)

lemma primitive_memLp {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) :
    MemLp (primitive A v) 2 (physicalMeasure A) := by
  exact MemLp.of_bound (primitive_measurable hv).aestronglyMeasurable
    (∫ u, ‖zeroExtension A v u‖) (Eventually.of_forall (primitive_norm_le hv))

lemma primitive_integrableOn {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) : IntegrableOn (primitive A v) (interval A) := by
  exact (primitive_memLp hv).integrable (by norm_num)

lemma primitive_parts_setIntegral {A : ℝ} (hA : 0 < A) {v φ : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A))
    (hφ : AbsolutelyContinuousOnInterval φ (-A) A) :
    (∫ t in interval A, primitive A v t * deriv φ t) =
    -(∫ t in interval A, v t * φ t) + totalMass A v * φ 0 := by
  have h := primitive_weak_derivative hA hv hφ
  rw [intervalIntegral.integral_of_le (by linarith : -A ≤ A),
    ← integral_Icc_eq_integral_Ioc] at h
  rw [intervalIntegral.integral_of_le (by linarith : -A ≤ A),
    ← integral_Icc_eq_integral_Ioc] at h
  change (∫ t in interval A, primitive A v t * deriv φ t) =
    -(∫ t in interval A, zeroExtension A v t * φ t)+totalMass A v*φ 0 at h
  have heq : (∫ t in interval A, zeroExtension A v t * φ t) =
      ∫ t in interval A, v t * φ t := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    simp only [zeroExtension_eq ht]
  rw [heq] at h
  exact h

theorem primitive_parts_setIntegral_anchored {A : ℝ} (hA : 0 < A) {v φ : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A))
    (hφ : AbsolutelyContinuousOnInterval φ (-A) A) (hzero : φ 0 = 0) :
    (∫ t in interval A, v t * φ t) =
    -(∫ t in interval A, primitive A v t * deriv φ t) := by
  have h := primitive_parts_setIntegral hA hv hφ
  rw [hzero] at h
  linarith

def primitiveLp (A : ℝ) (v : PhysicalSpace A) : PhysicalSpace A :=
  (primitive_memLp (Lp.memLp v)).toLp (primitive A v)

end RhAnchored
#print axioms RhAnchored.primitive_memLp
#print axioms RhAnchored.primitive_parts_setIntegral_anchored
