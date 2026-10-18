import RhAnchoredSignedConvolution001
import RhAnchoredCumulativeLedger001

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

lemma primitive_weight_integrable {A : ℝ} (hA : 0 < A) {v g : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (hg : Continuous g) :
    Integrable (fun u => g u*primitive A v u) (physicalMeasure A) := by
  exact (integrable_indicator_iff measurableSet_Icc).1 (weighted_primitive_integrable hA hv hg)

lemma orientation_weight_integrable {A : ℝ} (hA : 0 < A) {v g : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (hg : Continuous g) (t : ℝ) :
    Integrable (fun u => orientation (t-u)*g u*primitive A v u) (physicalMeasure A) := by
  apply (primitive_weight_integrable hA hv hg).mono
  · exact (((orientation_measurable.comp (by fun_prop : Measurable (fun u : ℝ => t-u))).mul
      hg.measurable).mul (primitive_measurable hv)).aestronglyMeasurable
  · exact Eventually.of_forall (fun u => by simp only [norm_mul, orientation_norm, one_mul]; rfl)

lemma orientation_product_integrable {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (t : ℝ) :
    Integrable (fun u => orientation (t-u)*primitive A v u) (physicalMeasure A) := by
  simpa only [mul_one] using orientation_weight_integrable hA hv
    (g := fun _ => (1 : ℝ)) continuous_const t

lemma signedExponential_product_integrable {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (ν t : ℝ) :
    Integrable (fun u => orientation (t-u)*Real.exp (-ν*|t-u|)*primitive A v u)
      (physicalMeasure A) := orientation_weight_integrable hA hv (by fun_prop) t

lemma hinge_product_integrable {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (L t : ℝ) :
    Integrable (fun u => hingeSlope L (t-u)*primitive A v u) (physicalMeasure A) := by
  have h : Integrable (fun u => (Iic (t-L)).indicator (primitive A v) u+
      (Iic (t+L)).indicator (primitive A v) u-primitive A v u) (physicalMeasure A) :=
    ((headMass_integrable hv (t-L)).add (headMass_integrable hv (t+L))).sub (primitive_integrableOn hv)
  apply h.congr
  exact Eventually.of_forall (fun u => (hingeSlope_integrand L t u (primitive A v)).symm)

def orientationConvolution (A : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in interval A, orientation (t-u)*w u

lemma orientation_integrand (t u : ℝ) (w : ℝ → ℝ) :
    orientation (t-u)*w u=2*(Iic t).indicator w u-w u := by
  by_cases hu : u ≤ t
  · simp only [orientation, ite_eq_right (not_lt.mpr (sub_nonneg.mpr hu)),
      indicator_of_mem (show u ∈ Iic t from hu)]
    ring
  · simp only [orientation, ite_eq_left (sub_neg.mpr (lt_of_not_ge hu)),
      indicator_of_notMem (show u ∉ Iic t from hu)]
    ring

theorem orientationConvolution_eq_cumulative {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (t : ℝ) :
    orientationConvolution A (primitive A v) t =
      2*leftPrimitive A (primitive A v) t-totalMass A (primitive A v) := by
  unfold orientationConvolution
  simp_rw [orientation_integrand]
  change (∫ u, 2*(Iic t).indicator (primitive A v) u-primitive A v u ∂physicalMeasure A) = _
  have h : Integrable (fun u => 2*(Iic t).indicator (primitive A v) u) (physicalMeasure A) :=
    (headMass_integrable hv t).const_mul 2
  rw [integral_sub h (primitive_integrableOn hv), integral_const_mul]
  change 2*headMass A (primitive A v) t-totalMass A (primitive A v) = _
  rw [headMass_eq_cumulative hA hv]

lemma orientationConvolution_difference {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (t : ℝ) :
    orientationConvolution A (primitive A v) t-orientationConvolution A (primitive A v) 0 =
      2*(leftPrimitive A (primitive A v) t-leftPrimitive A (primitive A v) 0) := by
  rw [orientationConvolution_eq_cumulative hA hv, orientationConvolution_eq_cumulative hA hv]
  ring

end RhAnchored
#print axioms RhAnchored.orientationConvolution_eq_cumulative
#print axioms RhAnchored.hinge_product_integrable
