import RhAnchoredPotentialSlope001
import RhAnchoredOrientation001
import RhAnchoredNativeFlux001
import RhAnchoredSchurInterface001

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

def potentialSlopeConvolution (A C α L : ℝ) (J : ℕ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in interval A, finitePotentialSlope C α L J (t-u)*w u

lemma finitePotentialSlope_mul (C α L : ℝ) (J : ℕ) (t u : ℝ) (w : ℝ → ℝ) :
    finitePotentialSlope C α L J (t-u)*w u =
      (-4)*(Real.sinh ((t-u)/2)*w u)+(C/2)*(orientation (t-u)*w u)
      -(∑ k ∈ Finset.range J, (beta k)⁻¹*
        (orientation (t-u)*Real.exp (-(beta k)*|t-u|)*w u))
      +α*(hingeSlope L (t-u)*w u) := by
  have hs : (∑ k ∈ Finset.range J,
      (beta k)⁻¹*orientation (t-u)*Real.exp (-(beta k)*|t-u|))*w u =
      ∑ k ∈ Finset.range J,
        (beta k)⁻¹*(orientation (t-u)*Real.exp (-(beta k)*|t-u|)*w u) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold finitePotentialSlope
  rw [add_mul, sub_mul, add_mul, hs]
  ring

lemma potentialSlope_product_integrable {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α L : ℝ) (J : ℕ) (t : ℝ) :
    Integrable (fun u => finitePotentialSlope C α L J (t-u)*primitive A v u)
      (physicalMeasure A) := by
  have hh : Integrable (fun u => (-4)*(Real.sinh ((t-u)/2)*primitive A v u))
      (physicalMeasure A) := (primitive_weight_integrable hA hv (by fun_prop)).const_mul (-4)
  have ho := (orientation_product_integrable hA hv t).const_mul (C/2)
  have he : ∀ k ∈ Finset.range J, Integrable
      (fun u => (beta k)⁻¹*(orientation (t-u)*Real.exp (-(beta k)*|t-u|)*primitive A v u))
      (physicalMeasure A) := fun k _ => (signedExponential_product_integrable hA hv (beta k) t).const_mul _
  have hs := integrable_finsetSum (Finset.range J) he
  have hp := (hinge_product_integrable hv L t).const_mul α
  have hc := ((hh.add ho).sub hs).add hp
  apply hc.congr
  exact Eventually.of_forall (fun u => (finitePotentialSlope_mul C α L J t u (primitive A v)).symm)

theorem potentialSlopeConvolution_expansion {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α L : ℝ) (J : ℕ) (t : ℝ) :
    potentialSlopeConvolution A C α L J (primitive A v) t =
      -4*Real.sinh (t/2)*(∫ u in interval A, Real.cosh (u/2)*primitive A v u)
      +4*Real.cosh (t/2)*(∫ u in interval A, Real.sinh (u/2)*primitive A v u)
      +(C/2)*orientationConvolution A (primitive A v) t
      -(∑ k ∈ Finset.range J, (beta k)⁻¹*signedExponentialOperator A (beta k) (primitive A v) t)
      +α*hingeConvolution A L (primitive A v) t := by
  have hc := primitive_weight_integrable hA hv (by fun_prop : Continuous (fun u => Real.cosh (u/2)))
  have hs := primitive_weight_integrable hA hv (by fun_prop : Continuous (fun u => Real.sinh (u/2)))
  have hphase : (∫ u in interval A, Real.sinh ((t-u)/2)*primitive A v u) =
      Real.sinh (t/2)*(∫ u in interval A, Real.cosh (u/2)*primitive A v u)
      -Real.cosh (t/2)*(∫ u in interval A, Real.sinh (u/2)*primitive A v u) := by
    simp_rw [sub_div, Real.sinh_sub, sub_mul, mul_assoc]
    change (∫ u, Real.sinh (t/2)*(Real.cosh (u/2)*primitive A v u)-
      Real.cosh (t/2)*(Real.sinh (u/2)*primitive A v u) ∂physicalMeasure A) = _
    rw [integral_sub (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul]
    rfl
  have hh : Integrable (fun u => (-4)*(Real.sinh ((t-u)/2)*primitive A v u))
      (physicalMeasure A) := (primitive_weight_integrable hA hv (by fun_prop)).const_mul (-4)
  have ho : Integrable (fun u => (C/2)*(orientation (t-u)*primitive A v u))
      (physicalMeasure A) := (orientation_product_integrable hA hv t).const_mul (C/2)
  have he : ∀ k ∈ Finset.range J, Integrable
      (fun u => (beta k)⁻¹*(orientation (t-u)*Real.exp (-(beta k)*|t-u|)*primitive A v u))
      (physicalMeasure A) := fun k _ => (signedExponential_product_integrable hA hv (beta k) t).const_mul _
  have hsum : Integrable (fun u => ∑ k ∈ Finset.range J, (beta k)⁻¹*
      (orientation (t-u)*Real.exp (-(beta k)*|t-u|)*primitive A v u)) (physicalMeasure A) :=
    integrable_finsetSum (Finset.range J) he
  have hp : Integrable (fun u => α*(hingeSlope L (t-u)*primitive A v u))
      (physicalMeasure A) := (hinge_product_integrable hv L t).const_mul α
  unfold potentialSlopeConvolution
  simp_rw [finitePotentialSlope_mul]
  change (∫ u, (-4)*(Real.sinh ((t-u)/2)*primitive A v u)+
      (C/2)*(orientation (t-u)*primitive A v u)-
      (∑ k ∈ Finset.range J, (beta k)⁻¹*
        (orientation (t-u)*Real.exp (-(beta k)*|t-u|)*primitive A v u))+
      α*(hingeSlope L (t-u)*primitive A v u) ∂physicalMeasure A) = _
  have hadd := integral_add ((hh.add ho).sub hsum) hp
  have hsub := integral_sub (hh.add ho) hsum
  have hadd' := integral_add hh ho
  simp only [Pi.add_apply, Pi.sub_apply] at hadd hsub hadd'
  rw [hadd, hsub, hadd', integral_finsetSum (Finset.range J) he]
  simp_rw [integral_const_mul]
  change (-4)*(∫ u in interval A, Real.sinh ((t-u)/2)*primitive A v u)+
    (C/2)*orientationConvolution A (primitive A v) t-
    (∑ k ∈ Finset.range J, (beta k)⁻¹*signedExponentialOperator A (beta k) (primitive A v) t)+
    α*hingeConvolution A L (primitive A v) t = _
  rw [hphase]
  ring

theorem firstFlux_eq_slope_difference {A L : ℝ} (hA : 0 < A) (hL : 0 < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) (J : ℕ) (t : ℝ) :
    firstFlux A C α L J (primitive A v) t =
      potentialSlopeConvolution A C α L J (primitive A v) t-
      potentialSlopeConvolution A C α L J (primitive A v) 0 := by
  have h1 := potentialSlope_product_integrable hA hv C α L J t
  have h0 : Integrable (fun u => finitePotentialSlope C α L J (-u)*primitive A v u)
      (physicalMeasure A) := by
    simpa only [zero_sub] using potentialSlope_product_integrable hA hv C α L J 0
  have he : (∫ u in interval A, primitive A v u*deriv (fun y => finiteKernel C α L J t y) u) =
      ∫ u in interval A, -(finitePotentialSlope C α L J (t-u)*primitive A v u)+
        finitePotentialSlope C α L J (-u)*primitive A v u := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (finiteKernel_section_ae_deriv hL C α J t)] with u hu
    simp only [hu]
    ring
  unfold firstFlux
  rw [he]
  change -(∫ u, -(finitePotentialSlope C α L J (t-u)*primitive A v u)+
      finitePotentialSlope C α L J (-u)*primitive A v u ∂physicalMeasure A) = _
  have hadd := integral_add h1.neg h0
  simp only [Pi.add_apply, Pi.neg_apply] at hadd
  rw [hadd, integral_neg]
  unfold potentialSlopeConvolution
  simp only [zero_sub]
  unfold physicalMeasure
  ring

theorem firstFlux_eq_nativeFlux {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) (J : ℕ) (t : ℝ) :
    firstFlux A C α L J (primitive A v) t=nativeFlux A C α L J (primitive A v) t := by
  rw [firstFlux_eq_slope_difference hA (lt_trans hA hAL) hv,
    potentialSlopeConvolution_expansion hA hv, potentialSlopeConvolution_expansion hA hv]
  have h0 : hingeConvolution A L (primitive A v) 0=0 := by
    rw [hingeConvolution_eq_shiftFlux hA hAL hv, shiftFlux_zero]
  have ho := orientationConvolution_difference hA hv t
  have hs : (∑ k ∈ Finset.range J, (beta k)⁻¹*
      (signedExponentialOperator A (beta k) (primitive A v) t-
       signedExponentialOperator A (beta k) (primitive A v) 0)) =
      (∑ k ∈ Finset.range J, (beta k)⁻¹*signedExponentialOperator A (beta k) (primitive A v) t)-
      (∑ k ∈ Finset.range J, (beta k)⁻¹*signedExponentialOperator A (beta k) (primitive A v) 0) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  unfold nativeFlux rankFlux
  rw [hs]
  simp only [zero_div, Real.sinh_zero, Real.cosh_zero, h0]
  linear_combination (C/2)*ho

end RhAnchored
#print axioms RhAnchored.potentialSlope_product_integrable
#print axioms RhAnchored.firstFlux_eq_nativeFlux
