import RhActualComplexCore001

/-! Literal complex Bochner-integral dictionary for the actual componentwise
anchored primitive. No component formula is merely assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval
namespace RhComplexAnchoredIntegral
open RhAnchored RhActualComplexCore

/-- The native physical zero extension for complex inputs. -/
def complexZeroExtension (R : ℝ) (v : ℝ → ℂ) : ℝ → ℂ := (interval R).indicator v

lemma complexZeroExtension_components (R : ℝ) (v : ℝ → ℂ) :
    complexZeroExtension R v = fun t =>
      (zeroExtension R (fun x => (v x).re) t : ℂ) +
        Complex.I * (zeroExtension R (fun x => (v x).im) t : ℂ) := by
  funext t
  by_cases ht : t ∈ interval R
  · simp only [complexZeroExtension, indicator_of_mem ht, zeroExtension_eq ht]
    simpa only [mul_comm] using (Complex.re_add_im (v t)).symm
  · simp [complexZeroExtension, zeroExtension, ht]

lemma complexZeroExtension_integrable {R : ℝ} {v : ℝ → ℂ}
    (hv : MemLp v 2 (physicalMeasure R)) : Integrable (complexZeroExtension R v) := by
  have hi : IntegrableOn v (interval R) := hv.integrable (by norm_num)
  exact (integrable_indicator_iff measurableSet_Icc).mpr hi

lemma interval_integral_components {R : ℝ} {v : ℝ → ℂ}
    (hv : MemLp v 2 (physicalMeasure R)) (a b : ℝ) :
    (∫ t in a..b, complexZeroExtension R v t) =
      ((∫ t in a..b, zeroExtension R (fun x => (v x).re) t : ℝ) : ℂ) +
        Complex.I * ((∫ t in a..b, zeroExtension R (fun x => (v x).im) t : ℝ) : ℂ) := by
  have hvr : MemLp (fun t => (v t).re) 2 (physicalMeasure R) := by
    simpa only [RCLike.re_eq_complex_re] using hv.re
  have hvi : MemLp (fun t => (v t).im) 2 (physicalMeasure R) := by
    simpa only [RCLike.im_eq_complex_im] using hv.im
  have hr : IntervalIntegrable (fun t => (zeroExtension R (fun x => (v x).re) t : ℂ)) volume a b :=
    (zeroExtension_integrable hvr).ofReal.intervalIntegrable
  have hi : IntervalIntegrable (fun t => Complex.I * (zeroExtension R (fun x => (v x).im) t : ℂ)) volume a b :=
    ((zeroExtension_integrable hvi).ofReal.const_mul Complex.I).intervalIntegrable
  rw [complexZeroExtension_components, intervalIntegral.integral_add hr hi,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]

/-- Explicit complex anchored integral with both one-sided traces retained. -/
def anchoredIntegral (R : ℝ) (v : ℝ → ℂ) (t : ℝ) : ℂ :=
  if t < 0 then ∫ u in (-R)..t, complexZeroExtension R v u
  else if 0 < t then ∫ u in R..t, complexZeroExtension R v u else 0

/-- The actual complex weighted primitive is precisely the ordinary complex
Bochner anchored integral, including its saved value at zero. -/
theorem complexPrimitive_eq_anchoredIntegral {R : ℝ} {v : ℝ → ℂ}
    (hv : MemLp v 2 (physicalMeasure R)) (t : ℝ) :
    complexPrimitive R v t = anchoredIntegral R v t := by
  by_cases ht : t < 0
  · simp only [complexPrimitive, primitive_eq_left _ ht, anchoredIntegral, if_pos ht,
      leftPrimitive]
    exact (interval_integral_components hv (-R) t).symm
  · by_cases ht' : 0 < t
    · simp only [complexPrimitive, primitive_eq_right _ ht', anchoredIntegral, if_neg ht,
        if_pos ht', rightPrimitive]
      exact (interval_integral_components hv R t).symm
    · have hz : t = 0 := by linarith
      subst t
      simp [complexPrimitive, anchoredIntegral, primitive_zero]

end RhComplexAnchoredIntegral
#print axioms RhComplexAnchoredIntegral.complexZeroExtension_components
#print axioms RhComplexAnchoredIntegral.complexZeroExtension_integrable
#print axioms RhComplexAnchoredIntegral.interval_integral_components
#print axioms RhComplexAnchoredIntegral.complexPrimitive_eq_anchoredIntegral
