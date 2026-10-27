import JensenGaussianMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! UNCOMPILED preparation only. No new theorem or axiom report is accepted.
New even-moment helpers are inline; import the accepted Gaussian, kernel and
weight objects from their existing authenticated directories. -/


/-!
# Even moments from the accepted Gaussian domination

UNCOMPILED PREPARATION ONLY. No compiler allocation, proof acceptance or
actual axiom report is asserted by this file. `JensenGaussianMeasure` is an
accepted dependency, imported from its authenticated object directory.

The exact coefficient is `(j.factorial : ℝ) / b ^ j`. In particular the
zeroth moment and the zero measure are included. No infinite interchange,
signed-measure/Jordan identification, or actual-source Gaussian theorem is
claimed here.
-/

noncomputable section

open MeasureTheory
open SignedJensenMeasurePrep

namespace SignedJensenMomentsPrep

/-- The real nonnegative even-power integrand; the exponent includes `j = 0`. -/
def evenPower (j : ℕ) (u : U) : ℝ := (u : ℝ) ^ (2 * j)

theorem evenPower_nonneg (j : ℕ) (u : U) : 0 ≤ evenPower j u := by
  exact pow_nonneg u.property _

/-- A single nonnegative term of the real exponential series pays the
entire even power, without replacing the exact factorial constant. -/
theorem evenPower_le_gaussian (b : ℝ) (j : ℕ) (hb : 0 < b) (u : U) :
    evenPower j u ≤ ((j.factorial : ℝ) / b ^ j) * gaussian b u := by
  have hx : 0 ≤ b * (u : ℝ) ^ 2 := by positivity
  have hfac : 0 < (j.factorial : ℝ) := by positivity
  have hbpow : 0 < b ^ j := pow_pos hb j
  have hterm := Real.pow_div_factorial_le_exp (b * (u : ℝ) ^ 2) hx j
  have hmul : (b * (u : ℝ) ^ 2) ^ j ≤
      Real.exp (b * (u : ℝ) ^ 2) * (j.factorial : ℝ) :=
    (div_le_iff₀ hfac).mp hterm
  have hmul' : b ^ j * (u : ℝ) ^ (2 * j) ≤
      Real.exp (b * (u : ℝ) ^ 2) * (j.factorial : ℝ) := by
    simpa only [mul_pow, ← pow_mul] using hmul
  change (u : ℝ) ^ (2 * j) ≤
    ((j.factorial : ℝ) / b ^ j) * Real.exp (b * (u : ℝ) ^ 2)
  calc
    (u : ℝ) ^ (2 * j) ≤
        (Real.exp (b * (u : ℝ) ^ 2) * (j.factorial : ℝ)) / b ^ j := by
      apply (le_div_iff₀ hbpow).2
      simpa only [mul_comm] using hmul'
    _ = ((j.factorial : ℝ) / b ^ j) * Real.exp (b * (u : ℝ) ^ 2) := by ring

/-- Actual Bochner integrability, not a finite numerical value assigned
to an integrand whose integrability has not been established. -/
theorem integrable_evenPower (μ : Measure U) (b : ℝ) (j : ℕ)
    (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    Integrable (evenPower j) μ := by
  apply (hG.const_mul ((j.factorial : ℝ) / b ^ j)).mono'
    (by unfold evenPower; fun_prop)
  apply Filter.Eventually.of_forall
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (evenPower_nonneg j u)]
  exact evenPower_le_gaussian b j hb u

/-- The real moment is nonnegative, including for the zero measure. -/
theorem integral_evenPower_nonneg (μ : Measure U) (j : ℕ) :
    0 ≤ ∫ u, evenPower j u ∂μ :=
  integral_nonneg (evenPower_nonneg j)

/-- Exact factorial/Gaussian moment bound, valid for every natural `j`.
`hG` supplies both sides' required actual integrability. -/
theorem integral_evenPower_le (μ : Measure U) (b : ℝ) (j : ℕ)
    (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    (∫ u, evenPower j u ∂μ) ≤
      ((j.factorial : ℝ) / b ^ j) * (∫ u, gaussian b u ∂μ) := by
  have hm := integrable_evenPower μ b j hb hG
  have hg := hG.const_mul ((j.factorial : ℝ) / b ^ j)
  calc
    (∫ u, evenPower j u ∂μ) ≤
        ∫ u, ((j.factorial : ℝ) / b ^ j) * gaussian b u ∂μ :=
      integral_mono hm hg (evenPower_le_gaussian b j hb)
    _ = ((j.factorial : ℝ) / b ^ j) * (∫ u, gaussian b u ∂μ) :=
      integral_const_mul _ _

end SignedJensenMomentsPrep

-- Requested audits for a future authorized launch, not actual reports.
#print axioms SignedJensenMomentsPrep.evenPower_le_gaussian
#print axioms SignedJensenMomentsPrep.integrable_evenPower
#print axioms SignedJensenMomentsPrep.integral_evenPower_nonneg
#print axioms SignedJensenMomentsPrep.integral_evenPower_le



/-!
# Finite moment-polynomial dictionary: uncompiled preparation

This file is a complete proposed proof script, not an accepted Lean theorem.
No compiler, admission check, or axiom audit has been run for this preparation.
Only finite sums are interchanged with integrals. Positive measures are not
asserted to be a Jordan pair, and no infinite moment-series identity is used.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SignedJensenMomentsPrep

open SignedJensenMeasurePrep

/-- The actual real signed even moment, with the two positive integrals
kept explicit. Integrability is established before this is used below. -/
def signedMoment (μp μm : Measure U) (j : ℕ) : ℝ :=
  (∫ u, evenPower j u ∂μp) - (∫ u, evenPower j u ∂μm)

/-- The original finite moment polynomial, including both endpoints of
the index set `0 ≤ j ≤ d`; in particular its constant term is retained. -/
def finiteMomentPolynomial (μp μm : Measure U) (d : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (d + 1),
    (-1 : ℂ) ^ j * (SignedJensenPrep.weight d j : ℂ) *
      (signedMoment μp μm j : ℂ) * z ^ j / ((2 * j).factorial : ℂ)

/-- A convenient constant coefficient for finite linearity only. Its
commutative reordering into the displayed polynomial is proved explicitly. -/
def momentCoefficient (d : ℕ) (z : ℂ) (j : ℕ) : ℂ :=
  (SignedJensenPrep.weight d j : ℂ) * (-1 : ℂ) ^ j * z ^ j /
    ((2 * j).factorial : ℂ)

theorem integrable_complex_evenPower (μ : Measure U) (b : ℝ) (j : ℕ)
    (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    Integrable (fun u => (evenPower j u : ℂ)) μ :=
  (integrable_evenPower μ b j hb hG).ofReal

/-- The scalar normalization uses the previously accepted kernel expansion,
with the real-to-complex even-power cast justified by `Complex.ofReal_pow`. -/
theorem weighted_kernelTerm_eq (d : ℕ) (z : ℂ) (j : ℕ) (u : U) :
    (SignedJensenPrep.weight d j : ℂ) *
        SignedJensenKernelPrep.kernelTerm (z * (u : ℂ) ^ 2) j =
      momentCoefficient d z j * (evenPower j u : ℂ) := by
  rw [SignedJensenKernelPrep.kernelTerm_native]
  simp only [momentCoefficient, evenPower, Complex.ofReal_pow]
  ring

theorem finiteNativeKernel_expansion (d : ℕ) (z : ℂ) (u : U) :
    finiteNativeKernel d z u =
      ∑ j ∈ Finset.range (d + 1),
        momentCoefficient d z j * (evenPower j u : ℂ) := by
  unfold finiteNativeKernel SignedJensenKernelPrep.finiteKernel
  apply Finset.sum_congr rfl
  intro j _
  exact weighted_kernelTerm_eq d z j u

/-- All monomials are genuinely integrable, including degree zero.
No finite-measure instance or positive-mass assumption is added. -/
theorem integrable_finiteNativeKernel_all_degrees (μ : Measure U)
    (b : ℝ) (d : ℕ) (z : ℂ) (hb : 0 < b)
    (hG : Integrable (gaussian b) μ) :
    Integrable (finiteNativeKernel d z) μ := by
  have hsum : Integrable (fun u => ∑ j ∈ Finset.range (d + 1),
      momentCoefficient d z j * (evenPower j u : ℂ)) μ := by
    apply integrable_finsetSum
    intro j _
    exact (integrable_complex_evenPower μ b j hb hG).const_mul _
  convert hsum using 1
  funext u
  exact finiteNativeKernel_expansion d z u

/-- Finite linearity with actual integrability hypotheses supplied before
the sum is moved. The complex cast is transferred by the pinned
`MeasureTheory.integral_complex_ofReal` API. -/
theorem integral_finiteNativeKernel (μ : Measure U) (b : ℝ) (d : ℕ)
    (z : ℂ) (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    (∫ u, finiteNativeKernel d z u ∂μ) =
      ∑ j ∈ Finset.range (d + 1),
        momentCoefficient d z j * ((∫ u, evenPower j u ∂μ) : ℂ) := by
  have hterms : ∀ j ∈ Finset.range (d + 1),
      Integrable (fun u => momentCoefficient d z j * (evenPower j u : ℂ)) μ := by
    intro j _
    exact (integrable_complex_evenPower μ b j hb hG).const_mul _
  simp_rw [finiteNativeKernel_expansion]
  rw [integral_finsetSum (Finset.range (d + 1)) hterms]
  simp only [integral_const_mul, integral_complex_ofReal]

/-- Exact finite moment-polynomial dictionary for every natural degree and
every complex parameter. The Gaussian hypothesis supplies all real moments
for both measures, including their constant moments. -/
theorem signedPair_finiteNativeKernel_eq (μp μm : Measure U) (b : ℝ)
    (d : ℕ) (z : ℂ) (hb : 0 < b)
    (hG : Integrable (gaussian b) (μp + μm)) :
    signedPair μp μm (finiteNativeKernel d z) =
      finiteMomentPolynomial μp μm d z := by
  unfold signedPair
  rw [integral_finiteNativeKernel μp b d z hb hG.left_of_add_measure,
    integral_finiteNativeKernel μm b d z hb hG.right_of_add_measure]
  unfold finiteMomentPolynomial
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [signedMoment, Complex.ofReal_sub, momentCoefficient, integral_complex_ofReal]
  ring

/-- Rewriting the accepted integrated kernel estimate changes neither the
actual polynomial nor its exact `1/24` constant. -/
theorem finiteMomentPolynomial_error (μp μm : Measure U) (b r : ℝ)
    (z : ℂ) (d : ℕ) (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r)
    (hd : 1 ≤ d) (hG : Integrable (gaussian b) (μp + μm)) :
    ‖finiteMomentPolynomial μp μm d z - signedPair μp μm (nativeKernel z)‖ ≤
      (r ^ 2 / (24 * (d : ℝ))) * (∫ u, fourthCosh r u ∂(μp + μm)) := by
  rw [← signedPair_finiteNativeKernel_eq μp μm b d z hb hG]
  exact signedPair_kernel_error μp μm b r z d hb hr hz hd hG

/-- Rewriting the accepted Gaussian estimate retains the exact `1/3`
coefficient. It is a finite-polynomial error theorem, not an infinite
moment-series interchange or an actual-source Gaussian-moment result. -/
theorem finiteMomentPolynomial_error_gaussian (μp μm : Measure U)
    (b r : ℝ) (z : ℂ) (d : ℕ) (hb : 0 < b) (hr : 0 ≤ r)
    (hz : ‖z‖ ≤ r) (hd : 1 ≤ d)
    (hG : Integrable (gaussian b) (μp + μm)) :
    ‖finiteMomentPolynomial μp μm d z - signedPair μp μm (nativeKernel z)‖ ≤
      ((r ^ 2 / (3 * b ^ 2 * (d : ℝ))) * Real.exp (r / (2 * b))) *
        (∫ u, gaussian b u ∂(μp + μm)) := by
  rw [← signedPair_finiteNativeKernel_eq μp μm b d z hb hG]
  exact signedPair_kernel_error_gaussian μp μm b r z d hb hr hz hd hG

end SignedJensenMomentsPrep

-- Requested future audits only: there is no compiler output for this draft.
#print axioms SignedJensenMomentsPrep.integrable_complex_evenPower
#print axioms SignedJensenMomentsPrep.weighted_kernelTerm_eq
#print axioms SignedJensenMomentsPrep.finiteNativeKernel_expansion
#print axioms SignedJensenMomentsPrep.integrable_finiteNativeKernel_all_degrees
#print axioms SignedJensenMomentsPrep.integral_finiteNativeKernel
#print axioms SignedJensenMomentsPrep.signedPair_finiteNativeKernel_eq
#print axioms SignedJensenMomentsPrep.finiteMomentPolynomial_error
#print axioms SignedJensenMomentsPrep.finiteMomentPolynomial_error_gaussian
