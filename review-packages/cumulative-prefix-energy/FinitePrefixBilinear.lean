import CumulativeSquareEnergy
import Mathlib.Tactic

/-!
A finite bilinear companion to the accepted cumulative square-energy theorem.
The coefficients in the two lists are arbitrary real numbers, and both endpoint
companions remain. There is no prime arithmetic or infinite-window assertion.
Verification of this selected source is recorded in the collection build receipt.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace CumulativePrefixBilinear
open CumulativeSquareEnergy

variable {ι : Type*}

theorem prefixMass_add (s : Finset ι) (p c e : ι → ℝ) (t : ℝ) :
    prefixMass s p (fun i => c i + e i) t =
      prefixMass s p c t + prefixMass s p e t := by
  unfold prefixMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : p i ≤ t <;> simp [h]

theorem weightedPrefix_add (s : Finset ι) (p c e : ι → ℝ) (t : ℝ) :
    weightedPrefix s p (fun i => c i + e i) t =
      weightedPrefix s p c t + weightedPrefix s p e t := by
  unfold weightedPrefix
  simp_rw [add_div]
  exact prefixMass_add s p _ _ t

theorem compensated_add (s : Finset ι) (p c e : ι → ℝ) (t : ℝ) :
    compensated s p (fun i => c i + e i) t =
      compensated s p c t + compensated s p e t := by
  unfold compensated
  rw [weightedPrefix_add, prefixMass_add, add_div]
  ring

/-- The mixed finite-prefix product is actually integrable; this is not an
extra hypothesis of the terminal energy theorem. -/
theorem prefixMass_mul_intervalIntegrable (s : Finset ι) (p c e : ι → ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable
      (fun t => prefixMass s p c t * prefixMass s p e t) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
  apply Measure.integrableOn_of_bounded (measure_Icc_lt_top.ne)
    ((prefixMass_measurable s p c).mul
      (prefixMass_measurable s p e)).aestronglyMeasurable
  filter_upwards with t
  change ‖prefixMass s p c t * prefixMass s p e t‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (prefixMass_norm_le s p c t)
    (prefixMass_norm_le s p e t) (norm_nonneg _)
    (Finset.sum_nonneg (fun i hi => norm_nonneg (c i)))

private theorem integral_square_add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable (fun t => f t ^ 2) volume a b)
    (hg : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : IntervalIntegrable (fun t => f t * g t) volume a b) :
    (∫ t in a..b, (f t + g t) ^ 2) =
      (∫ t in a..b, f t ^ 2) + 2 * (∫ t in a..b, f t * g t) +
        ∫ t in a..b, g t ^ 2 := by
  have heq : (fun t => (f t + g t) ^ 2) =
      fun t => (f t ^ 2 + 2 * (f t * g t)) + g t ^ 2 := by
    funext t
    ring
  rw [heq,
    intervalIntegral.integral_add (hf.add (hfg.const_mul 2)) hg,
    intervalIntegral.integral_add hf (hfg.const_mul 2),
    intervalIntegral.integral_const_mul]

private theorem integral_square_div_add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable (fun t => f t ^ 2 / t ^ 2) volume a b)
    (hg : IntervalIntegrable (fun t => g t ^ 2 / t ^ 2) volume a b)
    (hfg : IntervalIntegrable (fun t => f t * g t / t ^ 2) volume a b) :
    (∫ t in a..b, (f t + g t) ^ 2 / t ^ 2) =
      (∫ t in a..b, f t ^ 2 / t ^ 2) +
      2 * (∫ t in a..b, f t * g t / t ^ 2) +
        ∫ t in a..b, g t ^ 2 / t ^ 2 := by
  have heq : (fun t => (f t + g t) ^ 2 / t ^ 2) =
      fun t => (f t ^ 2 / t ^ 2 + 2 * (f t * g t / t ^ 2)) +
        g t ^ 2 / t ^ 2 := by
    funext t
    ring
  rw [heq,
    intervalIntegral.integral_add (hf.add (hfg.const_mul 2)) hg,
    intervalIntegral.integral_add hf (hfg.const_mul 2),
    intervalIntegral.integral_const_mul]

/-- Polarization of the actual finite-prefix energy identity. Both coefficient
lists are arbitrary, and no balance, orthogonality or zero-boundary assumption
is imposed. Sites may coincide, and either endpoint may be a jump. -/
theorem finite_prefix_bilinear_energy (s : Finset ι) (p c e : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, weightedPrefix s p c t * weightedPrefix s p e t) =
      b * compensated s p c b * compensated s p e b -
      a * compensated s p c a * compensated s p e a +
        ∫ t in a..b, prefixMass s p c t * prefixMass s p e t / t ^ 2 := by
  have hgc := prefixMass_sq_intervalIntegrable s p (fun i => c i / p i) hab
  have hge := prefixMass_sq_intervalIntegrable s p (fun i => e i / p i) hab
  have hgcge := prefixMass_mul_intervalIntegrable s p
    (fun i => c i / p i) (fun i => e i / p i) hab
  change IntervalIntegrable (fun t => weightedPrefix s p c t ^ 2) volume a b at hgc
  change IntervalIntegrable (fun t => weightedPrefix s p e t ^ 2) volume a b at hge
  change IntervalIntegrable
    (fun t => weightedPrefix s p c t * weightedPrefix s p e t) volume a b at hgcge
  have hinv : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (uIcc a b) := by
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1))
  have hMc : IntervalIntegrable
      (fun t => prefixMass s p c t ^ 2 / t ^ 2) volume a b := by
    simpa only [div_eq_mul_inv, one_mul] using
      (prefixMass_sq_intervalIntegrable s p c hab).mul_continuousOn hinv
  have hMe : IntervalIntegrable
      (fun t => prefixMass s p e t ^ 2 / t ^ 2) volume a b := by
    simpa only [div_eq_mul_inv, one_mul] using
      (prefixMass_sq_intervalIntegrable s p e hab).mul_continuousOn hinv
  have hMcMe : IntervalIntegrable
      (fun t => prefixMass s p c t * prefixMass s p e t / t ^ 2) volume a b := by
    simpa only [div_eq_mul_inv, one_mul] using
      (prefixMass_mul_intervalIntegrable s p c e hab).mul_continuousOn hinv
  have hc := finite_prefix_square_energy s p c hp ha hab
  have he := finite_prefix_square_energy s p e hp ha hab
  have hce := finite_prefix_square_energy s p (fun i => c i + e i) hp ha hab
  simp_rw [weightedPrefix_add, compensated_add, prefixMass_add] at hce
  rw [integral_square_add hgc hge hgcge,
    integral_square_div_add hMc hMe hMcMe] at hce
  nlinarith [hc, he, hce]

end CumulativePrefixBilinear

#print axioms CumulativePrefixBilinear.prefixMass_add
#print axioms CumulativePrefixBilinear.compensated_add
#print axioms CumulativePrefixBilinear.prefixMass_mul_intervalIntegrable
#print axioms CumulativePrefixBilinear.finite_prefix_bilinear_energy
