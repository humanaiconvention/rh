import RhFourierTailLimit001
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
L2 Fourier isometry and the nonnegative frequency-tail limit.
The spatial exponential-kernel identification is a separate obligation.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology Interval BigOperators ComplexInnerProductSpace ENNReal
namespace RhTail

abbrev WholeSpace := Lp (α := ℝ) ℂ 2 volume
def angularSquare (ξ : ℝ) : ℝ := (2*Real.pi*ξ)^2
def spectralDensity (w : WholeSpace) (ξ : ℝ) : ℝ := ‖(𝓕 w) ξ‖^2
def frequencySummand (b : ℝ) (w : WholeSpace) (k : ℕ) (ξ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (multiplier (angularSquare ξ) (b+2*k)*spectralDensity w ξ)
def finiteFrequencyEnergy (b : ℝ) (w : WholeSpace) (K : ℕ) : ℝ≥0∞ :=
  ∫⁻ ξ, ∑ k ∈ Finset.range K, frequencySummand b w k ξ
def fullFrequencyEnergy (b : ℝ) (w : WholeSpace) : ℝ≥0∞ :=
  ∫⁻ ξ, ∑' k : ℕ, frequencySummand b w k ξ

lemma frequencySummand_aemeasurable {b : ℝ} (hb : 0 < b) (w : WholeSpace) (k : ℕ) :
    AEMeasurable (frequencySummand b w k) volume := by
  have hk : 0 < b+2*(k : ℝ) := by positivity
  have hm : Continuous (fun ξ : ℝ => multiplier (angularSquare ξ) (b+2*k)) := by
    unfold multiplier angularSquare
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro ξ
      exact mul_ne_zero (ne_of_gt hk) (ne_of_gt (by positivity))
  have hd : AEMeasurable (spectralDensity w) volume :=
    (Lp.memLp (𝓕 w)).aestronglyMeasurable.norm.aemeasurable.pow_const 2
  exact (hm.aemeasurable.mul hd).ennreal_ofReal

theorem frequency_tail_monotone_convergence {b : ℝ} (hb : 0 < b) (w : WholeSpace) :
    (∫⁻ ξ, ⨆ K : ℕ, ∑ k ∈ Finset.range K, frequencySummand b w k ξ) =
      ⨆ K : ℕ, finiteFrequencyEnergy b w K := by
  apply lintegral_iSup'
  · intro K
    exact Finset.aemeasurable_fun_sum (Finset.range K)
      (fun k _ => frequencySummand_aemeasurable hb w k)
  · exact Eventually.of_forall (fun ξ K K' h =>
      Finset.sum_le_sum_of_subset (Finset.range_mono h))

lemma finite_frequency_eq_sum {b : ℝ} (hb : 0 < b) (w : WholeSpace) (K : ℕ) :
    finiteFrequencyEnergy b w K =
      ∑ k ∈ Finset.range K, ∫⁻ ξ, frequencySummand b w k ξ :=
  lintegral_finsetSum' (Finset.range K)
    (fun k _ => frequencySummand_aemeasurable hb w k)

lemma full_frequency_eq_tsum {b : ℝ} (hb : 0 < b) (w : WholeSpace) :
    fullFrequencyEnergy b w=∑' k : ℕ, ∫⁻ ξ, frequencySummand b w k ξ :=
  lintegral_tsum (frequencySummand_aemeasurable hb w)

theorem frequency_tail_limit {b : ℝ} (hb : 0 < b) (w : WholeSpace) :
    Tendsto (finiteFrequencyEnergy b w) atTop (𝓝 (fullFrequencyEnergy b w)) := by
  have hs : Summable (fun k : ℕ => ∫⁻ ξ, frequencySummand b w k ξ) := ENNReal.summable
  have h := hs.hasSum.tendsto_sum_nat
  simpa only [← finite_frequency_eq_sum hb w, ← full_frequency_eq_tsum hb w] using h

theorem frequency_tail_lower_bound {b : ℝ} (hb : 1 ≤ b) (w : WholeSpace) :
    (∫⁻ ξ, ENNReal.ofReal
      ((1/2+1/b)*angularSquare ξ/(b^2+angularSquare ξ)*spectralDensity w ξ)) ≤
      fullFrequencyEnergy b w := by
  apply lintegral_mono
  intro ξ
  have hd : 0 ≤ spectralDensity w ξ := sq_nonneg _
  have hx : 0 ≤ angularSquare ξ := sq_nonneg _
  have hs := (multiplier_series_summable hx hb).mul_right (spectralDensity w ξ)
  have hn : ∀ k : ℕ, 0 ≤ multiplier (angularSquare ξ) (b+2*k)*spectralDensity w ξ :=
    fun k => mul_nonneg (multiplier_nonneg hx (by positivity)) hd
  have he := ENNReal.ofReal_tsum_of_nonneg hn hs
  have hl := mul_le_mul_of_nonneg_right (multiplier_tail_lower_bound hx hb) hd
  unfold frequencySummand
  dsimp only
  rw [← he, tsum_mul_right]
  exact ENNReal.ofReal_le_ofReal hl

theorem plancherel_inner (f g : WholeSpace) :
    inner ℂ (𝓕 f) (𝓕 g) = inner ℂ f g :=
  Lp.inner_fourier_eq f g

end RhTail
#print axioms RhTail.frequency_tail_monotone_convergence
#print axioms RhTail.frequency_tail_limit
#print axioms RhTail.frequency_tail_lower_bound
#print axioms RhTail.plancherel_inner
