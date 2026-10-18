import RhFourierGridError001
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! Literal finite-rank Fourier-grid operators on the complete supported
weighted domain. This module supplies no arithmetic residual estimate. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ComplexConjugate
namespace RhFourierGridOperator
open RhWeightedMeasureEmbedding RhSupportedMollifier RhFiniteFourierGrid
open RhFourierSupportBound RhFourierGridError

/-- The compact plane wave with the conjugate convention of the L2 inner product. -/
def planeWave (R xi : ℝ) : ℝ → ℂ :=
  (Icc (-R) R).indicator (fun t => star (phase (-2 * Real.pi * t * xi)))

lemma planeWave_memLp (R xi : ℝ) : MemLp (planeWave R xi) 2 volume := by
  have h : MemLp ((Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ))) 2 volume := memLp_indicator_const (μ := (volume : Measure ℝ)) 2
    measurableSet_Icc.nullMeasurableSet (1 : ℝ) (Or.inr measure_Icc_lt_top.ne)
  apply h.mono'
  · exact (by unfold phase; fun_prop : Continuous (fun t : ℝ =>
      star (phase (-2 * Real.pi * t * xi)))).aestronglyMeasurable.indicator measurableSet_Icc
  · exact Eventually.of_forall (fun t => by
      by_cases ht : t ∈ Icc (-R) R
      · simp [planeWave, ht, phase_norm]
      · simp [planeWave, ht])

def planeWaveVector (R xi : ℝ) : WholeSpace := (planeWave_memLp R xi).toLp (planeWave R xi)

/-- A bounded actual Fourier sample, defined by a compact plane-wave L2 pairing. -/
def sample (R xi : ℝ) : SupportedSpace R →L[ℝ] ℂ :=
  (((innerSL ℂ (planeWaveVector R xi)).restrictScalars ℝ).comp physicalEmbedding).comp
    (supportedSubspace R).subtypeL

lemma sample_eq_fourier {R : ℝ} (F : SupportedSpace R) (xi : ℝ) :
    sample R xi F = (𝓕 (representative R F)) xi := by
  change inner ℂ (planeWaveVector R xi) (physicalEmbedding (F : WeightedSpace)) = _
  rw [L2.inner_def, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [(planeWave_memLp R xi).coeFn_toLp] with t ht
  change (planeWaveVector R xi : ℝ → ℂ) t = _ at ht
  rw [ht]
  by_cases hx : t ∈ Icc (-R) R
  · simp [planeWave, hx, RCLike.inner_apply, representative, phase, mul_comm]
  · simp [planeWave, hx, RCLike.inner_apply, representative]

def samples (R Omega : ℝ) (M : ℕ) : SupportedSpace R →L[ℝ] (Fin M → ℂ) :=
  ContinuousLinearMap.pi (fun i => sample R (left Omega M i))

lemma cellOne_memLp (Omega : ℝ) (M : ℕ) (i : Fin M) :
    MemLp ((cell Omega M i).indicator (fun _ : ℝ => (1 : ℂ))) 2 volume :=
  memLp_indicator_const 2 measurableSet_Ico.nullMeasurableSet _
    (Or.inr measure_Ico_lt_top.ne)

def cellVector (Omega : ℝ) (M : ℕ) (i : Fin M) : WholeSpace :=
  (cellOne_memLp Omega M i).toLp _

/-- Complex-linear reconstruction factors through exactly M complex coordinates. -/
def reconstruction (Omega : ℝ) (M : ℕ) : (Fin M → ℂ) →L[ℂ] WholeSpace :=
  ∑ i : Fin M, (ContinuousLinearMap.proj i).smulRight (cellVector Omega M i)

def grid (R Omega : ℝ) (M : ℕ) : SupportedSpace R →L[ℝ] WholeSpace :=
  ((reconstruction Omega M).restrictScalars ℝ).comp (samples R Omega M)

lemma reconstruction_ae (Omega : ℝ) (M : ℕ) (a : Fin M → ℂ) :
    reconstruction Omega M a =ᵐ[volume]
      (fun xi => ∑ i : Fin M, (cell Omega M i).indicator (fun _ => a i) xi) := by
  classical
  have hs : reconstruction Omega M a = ∑ i : Fin M, a i • cellVector Omega M i := by
    simp [reconstruction]
  rw [hs]
  have hc : ∀ᵐ xi ∂(volume : Measure ℝ), ∀ i : Fin M,
      (cellVector Omega M i : ℝ → ℂ) xi = (cell Omega M i).indicator (fun _ => (1 : ℂ)) xi :=
    ae_all_iff.mpr (fun i => (cellOne_memLp Omega M i).coeFn_toLp)
  filter_upwards [Lp.coeFn_finsetSum (Finset.univ : Finset (Fin M))
    (fun i => a i • cellVector Omega M i), hc,
    ae_all_iff.mpr (fun i : Fin M => Lp.coeFn_smul (a i) (cellVector Omega M i))] with xi hs hc hm
  rw [hs]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hm i]
  simp only [Pi.smul_apply]
  rw [hc i]
  by_cases hi : xi ∈ cell Omega M i <;> simp [hi]

lemma grid_ae {R : ℝ} (F : SupportedSpace R) (Omega : ℝ) (M : ℕ) :
    grid R Omega M F =ᵐ[volume] step Omega M (𝓕 (representative R F)) := by
  have h := reconstruction_ae Omega M (samples R Omega M F)
  exact h.trans (Eventually.of_forall (fun xi => by
    unfold step
    apply Finset.sum_congr rfl
    intro i _
    have he : samples R Omega M F i = (𝓕 (representative R F)) (left Omega M i) :=
      sample_eq_fourier F _
    rw [he]))

/-- Compactness is obtained from finite-dimensional factorization, not a
presumed bound on the arithmetic form. -/
theorem grid_compact (R Omega : ℝ) (M : ℕ) : IsCompactOperator (grid R Omega M) := by
  have hs : IsCompactOperator (samples R Omega M) :=
    isCompactOperator_of_locallyCompactSpace_dom (samples R Omega M)
  exact hs.clm_comp ((reconstruction Omega M).restrictScalars ℝ)

theorem physical_grid_compact (R Omega : ℝ) (M : ℕ) :
    IsCompactOperator (inverseFourier.comp (grid R Omega M)) :=
  (grid_compact R Omega M).clm_comp inverseFourier

end RhFourierGridOperator
#print axioms RhFourierGridOperator.sample_eq_fourier
#print axioms RhFourierGridOperator.grid_ae
#print axioms RhFourierGridOperator.grid_compact
#print axioms RhFourierGridOperator.physical_grid_compact



