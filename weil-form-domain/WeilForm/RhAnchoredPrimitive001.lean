import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
Concrete anchored primitives for real L2 representatives on a finite interval.
The value at zero is a convention; one-sided trace extensions are separate.
No arbitrary kernel or differential operator is assumed to satisfy an identity.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators

namespace RhAnchored

def interval (A : ℝ) : Set ℝ := Icc (-A) A
def physicalMeasure (A : ℝ) : Measure ℝ := volume.restrict (interval A)
instance (A : ℝ) : IsFiniteMeasure (physicalMeasure A) := by
  unfold physicalMeasure interval
  infer_instance
abbrev PhysicalSpace (A : ℝ) := Lp ℝ 2 (physicalMeasure A)

def zeroExtension (A : ℝ) (v : ℝ → ℝ) : ℝ → ℝ := (interval A).indicator v
def leftPrimitive (A : ℝ) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (-A)..t, zeroExtension A v u
def rightPrimitive (A : ℝ) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in A..t, zeroExtension A v u
def primitive (A : ℝ) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t < 0 then leftPrimitive A v t
  else if 0 < t then rightPrimitive A v t else 0
def totalMass (A : ℝ) (v : ℝ → ℝ) : ℝ := ∫ u in interval A, v u

lemma zeroExtension_integrable {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) : Integrable (zeroExtension A v) := by
  have h : IntegrableOn v (interval A) := by
    exact hv.integrable (by norm_num)
  exact (integrable_indicator_iff measurableSet_Icc).2 h

lemma zeroExtension_eq {A t : ℝ} {v : ℝ → ℝ} (ht : t ∈ interval A) :
    zeroExtension A v t = v t := by simp [zeroExtension, ht]

lemma zeroExtension_eq_zero {A t : ℝ} {v : ℝ → ℝ} (ht : t ∉ interval A) :
    zeroExtension A v t = 0 := by simp [zeroExtension, ht]

lemma primitive_zero (A : ℝ) (v : ℝ → ℝ) : primitive A v 0 = 0 := by
  simp [primitive]

lemma primitive_left_endpoint {A : ℝ} (hA : 0 < A) (v : ℝ → ℝ) :
    primitive A v (-A) = 0 := by
  simp [primitive, show -A < 0 by linarith, leftPrimitive]

lemma primitive_right_endpoint {A : ℝ} (hA : 0 < A) (v : ℝ → ℝ) :
    primitive A v A = 0 := by
  simp [primitive, hA, not_lt_of_ge hA.le, rightPrimitive]

lemma primitive_eq_left {A t : ℝ} (v : ℝ → ℝ) (ht : t < 0) :
    primitive A v t = leftPrimitive A v t := by simp [primitive, ht]

lemma primitive_eq_right {A t : ℝ} (v : ℝ → ℝ) (ht : 0 < t) :
    primitive A v t = rightPrimitive A v t := by
  simp [primitive, ht, not_lt_of_ge ht.le]

lemma rightPrimitive_eq_negative_integral (A : ℝ) (v : ℝ → ℝ) (t : ℝ) :
    rightPrimitive A v t = -(∫ u in t..A, zeroExtension A v u) := by
  exact intervalIntegral.integral_symm _ _

lemma leftPrimitive_ac {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) :
    AbsolutelyContinuousOnInterval (leftPrimitive A v) (-A) 0 := by
  exact (zeroExtension_integrable hv).intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (by simp)

lemma rightPrimitive_ac {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) :
    AbsolutelyContinuousOnInterval (rightPrimitive A v) 0 A := by
  exact (zeroExtension_integrable hv).intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (by simp)

lemma primitive_ac_left {A B : ℝ} (hA : 0 < A) (hB : -A ≤ B) (hB0 : B < 0)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) :
    AbsolutelyContinuousOnInterval (primitive A v) (-A) B := by
  apply ((leftPrimitive_ac hA hv).mono ?_).congr
  · intro t ht
    rw [uIcc_of_le hB] at ht
    rw [primitive_eq_left v (by linarith [ht.2])]
  · rw [uIcc_of_le hB, uIcc_of_le (by linarith : -A ≤ (0 : ℝ))]
    intro t ht
    exact ⟨ht.1, le_trans ht.2 hB0.le⟩

lemma primitive_ac_right {A B : ℝ} (hA : 0 < A) (hB : B ≤ A) (hB0 : 0 < B)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) :
    AbsolutelyContinuousOnInterval (primitive A v) B A := by
  apply ((rightPrimitive_ac hA hv).mono ?_).congr
  · intro t ht
    rw [uIcc_of_le hB] at ht
    rw [primitive_eq_right v (by linarith [ht.1])]
  · rw [uIcc_of_le hB, uIcc_of_le hA.le]
    intro t ht
    exact ⟨le_trans hB0.le ht.1, ht.2⟩

lemma leftPrimitive_continuous {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) : Continuous (leftPrimitive A v) := by
  exact intervalIntegral.continuous_primitive
    (fun _ _ => (zeroExtension_integrable hv).intervalIntegrable) (-A)

lemma rightPrimitive_continuous {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) : Continuous (rightPrimitive A v) := by
  exact intervalIntegral.continuous_primitive
    (fun _ _ => (zeroExtension_integrable hv).intervalIntegrable) A

lemma primitive_left_trace {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) :
    Tendsto (primitive A v) (𝓝[<] 0) (𝓝 (leftPrimitive A v 0)) := by
  apply ((leftPrimitive_continuous hv).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (primitive_eq_left v ht).symm

lemma primitive_right_trace {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) :
    Tendsto (primitive A v) (𝓝[>] 0) (𝓝 (rightPrimitive A v 0)) := by
  apply ((rightPrimitive_continuous hv).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (primitive_eq_right v ht).symm

lemma interval_zeroExtension_mass {A : ℝ} (hA : 0 < A) (v : ℝ → ℝ) :
    (∫ u in (-A)..A, zeroExtension A v u) = totalMass A v := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  exact zeroExtension_eq ht

lemma primitive_jump {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) :
    rightPrimitive A v 0 - leftPrimitive A v 0 = -totalMass A v := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    ((zeroExtension_integrable hv).intervalIntegrable (a := -A) (b := 0))
    ((zeroExtension_integrable hv).intervalIntegrable (a := 0) (b := A))
  rw [interval_zeroExtension_mass hA v] at h
  rw [rightPrimitive_eq_negative_integral]
  unfold leftPrimitive
  linarith

def anchoredKernel (g : ℝ → ℝ) (t u : ℝ) : ℝ :=
  g (t-u)-g t-g (-u)+g 0

lemma anchoredKernel_zero_left (g : ℝ → ℝ) (u : ℝ) :
    anchoredKernel g 0 u = 0 := by simp [anchoredKernel]

lemma anchoredKernel_zero_right (g : ℝ → ℝ) (t : ℝ) :
    anchoredKernel g t 0 = 0 := by simp [anchoredKernel]

def archIndex (k : ℕ) : ℝ := k+1/4
def beta (k : ℕ) : ℝ := 2*archIndex k

def finitePotential (C α L : ℝ) (J : ℕ) (x : ℝ) : ℝ :=
  -8*(Real.cosh (x/2)-1) + (C/2)*|x|
  - ∑ k ∈ Finset.range J, (1-Real.exp (-(beta k)*|x|))/(4*(archIndex k)^2)
  + α*max (|x|-L) 0

def finiteKernel (C α L : ℝ) (J : ℕ) : ℝ → ℝ → ℝ :=
  anchoredKernel (finitePotential C α L J)

lemma finiteKernel_zero_left (C α L : ℝ) (J : ℕ) (u : ℝ) :
    finiteKernel C α L J 0 u = 0 := anchoredKernel_zero_left _ _

lemma finiteKernel_zero_right (C α L : ℝ) (J : ℕ) (t : ℝ) :
    finiteKernel C α L J t 0 = 0 := anchoredKernel_zero_right _ _

end RhAnchored

#print axioms RhAnchored.primitive_jump
#print axioms RhAnchored.primitive_left_trace
#print axioms RhAnchored.primitive_ac_left
#print axioms RhAnchored.finiteKernel_zero_left
