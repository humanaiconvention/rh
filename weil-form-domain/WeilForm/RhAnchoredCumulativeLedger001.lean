import RhAnchoredShiftAE001

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

def headMass (A : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u in interval A, (Iic x).indicator w u

theorem headMass_eq_cumulative {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (x : ℝ) :
    headMass A (primitive A v) x = leftPrimitive A (primitive A v) x := by
  by_cases hxL : x ≤ -A
  · rw [cumulative_zero_before _ hxL]
    unfold headMass
    calc
      _ = ∫ u in interval A, (0 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro u hu
        dsimp only
        by_cases hux : u ≤ x
        · have hue : u = -A := by linarith [hu.1]
          rw [indicator_of_mem (show u ∈ Iic x from hux), hue, primitive_left_endpoint hA v]
        · exact indicator_of_notMem hux _
      _ = 0 := by simp
  by_cases hxR : A ≤ x
  · rw [cumulative_mass_after hA hv hxR]
    unfold headMass totalMass
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    exact indicator_of_mem (hu.2.trans hxR) _
  have hL : -A ≤ x := (lt_of_not_ge hxL).le
  have hR : x ≤ A := (lt_of_not_ge hxR).le
  unfold headMass leftPrimitive
  rw [setIntegral_indicator measurableSet_Iic]
  have hs : interval A ∩ Iic x = Icc (-A) x := by
    ext u
    simp only [interval, mem_inter_iff, mem_Icc, mem_Iic]
    constructor
    · intro h
      exact ⟨h.1.1, h.2⟩
    · intro h
      exact ⟨⟨h.1, h.2.trans hR⟩, h.2⟩
  rw [hs, intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  exact (zeroExtension_eq (show u ∈ interval A from ⟨hu.1, hu.2.trans hR⟩)).symm

lemma headMass_integrable {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (x : ℝ) :
    Integrable ((Iic x).indicator (primitive A v)) (physicalMeasure A) :=
  (primitive_integrableOn hv).indicator measurableSet_Iic

def hingeSlope (L x : ℝ) : ℝ := (if L ≤ x then 1 else 0)+(if -L ≤ x then 1 else 0)-1

def hingeConvolution (A L : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in interval A, hingeSlope L (t-u)*w u

lemma hingeSlope_integrand (L t u : ℝ) (w : ℝ → ℝ) :
    hingeSlope L (t-u)*w u =
    (Iic (t-L)).indicator w u+(Iic (t+L)).indicator w u-w u := by
  by_cases hm : u ≤ t-L <;> by_cases hp : u ≤ t+L
  all_goals simp only [hingeSlope]
  all_goals simp only [show (L ≤ t-u) ↔ u ≤ t-L by constructor <;> intro h <;> linarith,
    show (-L ≤ t-u) ↔ u ≤ t+L by constructor <;> intro h <;> linarith]
  all_goals simp [hm, hp]

theorem hingeConvolution_eq_cumulative {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (L t : ℝ) :
    hingeConvolution A L (primitive A v) t =
    leftPrimitive A (primitive A v) (t-L)+leftPrimitive A (primitive A v) (t+L)
      -totalMass A (primitive A v) := by
  unfold hingeConvolution
  simp_rw [hingeSlope_integrand]
  change (∫ u, (Iic (t-L)).indicator (primitive A v) u+
      (Iic (t+L)).indicator (primitive A v) u-primitive A v u ∂physicalMeasure A) = _
  have ha : Integrable (fun u => (Iic (t-L)).indicator (primitive A v) u+
      (Iic (t+L)).indicator (primitive A v) u) (physicalMeasure A) :=
    (headMass_integrable hv (t-L)).add (headMass_integrable hv (t+L))
  rw [integral_sub ha
    (primitive_integrableOn hv), integral_add (headMass_integrable hv (t-L))
    (headMass_integrable hv (t+L))]
  change headMass A (primitive A v) (t-L)+headMass A (primitive A v) (t+L)
    -totalMass A (primitive A v) = _
  rw [headMass_eq_cumulative hA hv, headMass_eq_cumulative hA hv]

theorem hingeConvolution_eq_shiftFlux {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (t : ℝ) :
    hingeConvolution A L (primitive A v) t=shiftFlux A L (primitive A v) t := by
  rw [hingeConvolution_eq_cumulative hA hv]
  unfold shiftFlux
  rw [cumulative_zero_before _ (by linarith : -L ≤ -A), cumulative_mass_after hA hv hAL.le]
  ring

theorem hingeConvolution_ac {A L : ℝ} (hA : 0 < A) (hAL : A < L) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) :
    AbsolutelyContinuousOnInterval (hingeConvolution A L (primitive A v)) (-A) A := by
  apply (shiftFlux_ac hv L).congr
  intro t _
  exact (hingeConvolution_eq_shiftFlux hA hAL hv t).symm

theorem hingeConvolution_ae_deriv {A L : ℝ} (hA : 0 < A) (hAL : A < L) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) :
    ∀ᵐ t ∂physicalMeasure A,
      deriv (hingeConvolution A L (primitive A v)) t=primeShift A L (primitive A v) t := by
  have he : hingeConvolution A L (primitive A v)=shiftFlux A L (primitive A v) := by
    funext t
    exact hingeConvolution_eq_shiftFlux hA hAL hv t
  rw [he]
  exact shiftFlux_ae_deriv hA hAL hv

end RhAnchored
#print axioms RhAnchored.headMass_eq_cumulative
#print axioms RhAnchored.hingeConvolution_eq_shiftFlux
#print axioms RhAnchored.hingeConvolution_ae_deriv
