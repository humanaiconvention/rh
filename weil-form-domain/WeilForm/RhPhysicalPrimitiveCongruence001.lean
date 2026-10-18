import RhPhysicalMassConvergence001
import RhCompleteFormBound001

/-! Actual restricted-AE congruence for Fourier quotients and every complete
bounded-form component. Both translated delays and both rank profiles remain.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhPhysicalPrimitiveCongruence
open RhAnchored RhTail

lemma zeroExtension_congr_ae {R : ℝ} {w z : ℝ → ℝ}
    (h : w =ᵐ[physicalMeasure R] z) : zeroExtension R w =ᵐ[volume] zeroExtension R z := by
  unfold physicalMeasure at h
  change ∀ᵐ t ∂volume.restrict (interval R), w t = z t at h
  rw [ae_restrict_iff' (show MeasurableSet (interval R) from measurableSet_Icc)] at h
  filter_upwards [h] with t ht
  by_cases htI : t ∈ interval R
  · rw [zeroExtension_eq htI, zeroExtension_eq htI, ht htI]
  · rw [zeroExtension_eq_zero htI, zeroExtension_eq_zero htI]

/-- Equality of the actual whole-line L2 Fourier-input classes, not pointwise
identification of chosen representatives. -/
theorem physicalFourierVector_congr_ae {R : ℝ} {w z : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure R)) (hz : MemLp z 2 (physicalMeasure R))
    (h : w =ᵐ[physicalMeasure R] z) :
    physicalFourierVector R w hw = physicalFourierVector R z hz := by
  unfold physicalFourierVector
  apply Lp.ext
  filter_upwards [(complexExtension_memLp hw).coeFn_toLp,
    (complexExtension_memLp hz).coeFn_toLp, zeroExtension_congr_ae h] with t hwt hzt ht
  rw [hwt, hzt]
  change (zeroExtension R w t : ℂ) = (zeroExtension R z t : ℂ)
  rw [ht]

theorem fullFrequencyEnergy_congr_ae {R : ℝ} {w z : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure R)) (hz : MemLp z 2 (physicalMeasure R))
    (h : w =ᵐ[physicalMeasure R] z) (b : ℝ) :
    fullFrequencyEnergy b (physicalFourierVector R w hw) =
      fullFrequencyEnergy b (physicalFourierVector R z hz) := by
  rw [physicalFourierVector_congr_ae hw hz h]

lemma square_mass_congr_ae {R : ℝ} {w z : ℝ → ℝ}
    (h : w =ᵐ[physicalMeasure R] z) :
    (∫ t in interval R, (w t) ^ 2) = ∫ t in interval R, (z t) ^ 2 := by
  apply integral_congr_ae
  filter_upwards [h] with t ht
  rw [ht]

lemma moment_congr_ae {R : ℝ} {w z : ℝ → ℝ}
    (h : w =ᵐ[physicalMeasure R] z) (p : ℝ → ℝ) :
    (∫ t in interval R, p t * w t) = ∫ t in interval R, p t * z t := by
  apply integral_congr_ae
  filter_upwards [h] with t ht
  rw [ht]

lemma realShift_congr_ae {w z : ℝ → ℝ} (h : w =ᵐ[volume] z) (L : ℝ) :
    RhDilation.realShift w L = RhDilation.realShift z L := by
  have hp := (measurePreserving_add_right volume L).quasiMeasurePreserving.ae_eq_comp h
  have hm := (measurePreserving_add_right volume (-L)).quasiMeasurePreserving.ae_eq_comp h
  unfold RhDilation.realShift
  apply integral_congr_ae
  filter_upwards [h, hp, hm] with t ht hpt hmt
  simp only [Function.comp_def] at hpt hmt
  simp only [sub_eq_add_neg]
  rw [ht, hpt, hmt]

/-- The actual zero-extended partial shifts descend to physical L2 classes. -/
theorem shift_pairing_congr_ae {R : ℝ} {w z : ℝ → ℝ}
    (h : w =ᵐ[physicalMeasure R] z) (L : ℝ) :
    (∫ t in interval R, primeShift R L w t * w t) =
      ∫ t in interval R, primeShift R L z t * z t := by
  rw [RhDilation.actual_shift_pairing, RhDilation.actual_shift_pairing]
  exact realShift_congr_ae (zeroExtension_congr_ae h) L

/-- BOTH native rank terms and the scalar mass are preserved. -/
theorem rankScalar_congr_ae {R : ℝ} {w z : ℝ → ℝ}
    (h : w =ᵐ[physicalMeasure R] z) (C : ℝ) :
    RhCompletePrimitiveDictionary.rankScalar R C w =
      RhCompletePrimitiveDictionary.rankScalar R C z := by
  unfold RhCompletePrimitiveDictionary.rankScalar
  rw [square_mass_congr_ae h, moment_congr_ae h (fun t => Real.cosh (t / 2)),
    moment_congr_ae h (fun t => Real.sinh (t / 2))]

/-- Every finite prime-power shift keeps its native coefficient and delay. -/
theorem boundedPart_congr_ae {R : ℝ} {w z : ℝ → ℝ}
    (h : w =ᵐ[physicalMeasure R] z) (C : ℝ) (N : ℕ) :
    RhCompleteFormBound.boundedPart R C N w = RhCompleteFormBound.boundedPart R C N z := by
  unfold RhCompleteFormBound.boundedPart
  rw [rankScalar_congr_ae h C]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [shift_pairing_congr_ae h (Real.log (n : ℝ))]

/-- Combined actual quotient dictionary: full energy, primitive mass, and the
entire bounded part are invariant under restricted almost-everywhere equality. -/
theorem complete_components_congr_ae {R : ℝ} {w z : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure R)) (hz : MemLp z 2 (physicalMeasure R))
    (h : w =ᵐ[physicalMeasure R] z) :
    fullFrequencyEnergy (1 / 2) (physicalFourierVector R w hw) =
      fullFrequencyEnergy (1 / 2) (physicalFourierVector R z hz) ∧
    (∫ t in interval R, (w t) ^ 2) = (∫ t in interval R, (z t) ^ 2) ∧
    ∀ C N, RhCompleteFormBound.boundedPart R C N w = RhCompleteFormBound.boundedPart R C N z :=
  ⟨fullFrequencyEnergy_congr_ae hw hz h (1 / 2), square_mass_congr_ae h,
    fun C N => boundedPart_congr_ae h C N⟩

end RhPhysicalPrimitiveCongruence
#print axioms RhPhysicalPrimitiveCongruence.physicalFourierVector_congr_ae
#print axioms RhPhysicalPrimitiveCongruence.fullFrequencyEnergy_congr_ae
#print axioms RhPhysicalPrimitiveCongruence.shift_pairing_congr_ae
#print axioms RhPhysicalPrimitiveCongruence.boundedPart_congr_ae
#print axioms RhPhysicalPrimitiveCongruence.complete_components_congr_ae
