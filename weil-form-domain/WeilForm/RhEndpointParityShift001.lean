import RhFinitePrimitiveEndpoint001

noncomputable section
open Set MeasureTheory Filter
namespace RhEndpointParity
open RhAnchored
lemma primeShift_memLp {A : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure A)) (L : ℝ) :
    MemLp (primeShift A L w) 2 (physicalMeasure A) := by
  have hz : MemLp (zeroExtension A w) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).mpr hw
  have hp := hz.comp_measurePreserving (measurePreserving_add_right volume L)
  have hm := hz.comp_measurePreserving (measurePreserving_add_right volume (-L))
  have hi := (hp.add hm).mono_measure (Measure.restrict_le_self (s := interval A))
  convert hi using 1
  · ext t
    simp [primeShift,Function.comp_def,sub_eq_add_neg]
  · rfl

lemma shift_integrable {A : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure A)) (L : ℝ) :
    IntegrableOn (fun t => primeShift A L w t*w t) (interval A) :=
  (primeShift_memLp hw L).integrable_mul hw


end RhEndpointParity
#print axioms RhEndpointParity.shift_integrable
