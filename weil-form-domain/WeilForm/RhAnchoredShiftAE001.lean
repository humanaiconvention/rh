import RhAnchoredShift001

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace RhAnchored

lemma ae_ne_const (c : ℝ) : ∀ᵐ t ∂volume, t ≠ c := by
  have h : volume ({c} : Set ℝ) = 0 := by simp
  rw [measure_eq_zero_iff_ae_notMem] at h
  simpa only [mem_singleton_iff] using h

theorem primeShift_left_trace {A L : ℝ} (hA : 0 < A) (hAL : A < L) (v : ℝ → ℝ) :
    primeShift A L (primitive A v) (A-L) = 0 := by
  have hp : (A-L)+L ∈ interval A := by constructor <;> linarith
  have hm : (A-L)-L ∉ interval A := by intro hm; linarith [hm.1]
  rw [primeShift, zeroExtension_eq hp, zeroExtension_eq_zero hm]
  rw [show A-L+L=A by ring, primitive_right_endpoint hA v]
  simp

theorem primeShift_right_trace {A L : ℝ} (hA : 0 < A) (hAL : A < L) (v : ℝ → ℝ) :
    primeShift A L (primitive A v) (L-A) = 0 := by
  have hp : (L-A)+L ∉ interval A := by intro hp; linarith [hp.2]
  have hm : (L-A)-L ∈ interval A := by constructor <;> linarith
  rw [primeShift, zeroExtension_eq_zero hp, zeroExtension_eq hm]
  rw [show L-A-L= -A by ring, primitive_left_endpoint hA v]
  simp

lemma shift_cell_partition {A L t : ℝ} (hAL : A < L) (ht : t ∈ interval A)
    (htL : t ≠ -A) (htR : t ≠ A) (ht1 : t ≠ A-L) (ht2 : t ≠ L-A) :
    t ∈ shiftLeftCell A L ∨ t ∈ shiftMiddleCell A L ∨ t ∈ shiftRightCell A L := by
  have hleft : -A < t := lt_of_le_of_ne ht.1 (Ne.symm htL)
  have hright : t < A := lt_of_le_of_ne ht.2 htR
  by_cases h1 : t < A-L
  · exact Or.inl ⟨hleft, h1⟩
  · have h1' : A-L < t := lt_of_le_of_ne (le_of_not_gt h1) (Ne.symm ht1)
    by_cases h2 : t < L-A
    · exact Or.inr (Or.inl ⟨h1', h2⟩)
    · have h2' : L-A < t := lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm ht2)
      exact Or.inr (Or.inr ⟨h2', hright⟩)

theorem shiftFlux_ae_deriv {A L : ℝ} (hA : 0 < A) (hAL : A < L) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) :
    ∀ᵐ t ∂physicalMeasure A,
      deriv (shiftFlux A L (primitive A v)) t=primeShift A L (primitive A v) t := by
  unfold physicalMeasure
  rw [ae_restrict_iff' (show MeasurableSet (interval A) from measurableSet_Icc)]
  filter_upwards [ae_ne_const (-A), ae_ne_const A,
    ae_ne_const (A-L), ae_ne_const (L-A)] with t htL htR ht1 ht2 htI
  rcases shift_cell_partition hAL htI htL htR ht1 ht2 with hleft|hmiddle|hright
  · rw [primeShift_left hAL hleft]
    exact (shiftFlux_hasDerivAt_left hA hAL hv hleft).deriv
  · rw [primeShift_middle hmiddle]
    exact (shiftFlux_hasDerivAt_middle hA hAL hv hmiddle).deriv
  · rw [primeShift_right hAL hright]
    exact (shiftFlux_hasDerivAt_right hA hAL hv hright).deriv

end RhAnchored
#print axioms RhAnchored.primeShift_left_trace
#print axioms RhAnchored.primeShift_right_trace
#print axioms RhAnchored.shiftFlux_ae_deriv
