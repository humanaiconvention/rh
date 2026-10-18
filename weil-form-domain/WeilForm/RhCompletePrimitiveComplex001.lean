import RhCompletePrimitiveDictionary001
import RhDilationComplex001

/-! Exact complex physical kernel dictionary via its real and imaginary
primitive components. No assertion of positivity or pointwise Fourier
squared-modulus splitting is made. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace RhCompletePrimitiveComplex
open RhAnchored RhAllPrime RhCompletePrimitiveDictionary RhSupport

/-- Actual finite-energy primitive value; the input MemLp proof is explicit. -/
def primitiveValue (R : ℝ) (N : ℕ) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) : ℝ :=
  (RhTail.fullFrequencyEnergy (1 / 2)
    (RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv))).toReal +
    rankScalar R archConstant (primitive R v) -
    (∑ n ∈ Finset.Icc 2 N, weight n * (∫ t in interval R,
      primeShift R (Real.log (n : ℝ)) (primitive R v) t * primitive R v t))

/-- A complete finite cutoff for actual complex physical inputs, represented
by two actual real anchored primitives with every signed companion retained. -/
theorem complex_cutoff_identity {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℂ} (hv : MemLp v 2 (physicalMeasure R)) (N : ℕ) :
    complexEnergy R (completeKernel N) v =
      ((primitiveValue R N (fun t => (v t).re) hv.re +
        primitiveValue R N (fun t => (v t).im) hv.im : ℝ) : ℂ) := by
  have hvr : MemLp (fun t => (v t).re) 2 (physicalMeasure R) := by
    simpa only [RCLike.re_eq_complex_re] using hv.re
  have hvi : MemLp (fun t => (v t).im) 2 (physicalMeasure R) := by
    simpa only [RCLike.im_eq_complex_im] using hv.im
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    rw [RhDilationComplex.complex_energy_re (complete_joint_continuous N) hv]
    rw [complete_cutoff_native_identity hR hvr N,
      complete_cutoff_native_identity hR hvi N]
    rfl
  · simp only [Complex.ofReal_im]
    exact RhDilationComplex.complex_energy_im (complete_joint_continuous N)
      (complete_symmetric N) hv

/-- The exact physical radius kernel has the same complex decomposition. -/
theorem all_radius_complex_identity {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℂ} (hv : MemLp v 2 (physicalMeasure R)) :
    complexEnergy R (radiusKernel R) v =
      ((primitiveValue R (radiusCutoff R) (fun t => (v t).re) hv.re +
        primitiveValue R (radiusCutoff R) (fun t => (v t).im) hv.im : ℝ) : ℂ) :=
  complex_cutoff_identity hR hv (radiusCutoff R)

end RhCompletePrimitiveComplex
#print axioms RhCompletePrimitiveComplex.complex_cutoff_identity
#print axioms RhCompletePrimitiveComplex.all_radius_complex_identity
