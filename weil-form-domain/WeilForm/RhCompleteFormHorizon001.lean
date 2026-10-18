import RhNativePrimeDilationControl001
import RhCompleteDilationDictionary001
import RhSmoothPhysicalTransfer001

/-! Exact finite-horizon coherence on the actual supported complete domain.
Boundary contact is handled by the already proved almost-everywhere support
lemma. No moving horizon, infinite sum, smoothing, or numerical cutoff occurs. -/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhCompleteFormHorizon
open RhAnchored RhWeightedMeasureEmbedding RhNativeCompleteBilinear RhFlatSmoothCore
open RhPulledCompleteForm

/-- Every missing row is either an actual zero arithmetic coefficient or has
no positive-measure overlap on this support. This permits exact equality at
the threshold and explicitly retains the prescribed von Mangoldt weights. -/
def CoversActive (R : ℝ) (N : ℕ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → N < n → RhAllPrime.weight n = 0 ∨ 2 * R ≤ Real.log (n : ℝ)

lemma coversActive_of_radiusCutoff {R : ℝ} {N : ℕ}
    (hN : RhAllPrime.radiusCutoff R ≤ N) : CoversActive R N := by
  intro n hn hmissing
  right
  exact (RhAllPrime.log_above_radius_cutoff R (by omega)
    (lt_of_le_of_lt hN hmissing)).le

lemma coversActive_of_next_threshold {R : ℝ} {N : ℕ}
    (hnext : 2 * R ≤ Real.log ((N + 1 : ℕ) : ℝ)) : CoversActive R N := by
  intro n hn hmissing
  right
  have hcast : ((N + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmissing
  exact hnext.trans (Real.log_le_log (by positivity) hcast)

lemma coversActive_mono_radius {R S : ℝ} {N : ℕ} (hRS : R ≤ S)
    (hN : CoversActive S N) : CoversActive R N := by
  intro n hn hmissing
  rcases hN n hn hmissing with hzero | hthreshold
  · exact Or.inl hzero
  · exact Or.inr (by linarith)

lemma coversActive_mono_horizon {R : ℝ} {N M : ℕ} (hNM : N ≤ M)
    (hN : CoversActive R N) : CoversActive R M := by
  intro n hn hmissing
  exact hN n hn (lt_of_le_of_lt hNM hmissing)

/-- Actual polarized native shift form vanishes at and beyond support contact,
not merely for a diagonal or for smooth test functions. -/
theorem shiftPair_zero_of_threshold {R ell : ℝ} (hgap : 2 * R ≤ |ell|)
    {F G : WeightedSpace} (hF : F ∈ supportedSubspace R) (hG : G ∈ supportedSubspace R) :
    shiftPair ell F G = 0 := by
  rw [shiftPair_apply, RhNativeCompleteDictionary.twoShift_spatial_dictionary,
    RhNativeCompleteDictionary.twoShift_spatial_dictionary,
    RhSupportedArithmeticContinuity.spatialPair_zero_of_threshold hgap hF hG,
    RhSupportedArithmeticContinuity.spatialPair_zero_of_threshold hgap hG hF]
  norm_num

lemma arithmetic_sum_eq_of_le {R : ℝ} {N M : ℕ} (hNM : N ≤ M)
    (hN : CoversActive R N) {F G : WeightedSpace}
    (hF : F ∈ supportedSubspace R) (hG : G ∈ supportedSubspace R) :
    (∑ n ∈ Finset.Icc 2 N, RhAllPrime.weight n * shiftPair (Real.log (n : ℝ)) F G) =
      ∑ n ∈ Finset.Icc 2 M, RhAllPrime.weight n * shiftPair (Real.log (n : ℝ)) F G := by
  have hsub : Finset.Icc 2 N ⊆ Finset.Icc 2 M := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hNM⟩
  apply Finset.sum_subset hsub
  intro n hn hnot
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hmissing : N < n := by
    by_contra h
    exact hnot (Finset.mem_Icc.mpr ⟨hn2, Nat.le_of_not_gt h⟩)
  rcases hN n hn2 hmissing with hzero | hthreshold
  · rw [hzero, zero_mul]
  · rw [shiftPair_zero_of_threshold (hthreshold.trans (le_abs_self _)) hF hG, mul_zero]

/-- Equality with any larger exact finite cap. All non-arithmetic companions
are the SAME actual scalar/rank/arch terms before this identity is used. -/
theorem completeForm_eq_of_le {R : ℝ} (C : ℝ) {N M : ℕ} (hNM : N ≤ M)
    (hN : CoversActive R N) {F G : WeightedSpace}
    (hF : F ∈ supportedSubspace R) (hG : G ∈ supportedSubspace R) :
    completeForm R C N F G = completeForm R C M F G := by
  change archPair F G + boundedPart R C N F G = archPair F G + boundedPart R C M F G
  rw [boundedPart_apply, boundedPart_apply, arithmetic_sum_eq_of_le hNM hN hF hG]

/-- Both horizons contain all active prime-power rows. No ordering of their
sizes is assumed, and the equality is bilinear on the full supported domain. -/
theorem completeForm_horizon_eq {R : ℝ} (C : ℝ) {N M : ℕ}
    (hN : CoversActive R N) (hM : CoversActive R M) {F G : WeightedSpace}
    (hF : F ∈ supportedSubspace R) (hG : G ∈ supportedSubspace R) :
    completeForm R C N F G = completeForm R C M F G := by
  rcases le_total N M with hNM | hMN
  · exact completeForm_eq_of_le C hNM hN hF hG
  · exact (completeForm_eq_of_le C hMN hM hF hG).symm

theorem baseForm_horizon_eq (R C : ℝ) {N M : ℕ}
    (hN : CoversActive R N) (hM : CoversActive R M) :
    baseForm R C N = baseForm R C M := by
  ext F G
  rw [baseForm_apply, baseForm_apply]
  exact completeForm_horizon_eq C hN hM
    (flatCore_supported R F.property) (flatCore_supported R G.property)

/-- A single horizon covering the maximum radius is an EXACT representative
for every smaller radius. The cap is chosen before any radius varies. -/
theorem bounded_radius_form_horizon {R S : ℝ} (hRS : R ≤ S) (C : ℝ) {N : ℕ}
    (hN : RhAllPrime.radiusCutoff S ≤ N) {F G : WeightedSpace}
    (hF : F ∈ supportedSubspace R) (hG : G ∈ supportedSubspace R) :
    completeForm R C (RhAllPrime.radiusCutoff R) F G = completeForm R C N F G :=
  completeForm_horizon_eq C (coversActive_of_radiusCutoff le_rfl)
    (coversActive_mono_radius hRS (coversActive_of_radiusCutoff hN)) hF hG

/-- The actual transported complete forms also agree exactly whenever the
fixed horizons cover the enlarged support; no graph-unitarity is assumed. -/
theorem pulledForm_horizon_eq {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) {N M : ℕ}
    (hN : CoversActive (r * R) N) (hM : CoversActive (r * R) M) :
    pulledForm (R := R) hr C N = pulledForm (R := R) hr C M := by
  ext F G
  rw [pulledForm_apply, pulledForm_apply]
  exact completeForm_horizon_eq C hN hM
    (flatCore_supported (r * R) (RhFlatCoreDilation.outwardMap hr F).property)
    (flatCore_supported (r * R) (RhFlatCoreDilation.outwardMap hr G).property)

/-- Actual physical anchored primitives identify the fixed cap with the
native all-radius kernel, at the exact native scalar. -/
theorem radius_primitive_fixed_horizon {R : ℝ} (hR : 0 < R) {N : ℕ}
    (hN : RhAllPrime.radiusCutoff R ≤ N) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) :
    completeForm R archConstant N
      (RhWeightedPrimitiveLift.actualPrimitiveLift hR v hv)
      (RhWeightedPrimitiveLift.actualPrimitiveLift hR v hv) =
      kernelQuadratic R (RhAllPrime.radiusKernel R) v := by
  rw [RhNativeCompleteDictionary.completeForm_actual hR hv N]
  exact (RhCompleteDilationDictionary.radius_quadratic_fixed_horizon hR.le N hN v).symm

/-- Positivity equivalence for the ACTUAL all-radius kernel and its fixed
finite-cap complete form. No positivity is asserted by this dictionary. -/
theorem radius_physical_positive_iff_fixed_form_positive {R : ℝ} (hR : 0 < R) {N : ℕ}
    (hN : RhAllPrime.radiusCutoff R ≤ N) :
    (∀ v : ℝ → ℝ, MemLp v 2 (physicalMeasure R) →
      0 ≤ kernelQuadratic R (RhAllPrime.radiusKernel R) v) ↔
      (∀ F : FlatCoreSpace R,
        0 ≤ completeForm R archConstant N (F : WeightedSpace) (F : WeightedSpace)) := by
  rw [← RhSmoothPhysicalTransfer.physical_positive_iff_complete_form_positive hR N]
  constructor
  · intro hp v hv
    rw [← RhCompleteDilationDictionary.radius_quadratic_fixed_horizon hR.le N hN v]
    exact hp v hv
  · intro hp v hv
    rw [RhCompleteDilationDictionary.radius_quadratic_fixed_horizon hR.le N hN v]
    exact hp v hv

/-- Exact native-radius member represented through ONE cap on the whole
bounded support range. This permits fixed-cap continuity arguments without
claiming uniformity in a varying arithmetic horizon. -/
theorem pulledForm_radius_fixed_cap {R r S : ℝ} (hr : 1 ≤ r)
    (hcap : r * R ≤ S) (C : ℝ) {N : ℕ} (hN : RhAllPrime.radiusCutoff S ≤ N) :
    pulledForm (R := R) hr C (RhAllPrime.radiusCutoff (r * R)) =
      pulledForm (R := R) hr C N :=
  pulledForm_horizon_eq hr C (coversActive_of_radiusCutoff le_rfl)
    (coversActive_mono_radius hcap (coversActive_of_radiusCutoff hN))

theorem bounded_radius_physical_positive_iff_fixed_form_positive {R S : ℝ}
    (hR : 0 < R) (hRS : R ≤ S) {N : ℕ} (hN : RhAllPrime.radiusCutoff S ≤ N) :
    (∀ v : ℝ → ℝ, MemLp v 2 (physicalMeasure R) →
      0 ≤ kernelQuadratic R (RhAllPrime.radiusKernel R) v) ↔
      (∀ F : FlatCoreSpace R,
        0 ≤ completeForm R archConstant N (F : WeightedSpace) (F : WeightedSpace)) :=
  radius_physical_positive_iff_fixed_form_positive hR
    ((RhAllPrime.radiusCutoff_mono hRS).trans hN)
end RhCompleteFormHorizon
#print axioms RhCompleteFormHorizon.shiftPair_zero_of_threshold
#print axioms RhCompleteFormHorizon.completeForm_horizon_eq
#print axioms RhCompleteFormHorizon.bounded_radius_form_horizon
#print axioms RhCompleteFormHorizon.pulledForm_horizon_eq
#print axioms RhCompleteFormHorizon.radius_primitive_fixed_horizon
#print axioms RhCompleteFormHorizon.radius_physical_positive_iff_fixed_form_positive
#print axioms RhCompleteFormHorizon.pulledForm_radius_fixed_cap
#print axioms RhCompleteFormHorizon.bounded_radius_physical_positive_iff_fixed_form_positive
