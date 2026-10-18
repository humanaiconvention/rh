import RhNativeRadiusFamily001
import RhNativeStrictInteriorUCP001

/-! PRIVATE radial spectral consequence of actual compact-domain attainment and
strict-interior weak-null uniqueness. Every fixed finite horizon is retained.
The scalar shift does not change any rank or prime-power companion.
Strict decrease determines NO sign and proves neither all-radius positivity
nor existence/exclusion of an actual zero bottom. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open Set MeasureTheory
open scoped Topology
namespace RhNativeRayleighStrict
open RhAnchored RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhNativeRayleighDomain RhNativeRayleighPositivity RhNativeRayleighRadius
open RhNativeRadiusFamily RhNativeCompactGap

lemma completeForm_scalar_shift (R C a : ℝ) (N : ℕ) (F G : WeightedSpace) :
    completeForm R (C+a) N F G =
      completeForm R C N F G - a * spatialPair F G := by
  change archPair F G + boundedPart R (C+a) N F G =
    archPair F G + boundedPart R C N F G - a * spatialPair F G
  rw [boundedPart_apply, boundedPart_apply]
  ring

lemma diagonal_scalar_shift (R C a : ℝ) (N : ℕ) (F : FlatCoreSpace R) :
    diagonal R (C+a) N F =
      diagonal R C N F - a * ‖physicalEmbedding (F : WeightedSpace)‖^2 := by
  unfold RhNativeRayleighDomain.diagonal
  rw [completeForm_scalar_shift, spatialPair_apply, real_inner_self_eq_norm_sq]

/-- Exact translation of a genuine bounded-below nonempty Rayleigh infimum. -/
theorem bottom_scalar_shift {R : ℝ} (hR : 0 < R) (C a : ℝ) (N : ℕ) :
    bottom R (C+a) N = bottom R C N - a := by
  have he : ∀ F ∈ physicalUnit R,
      diagonal R (C+a) N F = diagonal R C N F - a := by
    intro F hF
    rw [diagonal_scalar_shift, hF]
    ring
  obtain ⟨_hb,hlo,hhi⟩ := RhVariationalInfimum.affine_infimum_bounds
    (physicalUnit_nonempty hR) (diagonal_bddBelow R C N)
    (g := RhNativeRayleighDomain.diagonal R (C+a) N)
    (a:=1) (b := -a) (c:=1) (d := -a) (by norm_num) (by norm_num)
    (fun F hF => by rw [he F hF]; ring_nf; exact le_rfl)
    (fun F hF => by rw [he F hF]; ring_nf; exact le_rfl)
  change 1 * bottom R C N + -a ≤ bottom R (C+a) N at hlo
  change bottom R (C+a) N ≤ 1 * bottom R C N + -a at hhi
  linarith

/-- The arbitrary bottom is attained after its exact scalar shift to zero.
The returned nonzero vector is in the TRUE shifted form radical. -/
theorem bottom_has_shifted_null {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ) :
    ∃ F : FlatCoreSpace R, F ≠ 0 ∧
      F ∈ (form R (C + bottom R C N) N).ker := by
  apply zero_bottom_has_actual_null hR (C + bottom R C N) N
  rw [bottom_scalar_shift hR C (bottom R C N) N]
  ring

/-- Genuine PHYSICAL-unit minimizer for any real scalar C and finite cap N.
This is primitive-coordinate attainment, not a derivative-input L2 estimate. -/
theorem bottom_attained {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ) :
    ∃ F : FlatCoreSpace R, F ∈ physicalUnit R ∧
      diagonal R C N F = bottom R C N := by
  obtain ⟨p,hp,hker⟩ := bottom_has_shifted_null hR C N
  have hn := physical_norm_pos hp
  let c : ℝ := ‖physicalEmbedding (p : WeightedSpace)‖⁻¹
  have hc : 0 < c := inv_pos.mpr hn
  have hu : c • p ∈ physicalUnit R := by
    change ‖physicalEmbedding (c • (p : WeightedSpace))‖ = 1
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    exact inv_mul_cancel₀ hn.ne'
  have hz : diagonal R (C + bottom R C N) N p = 0 := by
    change form R (C + bottom R C N) N p p = 0
    change form R (C + bottom R C N) N p = 0 at hker
    rw [hker]
    rfl
  have hz' : diagonal R (C + bottom R C N) N (c • p) = 0 := by
    rw [diagonal_smul,hz,mul_zero]
  rw [diagonal_scalar_shift,hu] at hz'
  refine ⟨c • p,hu,?_⟩
  nlinarith

/-- Strict radial decrease for one common finite prime horizon. A tie would
make a smaller supported minimizer a full weak null on the larger window. -/
theorem bottom_strict_antitone_support {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (C : ℝ) (N : ℕ) : bottom S C N < bottom R C N := by
  have hle := bottom_antitone_support hR hRS.le C N
  apply lt_of_le_of_ne hle
  intro heq
  let a : ℝ := bottom R C N
  have hzero : bottom S (C+a) N = 0 := by
    rw [bottom_scalar_shift (hR.trans hRS) C a N,heq]
    dsimp [a]
    ring
  have hpos := (bottom_nonnegative_iff (hR.trans hRS) (C+a) N).mp hzero.ge
  obtain ⟨p,hp,hker⟩ := bottom_has_shifted_null hR C N
  have hsmall : completeForm R (C+a) N (p : WeightedSpace) (p : WeightedSpace) = 0 := by
    change form R (C+a) N p p = 0
    change form R (C+a) N p = 0 at hker
    rw [hker]
    rfl
  have hlarge := RhLiteralSupportForm.old_null_diagonal_stays_zero hRS.le
    (C+a) N p hsmall
  let P : FlatCoreSpace S := ⟨(p : WeightedSpace),
    RhLiteralSupportForm.flatCore_mono hRS.le p.property⟩
  have hPrad : form S (C+a) N P = 0 :=
    RhCompactPositiveSequence.zero_diagonal_radical (form S (C+a) N)
      (form_symmetric S (C+a) N) hpos hlarge
  have hrow : ∀ g : FlatCoreSpace S,
      completeForm S (C+a) N (p : WeightedSpace) (g : WeightedSpace) = 0 := by
    intro g
    change form S (C+a) N P g = 0
    rw [hPrad]
    rfl
  exact hp (RhNativeStrictInteriorUCP.full_row_unique hR hRS (C+a) N p hrow)

/-- Actual all-prime ground strictness: choose the larger sufficient cap
FIRST, then use the fixed-horizon theorem. No prime sum limit occurs. -/
theorem nativeBottom_strict_antitone {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (C : ℝ) : nativeBottom S C < nativeBottom R C := by
  rw [nativeBottom_fixed_cap (R:=R) hRS.le C
    (N:=RhAllPrime.radiusCutoff S) le_rfl]
  exact bottom_strict_antitone_support hR hRS C (RhAllPrime.radiusCutoff S)

end RhNativeRayleighStrict
#print axioms RhNativeRayleighStrict.completeForm_scalar_shift
#print axioms RhNativeRayleighStrict.bottom_scalar_shift
#print axioms RhNativeRayleighStrict.bottom_has_shifted_null
#print axioms RhNativeRayleighStrict.bottom_attained
#print axioms RhNativeRayleighStrict.bottom_strict_antitone_support
#print axioms RhNativeRayleighStrict.nativeBottom_strict_antitone
