import RhFlatCoreDilation001
import RhNativeGraphCoercivity001

/-! Actual common-domain complete arithmetic forms. The form is pulled back
through the constructed physical dilation on the SAME real closed smooth
core. Its full signed difference is explicit; no positivity or coercivity is
assumed and the exact finite arithmetic horizon is common to both radii.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhPulledCompleteForm
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear

abbrev CoreBilinear (R : ℝ) := FlatCoreSpace R →L[ℝ] FlatCoreSpace R →L[ℝ] ℝ

def baseForm (R C : ℝ) (N : ℕ) : CoreBilinear R :=
  RhNativeGraphCoercivity.restrictedForm R C N (flatCore R)

/-- The actual native form at the enlarged radius, transported to the fixed
complete domain by the actual physical unitary dilation. -/
def pulledForm {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ) : CoreBilinear R :=
  (baseForm (r * R) C N).bilinearComp
    (RhFlatCoreDilation.outwardMap hr) (RhFlatCoreDilation.outwardMap hr)

lemma baseForm_apply (R C : ℝ) (N : ℕ) (F G : FlatCoreSpace R) :
    baseForm R C N F G = completeForm R C N (F : WeightedSpace) (G : WeightedSpace) := rfl

lemma pulledForm_apply {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ) (F G : FlatCoreSpace R) :
    pulledForm hr C N F G = completeForm (r * R) C N
      (RhFlatCoreDilation.outwardMap hr F : WeightedSpace)
      (RhFlatCoreDilation.outwardMap hr G : WeightedSpace) := rfl

lemma pulledForm_norm_bound {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (F G : FlatCoreSpace R) :
    ‖pulledForm hr C N F G‖ ≤ ‖completeForm (r * R) C N‖ * ‖F‖ * ‖G‖ := by
  rw [pulledForm_apply]
  calc
    _ ≤ ‖completeForm (r * R) C N‖ * ‖RhFlatCoreDilation.outwardMap hr F‖ *
        ‖RhFlatCoreDilation.outwardMap hr G‖ := by
      simpa only [Submodule.norm_coe] using
        (completeForm (r * R) C N).le_opNorm₂
          (RhFlatCoreDilation.outwardMap hr F : WeightedSpace)
          (RhFlatCoreDilation.outwardMap hr G : WeightedSpace)
    _ ≤ _ := by
      gcongr
      · exact RhFlatCoreDilation.outwardMap_norm_le hr F
      · exact RhFlatCoreDilation.outwardMap_norm_le hr G

/-- The exact difference is first constructed algebraically, avoiding any
inferred curried-dual additive structure. -/
def differenceLinear {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ) :
    FlatCoreSpace R →ₗ[ℝ] FlatCoreSpace R →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun F G => pulledForm hr C N F G - baseForm R C N F G)
    (by intro F G H; simp only [map_add, ContinuousLinearMap.add_apply]; ring)
    (by intro c F G; simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring)
    (by intro F G H; simp only [map_add]; ring)
    (by intro c F G; simp only [map_smul, smul_eq_mul]; ring)

lemma differenceLinear_bound {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (F G : FlatCoreSpace R) :
    ‖differenceLinear hr C N F G‖ ≤
      (‖completeForm (r * R) C N‖ + ‖completeForm R C N‖) * ‖F‖ * ‖G‖ := by
  have hb : ‖baseForm R C N F G‖ ≤ ‖completeForm R C N‖ * ‖F‖ * ‖G‖ := by
    simpa only [baseForm_apply, Submodule.norm_coe] using
      (completeForm R C N).le_opNorm₂ (F : WeightedSpace) (G : WeightedSpace)
  calc
    _ = ‖pulledForm hr C N F G - baseForm R C N F G‖ := rfl
    _ ≤ ‖pulledForm hr C N F G‖ + ‖baseForm R C N F G‖ := norm_sub_le _ _
    _ ≤ ‖completeForm (r * R) C N‖ * ‖F‖ * ‖G‖ +
        ‖completeForm R C N‖ * ‖F‖ * ‖G‖ :=
      add_le_add (pulledForm_norm_bound hr C N F G) hb
    _ = _ := by ring

/-- Genuine continuous exact bilinear difference on ONE complete domain.
Continuity follows from the actual native operator norms, not a target premise. -/
def differenceForm {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ) : CoreBilinear R :=
  (differenceLinear (R := R) hr C N).mkContinuous₂
    (‖completeForm (r * R) C N‖ + ‖completeForm R C N‖)
    (differenceLinear_bound hr C N)

lemma differenceForm_apply {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ) (F G : FlatCoreSpace R) :
    differenceForm hr C N F G = pulledForm hr C N F G - baseForm R C N F G := rfl

lemma outward_one_ambient {R : ℝ} (F : FlatCoreSpace R) :
    (RhFlatCoreDilation.outwardMap (r := 1) (le_refl 1) F : WeightedSpace) = (F : WeightedSpace) := by
  apply physicalEmbedding_injective
  apply Lp.ext
  have h := RhFlatCoreDilation.outwardMap_physical_ae (r := 1) (le_refl 1) F
  filter_upwards [h] with t ht
  simpa [RhDilation.complexDilate] using ht

/-- The unperturbed row really IS q_1, not an unrelated chosen baseline. -/
theorem pulledForm_one (R C : ℝ) (N : ℕ) :
    pulledForm (R := R) (r := 1) (le_refl 1) C N = baseForm R C N := by
  ext F G
  simp only [pulledForm_apply, outward_one_ambient]
  rw [one_mul, baseForm_apply]

theorem differenceForm_is_qr_sub_q1 {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (F G : FlatCoreSpace R) :
    differenceForm hr C N F G = pulledForm hr C N F G -
      pulledForm (R := R) (r := 1) (le_refl 1) C N F G := by
  rw [pulledForm_one]
  rfl

theorem pulledForm_symmetric {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ) (F G : FlatCoreSpace R) :
    pulledForm hr C N F G = pulledForm hr C N G F :=
  completeForm_symmetric (r * R) C N _ _

theorem differenceForm_symmetric {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ) (F G : FlatCoreSpace R) :
    differenceForm hr C N F G = differenceForm hr C N G F := by
  rw [differenceForm_apply, differenceForm_apply, pulledForm_symmetric hr C N F G,
    baseForm_apply, baseForm_apply, completeForm_symmetric R C N (F : WeightedSpace) (G : WeightedSpace)]

/-- Exact ALL-COMPONENT signed perturbation. Both complex moment components
and both spatial translations remain attached; no covariance is discarded.
This identity does not assert a small norm or a sign for the perturbation. -/
theorem differenceForm_native_expansion {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (F G : FlatCoreSpace R) :
    let Fr : WeightedSpace := RhFlatCoreDilation.outwardMap hr F
    let Gr : WeightedSpace := RhFlatCoreDilation.outwardMap hr G
    differenceForm hr C N F G =
      (archPair Fr Gr - archPair (F : WeightedSpace) (G : WeightedSpace)) -
      C * (spatialPair Fr Gr - spatialPair (F : WeightedSpace) (G : WeightedSpace)) +
      2 * (coshPair (r * R) Fr Gr - coshPair R (F : WeightedSpace) (G : WeightedSpace)) -
      2 * (sinhPair (r * R) Fr Gr - sinhPair R (F : WeightedSpace) (G : WeightedSpace)) -
      ∑ n ∈ Finset.Icc 2 N, RhAllPrime.weight n *
        (shiftPair (Real.log (n : ℝ)) Fr Gr -
          shiftPair (Real.log (n : ℝ)) (F : WeightedSpace) (G : WeightedSpace)) := by
  dsimp only
  rw [differenceForm_apply, pulledForm_apply, baseForm_apply]
  change archPair _ _ + boundedPart (r * R) C N _ _ -
    (archPair _ _ + boundedPart R C N _ _) = _
  rw [boundedPart_apply, boundedPart_apply]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end RhPulledCompleteForm
#print axioms RhPulledCompleteForm.pulledForm_one
#print axioms RhPulledCompleteForm.differenceForm_is_qr_sub_q1
#print axioms RhPulledCompleteForm.pulledForm_symmetric
#print axioms RhPulledCompleteForm.differenceForm_symmetric
#print axioms RhPulledCompleteForm.differenceForm_native_expansion
