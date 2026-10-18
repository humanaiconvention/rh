import RhPhysicalProjectionSchur001
import RhLiteralSupportForm001
import RhSupportedInwardStrong001
import Mathlib.Topology.Sequences

/-! Actual inward old-null vectors in the FIXED real form core. Inward
dilation is followed by literal support inclusion; outward dilation then
returns the literal old vector exactly. All signed native components remain
inside the complete form with ONE common finite prime horizon. -/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RhInwardOldNullLift
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPulledCompleteForm

lemma inward_radius_le {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r) : r⁻¹ * R ≤ R := by
  have hr0 : 0 < r := by linarith
  have hi : r⁻¹ ≤ 1 := (inv_le_one₀ hr0).mpr hr
  nlinarith

def oldNullLift {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (p : FlatCoreSpace R) : FlatCoreSpace R :=
  ⟨(RhFlatCoreDilation.inwardMap hr p : WeightedSpace),
    RhLiteralSupportForm.flatCore_mono (inward_radius_le hR hr)
      (RhFlatCoreDilation.inwardMap hr p).property⟩

lemma oldNullLift_ambient {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (p : FlatCoreSpace R) :
    (oldNullLift hR hr p : WeightedSpace) =
      (RhFlatCoreDilation.inwardMap hr p : WeightedSpace) := rfl

/-- The true outward inverse returns literal old support, not a rescaled old
vector or a graph-unitary surrogate. -/
theorem outward_oldNullLift_ambient {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (p : FlatCoreSpace R) :
    (RhFlatCoreDilation.outwardMap hr (oldNullLift hR hr p) : WeightedSpace) =
      (p : WeightedSpace) := by
  have he := RhFlatCoreDilation.outward_ambient_congr hr (oldNullLift hR hr p)
    (RhFlatCoreDilation.inwardMap hr p) (oldNullLift_ambient hR hr p)
  exact he.trans (RhFlatCoreDilation.outward_inward_cancel hr p)

/-- Actual full pair identity, including both ranks and every finite prime
shift; no arithmetic componentwise cancellation is inferred. -/
theorem pulledForm_oldNullLift_pair {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p q : FlatCoreSpace R) :
    pulledForm hr C N (oldNullLift hR hr p) (oldNullLift hR hr q) =
      baseForm R C N p q := by
  rw [pulledForm_apply, outward_oldNullLift_ambient hR hr p,
    outward_oldNullLift_ambient hR hr q, baseForm_apply]
  have hRS : R ≤ r * R := by nlinarith
  exact (RhLiteralSupportForm.completeForm_support_invariant hRS C N
    (p : WeightedSpace) (q : WeightedSpace)
    (flatCore_supported R p.property) (flatCore_supported R q.property)).symm

theorem old_null_diagonal_zero {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : FlatCoreSpace R) (hp : baseForm R C N p p = 0) :
    pulledForm hr C N (oldNullLift hR hr p) (oldNullLift hR hr p) = 0 := by
  rw [pulledForm_oldNullLift_pair hR hr C N, hp]

/-- Strong convergence in the ACTUAL weighted complete form norm, for any
sequence of local outward scales. No finite-dimensional or nullness premise. -/
theorem oldNullLift_norm_tendsto {r : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hr1 : ∀ n, 1 ≤ r n) (hr2 : ∀ n, r n ≤ 2)
    (hr : Tendsto r atTop (𝓝 1)) (p : FlatCoreSpace R) :
    Tendsto (fun n => ‖oldNullLift hR (hr1 n) p - p‖) atTop (𝓝 0) := by
  let F : SupportedSpace R := ⟨(p : WeightedSpace), flatCore_supported R p.property⟩
  have he (n : ℕ) : (oldNullLift hR (hr1 n) p : WeightedSpace) =
      (RhWeightedInwardMap.inwardMap (hr1 n) F : WeightedSpace) := rfl
  have hh := RhSupportedInwardStrong.supported_inward_norm_tendsto hr1 hr2 hr F
  change Tendsto (fun n => ‖(oldNullLift hR (hr1 n) p : WeightedSpace) -
    (p : WeightedSpace)‖) atTop (𝓝 0)
  simpa only [he] using hh

abbrev Scale := Set.Icc (1 : ℝ) 2

def oneScale : Scale := ⟨1, by constructor <;> norm_num⟩

/-- A genuine local topological limit, not only the canonical shrinking
sequence. Icc[1,2] loses no outward neighborhood of scale one. -/
theorem oldNullLift_tendsto {R : ℝ} (hR : 0 < R) (p : FlatCoreSpace R) :
    Tendsto (fun r : Scale => oldNullLift hR r.property.1 p)
      (𝓝 oneScale) (𝓝 p) := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro r hr
  have hc : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 1) := by
    simpa only [oneScale, Function.comp_def] using (continuous_subtype_val.tendsto oneScale).comp hr
  have hn := oldNullLift_norm_tendsto hR (fun n => (r n).property.1)
    (fun n => (r n).property.2) hc p
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end RhInwardOldNullLift
#print axioms RhInwardOldNullLift.outward_oldNullLift_ambient
#print axioms RhInwardOldNullLift.pulledForm_oldNullLift_pair
#print axioms RhInwardOldNullLift.old_null_diagonal_zero
#print axioms RhInwardOldNullLift.oldNullLift_norm_tendsto
#print axioms RhInwardOldNullLift.oldNullLift_tendsto