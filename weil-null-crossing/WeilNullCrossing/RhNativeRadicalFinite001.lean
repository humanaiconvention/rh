import RhNativeCompactGap001
import RhPulledCompleteForm001

/-! Finite actual radical WITHOUT positivity of the original form. Restrict
compact physical embedding and graph control to q.ker, where the form is
exactly zero, then use compactness of that actual closed domain. -/
noncomputable section
set_option maxHeartbeats 150000
open Set Filter
open scoped Topology
namespace RhCompactRadicalFinite

/-- Positivity and symmetry of q are unnecessary: its actual left radical
has zero row identically, and compact physical embedding controls its graph
norm. The positive helper is used only for the ZERO form on this radical. -/
theorem finite_radical {V H : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (q : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] H)
    (hJ : IsCompactOperator J) {G : ℝ} (hG : 0 ≤ G)
    (hgraph : ∀ x : V, ‖x‖^2 ≤ q x x + G*‖J x‖^2) :
    FiniteDimensional ℝ q.ker := by
  let K := q.ker
  letI : CompleteSpace K := q.isClosed_ker.completeSpace_coe
  let Jk : K →L[ℝ] H := J.comp K.subtypeL
  let zform : K →L[ℝ] K →L[ℝ] ℝ := 0
  have hJk : IsCompactOperator Jk := hJ.comp_clm K.subtypeL
  have hzero (x : K) : q (x : V) (x : V) = 0 := by
    have hx : q (x : V) = 0 := x.property
    rw [hx]
    rfl
  have hg : ∀ x : K, ‖x‖^2 ≤ zform x x + G*‖Jk x‖^2 := by
    intro x
    have hh := hgraph (x : V)
    rw [hzero x] at hh
    exact hh
  letI : FiniteDimensional ℝ zform.ker :=
    RhCompactPositiveKernel.finite_nullspace zform Jk hJk hG
      (by intro x; simp [zform]) (by intro x y; rfl) hg
  let inclusion : K →ₗ[ℝ] zform.ker :=
    { toFun := fun x => ⟨x, by change zform x = 0; rfl⟩
      map_add' := by intro x y; apply Subtype.ext; rfl
      map_smul' := by intro c x; apply Subtype.ext; rfl }
  exact FiniteDimensional.of_injective inclusion (fun x y h => congrArg Subtype.val h)

end RhCompactRadicalFinite
namespace RhNativeRadicalFinite
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhNativeCompactGap RhPulledCompleteForm

/-- At every positive finite radius, every scalar C and finite horizon N,
the actual complete-form radical is finite dimensional. No PSD assumption
or assertion of existence/nonexistence of a nonzero radical is made. -/
theorem finite_native_radical {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ) :
    FiniteDimensional ℝ (form R C N).ker := by
  apply RhCompactRadicalFinite.finite_radical (form R C N) (physical R)
    (physical_compact hR)
    (by have hK := RhCompleteFormBound.boundConstant_nonneg R C N; positivity)
    (actual_graph_control R C N)

/-- The common fixed-domain form has the identical actual radical, so this
is the declaration needed for arbitrary-sign radial continuation audits. -/
theorem finite_base_radical {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ) :
    FiniteDimensional ℝ (baseForm R C N).ker := by
  apply RhCompactRadicalFinite.finite_radical
    (G := RhCompleteFormBound.boundConstant R C N + 1) (baseForm R C N) (physical R)
    (physical_compact hR)
    (by have hK := RhCompleteFormBound.boundConstant_nonneg R C N; positivity)
  intro x
  exact actual_graph_control R C N x

end RhNativeRadicalFinite
#print axioms RhCompactRadicalFinite.finite_radical
#print axioms RhNativeRadicalFinite.finite_native_radical
#print axioms RhNativeRadicalFinite.finite_base_radical


