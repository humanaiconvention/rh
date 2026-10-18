import RhNativeDilationSmallness001
import RhSymmetricFormPolarization001

/-! Genuine full bilinear local graph-form smallness of the actual native
complete arithmetic perturbation, by exact real polarization. No cross-term
estimate or positivity is inserted as a premise.
-/
noncomputable section
open RhFlatSmoothCore RhPulledCompleteForm
namespace RhNativeBilinearSmallness

theorem uniform_actual_bilinear_smallness {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (r : ℝ) (hr : 1 ≤ r), |r - 1| < delta →
      ∀ F G : FlatCoreSpace R,
        |differenceForm hr C N F G| ≤ eta * ‖F‖ * ‖G‖ := by
  obtain ⟨delta, hdelta, hd⟩ :=
    RhNativeDilationSmallness.uniform_actual_graph_form_smallness hR C N heta
  refine ⟨delta, hdelta, ?_⟩
  intro r hr hclose F G
  exact RhSymmetricFormPolarization.bilinear_bound_of_diagonal
    (differenceForm (R := R) hr C N) (differenceForm_symmetric hr C N) heta.le
    (hd r hr hclose) F G

end RhNativeBilinearSmallness
#print axioms RhNativeBilinearSmallness.uniform_actual_bilinear_smallness
