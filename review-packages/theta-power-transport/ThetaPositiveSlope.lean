import ThetaOriginStationarity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Strict positivity of the actual complete ratio's first derivative on (0,∞).
The endpoint continuity needed by the mean-value theorem is supplied by
the accepted actual second derivative, not inferred from curvature alone.
No probability normalization or source-order premise is assumed.
-/
noncomputable section
open Set

namespace ThetaMacdonald.Slope

theorem hasDerivAt_deriv_ratio (u : ℝ) :
    HasDerivAt (deriv Complete.ratio) (Complete.ratioD2 u) u := by
  have hd : deriv Complete.ratio = Complete.ratioD1 :=
    funext fun v => (Complete.hasDerivAt_ratio v).deriv
  rw [hd]
  exact Complete.hasDerivAt_ratioD1 u

/-- Strict increase includes the closed endpoint, using actual continuity. -/
theorem strictMonoOn_deriv_ratio :
    StrictMonoOn (deriv Complete.ratio) (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
  · intro u _
    exact (hasDerivAt_deriv_ratio u).continuousAt.continuousWithinAt
  · intro u hu
    exact Complete.second_deriv_ratio_pos (interior_subset hu)

/-- The sole mathematical hypothesis is u>0. F'(0)=0 is an accepted theorem. -/
theorem deriv_ratio_pos {u : ℝ} (hu : 0 < u) :
    0 < deriv Complete.ratio u := by
  have h : deriv Complete.ratio 0 < deriv Complete.ratio u :=
    strictMonoOn_deriv_ratio
      (show (0 : ℝ) ∈ Ici (0 : ℝ) by simp)
      (show u ∈ Ici (0 : ℝ) from hu.le) hu
  simpa only [Symmetry.deriv_ratio_zero] using h

end ThetaMacdonald.Slope

#print axioms ThetaMacdonald.Slope.hasDerivAt_deriv_ratio
#print axioms ThetaMacdonald.Slope.strictMonoOn_deriv_ratio
#print axioms ThetaMacdonald.Slope.deriv_ratio_pos
