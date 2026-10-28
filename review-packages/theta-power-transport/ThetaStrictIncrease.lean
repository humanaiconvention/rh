import ThetaPositiveSlope

/-!
Strict increase of the actual complete unnormalized ratio on [0,∞).
Continuity is supplied at every point, including0. Positive derivative is
required only on the interior; F'(0)=0 is therefore compatible with the result.
-/
noncomputable section
open Set

namespace ThetaMacdonald.Monotonicity

theorem strictMonoOn_ratio :
    StrictMonoOn Complete.ratio (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
  · intro u _
    exact (Complete.hasDerivAt_ratio u).continuousAt.continuousWithinAt
  · intro u hu
    exact Slope.deriv_ratio_pos (by simpa only [interior_Ici, mem_Ioi] using hu)

end ThetaMacdonald.Monotonicity

#print axioms ThetaMacdonald.Monotonicity.strictMonoOn_ratio
