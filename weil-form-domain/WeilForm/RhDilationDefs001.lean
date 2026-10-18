import RhAnchoredSpace001

/-! Actual real interval dilation definitions. No measure preservation is
asserted: the Jacobian is handled by the physical lemmas. -/
noncomputable section
namespace RhDilation

def dilate (r : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  (Real.sqrt r)⁻¹*w (t/r)

def pullback (r : ℝ) (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  r*Real.sqrt r*v (r*x)

lemma dilate_one (w : ℝ → ℝ) : dilate 1 w=w := by
  funext t
  simp [dilate]

lemma pullback_one (v : ℝ → ℝ) : pullback 1 v=v := by
  funext t
  simp [pullback]

end RhDilation
#print axioms RhDilation.dilate_one
#print axioms RhDilation.pullback_one

