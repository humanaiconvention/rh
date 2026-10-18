import RhInteriorSmoothCutoff001
import RhSmoothPrimitiveMass001
import Mathlib.Analysis.Calculus.BumpFunction.Normed

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RhActualCoreBump
open RhAnchored RhInteriorSmoothCutoff

/-- All bumps, not merely an eventual tail, fit strictly inside the physical radius. -/
def centralBump (R : ℝ) (hR : 0 < R) (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := delta R n / 4
  rOut := delta R n / 2
  rIn_pos := div_pos (delta_pos hR n) (by norm_num)
  rIn_lt_rOut := by linarith [delta_pos hR n]

lemma rOut_tendsto (R : ℝ) (hR : 0 < R) :
    Tendsto (fun n => (centralBump R hR n).rOut) atTop (𝓝 0) := by
  simpa only [centralBump, zero_div] using (delta_tendsto R).div_const 2

lemma normed_tsupport {R : ℝ} (hR : 0 < R) (n : ℕ) :
    tsupport ((centralBump R hR n).normed volume) ⊆ Ioo (-R) R := by
  rw [(centralBump R hR n).tsupport_normed_eq]
  intro t ht
  have ha : |t| ≤ delta R n / 2 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, centralBump] using ht
  have hd0 := delta_pos hR n
  have hdR := delta_lt hR n
  have hab := abs_le.mp ha
  constructor <;> linarith [hab.1, hab.2]

lemma normed_totalMass {R : ℝ} (hR : 0 < R) (n : ℕ) :
    totalMass R ((centralBump R hR n).normed volume) = 1 := by
  rw [RhSmoothPrimitiveMass.totalMass_eq_integral]
  · exact (centralBump R hR n).integral_normed
  · intro t ht
    have h := normed_tsupport hR n (subset_tsupport _ ht)
    exact ⟨h.1.le, h.2.le⟩

end RhActualCoreBump
#print axioms RhActualCoreBump.rOut_tendsto
#print axioms RhActualCoreBump.normed_tsupport
#print axioms RhActualCoreBump.normed_totalMass
