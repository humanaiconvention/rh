import RhInteriorSmoothCutoff001
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-! Ordinary physical L2 density with strictly interior C-infinity support.
This is not a weighted Fourier density theorem. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal
namespace RhInteriorSmoothDensity
open RhAnchored RhInteriorSmoothCutoff

/-- Every actual physical L2 vector has a C-infinity compact approximation
strictly inside the same support radius, in the actual L2 quotient norm. -/
theorem exists_interior_smooth_approx {R : ℝ} (hR : 0 < R) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) {eps : ℝ} (heps : 0 < eps) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo (-R) R ∧
      ∃ hf : MemLp f 2 (physicalMeasure R), ‖hf.toLp f - hv.toLp v‖ < eps := by
  obtain ⟨g, hgc, hgs, hge⟩ :=
    MemLp.exist_eLpNorm_sub_le (p := 2) (by norm_num) (by norm_num) hv
      (show 0 < eps / 3 by positivity)
  have hgm : MemLp g 2 (physicalMeasure R) := RhDilationRank.continuous_memLp hgs.continuous
  have hVG : ‖hv.toLp v - hgm.toLp g‖ ≤ eps / 3 := by
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hge
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ eps / 3)] using h
  have hsmall : ∀ᶠ n in atTop,
      ‖(cutoff_mul_memLp hR n hgs.continuous).toLp (fun t => cutoff R hR n t * g t) -
        hgm.toLp g‖ < eps / 3 :=
    (tendsto_order.1 (cutoff_L2_error_tendsto hR hgs.continuous)).2 _ (by positivity)
  obtain ⟨n, hn⟩ := hsmall.exists
  let f : ℝ → ℝ := fun t => cutoff R hR n t * g t
  have hf : MemLp f 2 (physicalMeasure R) := cutoff_mul_memLp hR n hgs.continuous
  refine ⟨f, (cutoff_contDiff hR n).mul hgs, (cutoff_hasCompactSupport hR n).mul_right,
    tsupport_mul_subset_left.trans (cutoff_tsupport hR n), hf, ?_⟩
  have hGV : ‖hgm.toLp g - hv.toLp v‖ ≤ eps / 3 := by
    simpa only [norm_sub_rev] using hVG
  have htri := dist_triangle (hf.toLp f) (hgm.toLp g) (hv.toLp v)
  simp only [dist_eq_norm] at htri
  change ‖hf.toLp f - hgm.toLp g‖ < eps / 3 at hn
  linarith

end RhInteriorSmoothDensity
#print axioms RhInteriorSmoothDensity.exists_interior_smooth_approx
