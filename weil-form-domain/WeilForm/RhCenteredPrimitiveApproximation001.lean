import RhPrimitiveBumpMass001
import RhAllPrimeUnclosedTarget001

/-! Actual centering-error convergence in complete positive archimedean energy
and primitive L2 mass. The assumptions concern physical L2 source convergence,
scalar convergence, and explicit normalized bumps; energy convergence is proved.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhCenteredPrimitiveApproximation
open RhAnchored RhAllPrimeTarget RhNativeArchKernel RhNativeBumpCapacity
open RhPrimitiveApproximation RhPrimitiveBumpMass

abbrev energy (R : ℝ) (v : ℝ → ℝ) : ℝ := kernelQuadratic R energyKernel v
abbrev primitiveMass (R : ℝ) (v : ℝ → ℝ) : ℝ :=
  ∫ t in interval R, (primitive R v t) ^ 2

lemma pair_smul_first (R : ℝ) (K : ℝ → ℝ → ℝ) (c : ℝ) (f g : ℝ → ℝ) :
    pair R K (c • f) g = c * pair R K f g := by
  unfold pair
  calc
    _ = ∫ p : ℝ × ℝ, c * (K p.1 p.2 * f p.2 * g p.1)
        ∂((physicalMeasure R).prod (physicalMeasure R)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by dsimp only [Pi.smul_apply, smul_eq_mul]; ring)
    _ = _ := integral_const_mul c _

lemma pair_smul_second (R : ℝ) (K : ℝ → ℝ → ℝ) (c : ℝ) (f g : ℝ → ℝ) :
    pair R K f (c • g) = c * pair R K f g := by
  unfold pair
  calc
    _ = ∫ p : ℝ × ℝ, c * (K p.1 p.2 * f p.2 * g p.1)
        ∂((physicalMeasure R).prod (physicalMeasure R)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by dsimp only [Pi.smul_apply, smul_eq_mul]; ring)
    _ = _ := integral_const_mul c _

lemma pair_sub_first {R : ℝ} (K : ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2)) {f g h : ℝ → ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) (hg : MemLp g 2 (physicalMeasure R))
    (hh : MemLp h 2 (physicalMeasure R)) :
    pair R K (f - g) h = pair R K f h - pair R K g h := by
  unfold pair
  calc
    _ = ∫ p : ℝ × ℝ, (K p.1 p.2 * f p.2 * h p.1 - K p.1 p.2 * g p.2 * h p.1)
        ∂((physicalMeasure R).prod (physicalMeasure R)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by dsimp only [Pi.sub_apply]; ring)
    _ = _ := integral_sub (RhSupportLocalization.kernel_joint_integrable K hK hf hh)
      (RhSupportLocalization.kernel_joint_integrable K hK hg hh)

lemma pair_sub_second {R : ℝ} (K : ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2)) {f g h : ℝ → ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) (hg : MemLp g 2 (physicalMeasure R))
    (hh : MemLp h 2 (physicalMeasure R)) :
    pair R K f (g - h) = pair R K f g - pair R K f h := by
  unfold pair
  calc
    _ = ∫ p : ℝ × ℝ, (K p.1 p.2 * f p.2 * g p.1 - K p.1 p.2 * f p.2 * h p.1)
        ∂((physicalMeasure R).prod (physicalMeasure R)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by dsimp only [Pi.sub_apply]; ring)
    _ = _ := integral_sub (RhSupportLocalization.kernel_joint_integrable K hK hf hg)
      (RhSupportLocalization.kernel_joint_integrable K hK hf hh)

lemma energy_smul {R : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) (c : ℝ) :
    energy R (c • v) = c ^ 2 * energy R v := by
  unfold energy
  rw [← pair_self energyKernel kernel_continuous (hv.const_smul c),
    pair_smul_first, pair_smul_second, pair_self energyKernel kernel_continuous hv]
  ring

lemma energy_parallelogram {R : ℝ} {f g : ℝ → ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) (hg : MemLp g 2 (physicalMeasure R)) :
    energy R (f + g) + energy R (f - g) = 2 * energy R f + 2 * energy R g := by
  unfold energy
  rw [← pair_self energyKernel kernel_continuous (hf.add hg),
    ← pair_self energyKernel kernel_continuous (hf.sub hg),
    pair_add_first _ kernel_continuous hf hg (hf.add hg),
    pair_add_second _ kernel_continuous hf hf hg,
    pair_add_second _ kernel_continuous hg hf hg,
    pair_sub_first _ kernel_continuous hf hg (hf.sub hg),
    pair_sub_second _ kernel_continuous hf hf hg,
    pair_sub_second _ kernel_continuous hg hf hg,
    pair_self energyKernel kernel_continuous hf,
    pair_self energyKernel kernel_continuous hg]
  ring

lemma energy_difference_le {R : ℝ} (hR : 0 < R) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) (hg : MemLp g 2 (physicalMeasure R)) :
    energy R (f - g) ≤ 2 * energy R f + 2 * energy R g := by
  have he := energy_parallelogram hf hg
  have hp := kernel_quadratic_nonnegative hR (hf.add hg)
  linarith

lemma energy_l2_bound {R : ℝ} (hR : 0 < R) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) :
    energy R v ≤ (2 * R * bound) * (∫ t in interval R, (v t) ^ 2) := by
  have h := kernel_quadratic_norm_bound hv
  rw [Real.norm_eq_abs, abs_of_nonneg (kernel_quadratic_nonnegative hR hv)] at h
  have hL := RhDilationRank.l1_sq_le hR hv
  simp only [Real.norm_eq_abs] at h
  have hm := mul_le_mul_of_nonneg_left hL bound_nonnegative
  exact h.trans (by convert hm using 1 <;> ring)

lemma physical_energy_tendsto_zero {R : ℝ} (hR : 0 < R) (e : ℕ → ℝ → ℝ)
    (he : ∀ n, MemLp (e n) 2 (physicalMeasure R))
    (he0 : Tendsto (fun n => ∫ t in interval R, (e n t) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => energy R (e n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => kernel_quadratic_nonnegative hR (he n)))
  · exact Eventually.of_forall (fun n => energy_l2_bound hR (he n))
  · simpa only [mul_zero] using he0.const_mul (2 * R * bound)

lemma primitive_difference {R : ℝ} {f g : ℝ → ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) (hg : MemLp g 2 (physicalMeasure R)) (c : ℝ) :
    primitive R (f - c • g) = primitive R f - c • primitive R g := by
  have he : f - c • g = f + (-c) • g := by
    funext t
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, primitive_add hf (hg.const_smul (-c)), primitive_smul]
  funext t
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma primitive_mass_difference_le {R : ℝ} {f g : ℝ → ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) (hg : MemLp g 2 (physicalMeasure R)) (c : ℝ) :
    primitiveMass R (f - c • g) ≤ 2 * primitiveMass R f + 2 * c ^ 2 * primitiveMass R g := by
  have hwF := RhTail.physical_square_integrable (primitive_memLp hf)
  have hwG := RhTail.physical_square_integrable (primitive_memLp hg)
  have hwD := RhTail.physical_square_integrable (primitive_memLp (hf.sub (hg.const_smul c)))
  have hi := integral_mono hwD ((hwF.const_mul 2).add (hwG.const_mul (2 * c ^ 2)))
    (fun t => by
      rw [primitive_difference hf hg c]
      dsimp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      nlinarith [sq_nonneg (primitive R f t + c * primitive R g t)])
  have hr : (∫ t in interval R,
      2 * (primitive R f t) ^ 2 + (2 * c ^ 2) * (primitive R g t) ^ 2) =
      2 * primitiveMass R f + 2 * c ^ 2 * primitiveMass R g := by
    rw [integral_add (hwF.const_mul 2) (hwG.const_mul (2 * c ^ 2)),
      integral_const_mul, integral_const_mul]
  exact hi.trans_eq hr

lemma physical_primitive_mass_tendsto_zero {R : ℝ} (hR : 0 < R)
    (e : ℕ → ℝ → ℝ) (he : ∀ n, MemLp (e n) 2 (physicalMeasure R))
    (he0 : Tendsto (fun n => ∫ t in interval R, (e n t) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => primitiveMass R (e n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun _ => sq_nonneg _)))
  · exact Eventually.of_forall (fun n => primitive_square_bound hR (he n))
  · simpa only [mul_zero] using he0.const_mul (4 * R ^ 2)

/-- The actual centering source; no unspecified form approximation is an input. -/
def centeredSource (e : ℕ → ℝ → ℝ) (M : ℕ → ℝ)
    (φ : ℕ → ContDiffBump (0 : ℝ)) (n : ℕ) : ℝ → ℝ :=
  e n - M n • (φ n).normed volume

lemma centered_memLp {R : ℝ} (e : ℕ → ℝ → ℝ) (M : ℕ → ℝ)
    (φ : ℕ → ContDiffBump (0 : ℝ))
    (he : ∀ n, MemLp (e n) 2 (physicalMeasure R)) (n : ℕ) :
    MemLp (centeredSource e M φ n) 2 (physicalMeasure R) :=
  (he n).sub ((normalized_bump_memLp (φ n) R).const_smul (M n))

/-- Complete positive energy of the actual source correction tends to zero. -/
theorem centered_energy_tendsto_zero {R : ℝ} (hR : 0 < R)
    (e : ℕ → ℝ → ℝ) (M : ℕ → ℝ) (φ : ℕ → ContDiffBump (0 : ℝ))
    (he : ∀ n, MemLp (e n) 2 (physicalMeasure R))
    (he0 : Tendsto (fun n => ∫ t in interval R, (e n t) ^ 2) atTop (𝓝 0))
    {m : ℝ} (hM : Tendsto M atTop (𝓝 m))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => energy R (centeredSource e M φ n)) atTop (𝓝 0) := by
  have heE := physical_energy_tendsto_zero hR e he he0
  have hbE := normalized_bump_quadratic_tendsto_zero φ hφ R
  have hlim : Tendsto (fun n => 2 * energy R (e n) +
      2 * (M n) ^ 2 * energy R ((φ n).normed volume)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, energy, mul_assoc] using
      (heE.const_mul 2).add (((hM.pow 2).mul hbE).const_mul 2)
  apply squeeze_zero' (g := fun n => 2 * energy R (e n) +
    2 * (M n) ^ 2 * energy R ((φ n).normed volume))
    (Eventually.of_forall (fun n =>
      kernel_quadratic_nonnegative hR (centered_memLp e M φ he n)))
  · exact Eventually.of_forall (fun n => by
      have h := energy_difference_le hR (he n)
        ((normalized_bump_memLp (φ n) R).const_smul (M n))
      rw [energy_smul (normalized_bump_memLp (φ n) R)] at h
      simpa only [centeredSource, mul_assoc] using h)
  · exact hlim

/-- The same actual correction also converges in primitive L2 mass. -/
theorem centered_primitive_mass_tendsto_zero {R : ℝ} (hR : 0 < R)
    (e : ℕ → ℝ → ℝ) (M : ℕ → ℝ) (φ : ℕ → ContDiffBump (0 : ℝ))
    (he : ∀ n, MemLp (e n) 2 (physicalMeasure R))
    (he0 : Tendsto (fun n => ∫ t in interval R, (e n t) ^ 2) atTop (𝓝 0))
    {m : ℝ} (hM : Tendsto M atTop (𝓝 m))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => primitiveMass R (centeredSource e M φ n)) atTop (𝓝 0) := by
  have heN := physical_primitive_mass_tendsto_zero hR e he he0
  have hbN := primitive_bump_square_tendsto_zero φ hφ hR
  have hlim : Tendsto (fun n => 2 * primitiveMass R (e n) +
      2 * (M n) ^ 2 * primitiveMass R ((φ n).normed volume)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, primitiveMass, mul_assoc] using
      (heN.const_mul 2).add (((hM.pow 2).mul hbN).const_mul 2)
  apply squeeze_zero' (g := fun n => 2 * primitiveMass R (e n) +
    2 * (M n) ^ 2 * primitiveMass R ((φ n).normed volume))
    (Eventually.of_forall (fun n => integral_nonneg (fun _ => sq_nonneg _)))
  · exact Eventually.of_forall (fun n =>
      primitive_mass_difference_le (he n) (normalized_bump_memLp (φ n) R) (M n))
  · exact hlim

/-- Actual complete positive graph error, with both energy and mass retained. -/
theorem centered_graph_error_tendsto_zero {R : ℝ} (hR : 0 < R)
    (e : ℕ → ℝ → ℝ) (M : ℕ → ℝ) (φ : ℕ → ContDiffBump (0 : ℝ))
    (he : ∀ n, MemLp (e n) 2 (physicalMeasure R))
    (he0 : Tendsto (fun n => ∫ t in interval R, (e n t) ^ 2) atTop (𝓝 0))
    {m : ℝ} (hM : Tendsto M atTop (𝓝 m))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => energy R (centeredSource e M φ n) +
      primitiveMass R (centeredSource e M φ n)) atTop (𝓝 0) := by
  simpa only [add_zero] using
    (centered_energy_tendsto_zero hR e M φ he he0 hM hφ).add
      (centered_primitive_mass_tendsto_zero hR e M φ he he0 hM hφ)

end RhCenteredPrimitiveApproximation
#print axioms RhCenteredPrimitiveApproximation.energy_parallelogram
#print axioms RhCenteredPrimitiveApproximation.energy_l2_bound
#print axioms RhCenteredPrimitiveApproximation.centered_energy_tendsto_zero
#print axioms RhCenteredPrimitiveApproximation.centered_primitive_mass_tendsto_zero
#print axioms RhCenteredPrimitiveApproximation.centered_graph_error_tendsto_zero
