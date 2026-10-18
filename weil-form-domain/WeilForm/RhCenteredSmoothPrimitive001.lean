import RhActualCoreBump001
import RhCenteredPrimitiveApproximation001

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval
namespace RhCenteredSmoothPrimitive
open RhAnchored RhActualCoreBump RhNativeBumpCapacity

def centeredPhysical (R : ℝ) (hR : 0 < R) (u : ℕ → ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  u n - totalMass R (u n) • (centralBump R hR n).normed volume

lemma centered_memLp {R : ℝ} (hR : 0 < R) (u : ℕ → ℝ → ℝ)
    (hu : ∀ n, MemLp (u n) 2 (physicalMeasure R)) (n : ℕ) :
    MemLp (centeredPhysical R hR u n) 2 (physicalMeasure R) :=
  (hu n).sub ((normalized_bump_memLp (centralBump R hR n) R).const_smul (totalMass R (u n)))

lemma centered_contDiff {R : ℝ} (hR : 0 < R) (u : ℕ → ℝ → ℝ)
    (hu : ∀ n, ContDiff ℝ ∞ (u n)) (n : ℕ) :
    ContDiff ℝ ∞ (centeredPhysical R hR u n) := by
  change ContDiff ℝ ∞ (fun t => u n t - totalMass R (u n) *
    (centralBump R hR n).normed volume t)
  exact (hu n).sub (contDiff_const.mul (centralBump R hR n).contDiff_normed)

lemma centered_compact {R : ℝ} (hR : 0 < R) (u : ℕ → ℝ → ℝ)
    (hu : ∀ n, HasCompactSupport (u n)) (n : ℕ) :
    HasCompactSupport (centeredPhysical R hR u n) := by
  have hm : HasCompactSupport (fun t => totalMass R (u n) *
      (centralBump R hR n).normed volume t) :=
    (centralBump R hR n).hasCompactSupport_normed.mul_left
  exact (hu n).sub hm

lemma centered_tsupport {R : ℝ} (hR : 0 < R) (u : ℕ → ℝ → ℝ)
    (hu : ∀ n, tsupport (u n) ⊆ Ioo (-R) R) (n : ℕ) :
    tsupport (centeredPhysical R hR u n) ⊆ Ioo (-R) R := by
  have hs := tsupport_binop_subset (fun x y : ℝ => x - totalMass R (u n) * y)
    (by ring) (u n) ((centralBump R hR n).normed volume)
  exact hs.trans (union_subset (hu n) (normed_tsupport hR n))

lemma centered_totalMass {R : ℝ} (hR : 0 < R) (u : ℕ → ℝ → ℝ)
    (hu : ∀ n, MemLp (u n) 2 (physicalMeasure R)) (n : ℕ) :
    totalMass R (centeredPhysical R hR u n) = 0 := by
  have hui : IntegrableOn (u n) (interval R) := (hu n).integrable (by norm_num)
  have hbi : IntegrableOn ((centralBump R hR n).normed volume) (interval R) :=
    (normalized_bump_memLp (centralBump R hR n) R).integrable (by norm_num)
  change (∫ t in interval R, u n t - totalMass R (u n) *
    (centralBump R hR n).normed volume t) = 0
  rw [integral_sub hui (hbi.const_mul _), integral_const_mul]
  change totalMass R (u n) - totalMass R (u n) *
    totalMass R ((centralBump R hR n).normed volume) = 0
  rw [normed_totalMass hR n]
  ring

/-- Actual smooth compact primitives of the corrected physical derivatives. -/
theorem exists_centered_smooth_primitives {R : ℝ} (hR : 0 < R)
    (u : ℕ → ℝ → ℝ) (huS : ∀ n, ContDiff ℝ ∞ (u n))
    (huC : ∀ n, HasCompactSupport (u n))
    (huT : ∀ n, tsupport (u n) ⊆ Ioo (-R) R)
    (hu : ∀ n, MemLp (u n) 2 (physicalMeasure R)) :
    ∃ f : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ ∞ (f n)) ∧
      (∀ n, HasCompactSupport (f n)) ∧ (∀ n, tsupport (f n) ⊆ Ioo (-R) R) ∧
      (∀ n, deriv (f n) = centeredPhysical R hR u n) ∧
      (∀ n, f n =ᵐ[volume] zeroExtension R (primitive R (centeredPhysical R hR u n))) := by
  have hex (n : ℕ) := RhSmoothPrimitiveMass.exists_smooth_compact_primitive hR
    (centered_contDiff hR u huS n) (centered_compact hR u huC n)
    (centered_tsupport hR u huT n) (centered_totalMass hR u hu n)
  choose f hfS hfC hfT hfD hfA using hex
  exact ⟨f, hfS, hfC, hfT, hfD, hfA⟩

end RhCenteredSmoothPrimitive
#print axioms RhCenteredSmoothPrimitive.centered_totalMass
#print axioms RhCenteredSmoothPrimitive.exists_centered_smooth_primitives
