import ThetaSeries

/-!
Actual Gaussian seed series and its first two derivatives. The imported
polynomial majorants supply every convergence hypothesis. The shell identity
uses the full-integer theta multiplicity, including its zero Gaussian.
-/
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace ThetaMacdonald.Symmetry

def gaussianSeed (k : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u/2 - zArg k u)
def gaussianSeedD1 (k : ℕ) (u : ℝ) : ℝ :=
  ((1/2 : ℝ) - 2 * zArg k u) * gaussianSeed k u
def gaussianSeedD2 (k : ℕ) (u : ℝ) : ℝ :=
  ((1/4 : ℝ) - 6 * zArg k u + 4 * zArg k u ^ 2) * gaussianSeed k u

def seedCoefficient : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 1, 0 => 1/2
  | 1, 1 => -2
  | 2, 0 => 1/4
  | 2, 1 => -6
  | 2, 2 => 4
  | _, _ => 0
def seedRow (r k : ℕ) (u : ℝ) : ℝ :=
  Series.polynomialShell (Finset.range 3) (seedCoefficient r) k u
def seedMajorant (r : ℕ) (L U : ℝ) (k : ℕ) : ℝ :=
  Series.polynomialMajorant (Finset.range 3) (seedCoefficient r) L U k

theorem seedRow_zero (k : ℕ) (u : ℝ) :
    seedRow 0 k u = gaussianSeed k u := by
  simp [seedRow, Series.polynomialShell, Finset.sum_range_succ,
    seedCoefficient, Series.gaussianMonomial, gaussianSeed]
theorem seedRow_one (k : ℕ) (u : ℝ) :
    seedRow 1 k u = gaussianSeedD1 k u := by
  simp [seedRow, Series.polynomialShell, Finset.sum_range_succ,
    seedCoefficient, Series.gaussianMonomial, gaussianSeedD1, gaussianSeed]
  ring
theorem seedRow_two (k : ℕ) (u : ℝ) :
    seedRow 2 k u = gaussianSeedD2 k u := by
  simp [seedRow, Series.polynomialShell, Finset.sum_range_succ,
    seedCoefficient, Series.gaussianMonomial, gaussianSeedD2, gaussianSeed]
  ring

theorem summable_seedMajorant (r : ℕ) (L U : ℝ) :
    Summable (seedMajorant r L U) :=
  Series.summable_polynomialMajorant _ _ _ _
theorem norm_seedRow_le (r k : ℕ) {L U u : ℝ} (hu : u ∈ Icc L U) :
    ‖seedRow r k u‖ ≤ seedMajorant r L U k :=
  Series.norm_polynomialShell_le _ _ _ hu
theorem summable_seedRow (r : ℕ) (u : ℝ) :
    Summable (fun k => seedRow r k u) :=
  (summable_seedMajorant r u u).of_norm_bounded
    (fun k => norm_seedRow_le r k ⟨le_rfl, le_rfl⟩)
theorem summable_gaussianSeed (u : ℝ) :
    Summable (fun k => gaussianSeed k u) := by
  simpa only [seedRow_zero] using summable_seedRow 0 u
theorem summable_gaussianSeedD1 (u : ℝ) :
    Summable (fun k => gaussianSeedD1 k u) := by
  simpa only [seedRow_one] using summable_seedRow 1 u
theorem summable_gaussianSeedD2 (u : ℝ) :
    Summable (fun k => gaussianSeedD2 k u) := by
  simpa only [seedRow_two] using summable_seedRow 2 u

theorem hasDerivAt_gaussianSeed (k : ℕ) (u : ℝ) :
    HasDerivAt (gaussianSeed k) (gaussianSeedD1 k u) u := by
  convert ((hasDerivAt_id u).div_const 2 |>.sub (hasDerivAt_zArg k u)).exp using 1
  · rfl
  · dsimp [gaussianSeedD1, gaussianSeed]
    ring
theorem hasDerivAt_gaussianSeedD1 (k : ℕ) (u : ℝ) :
    HasDerivAt (gaussianSeedD1 k) (gaussianSeedD2 k u) u := by
  have hp := ((hasDerivAt_zArg k u).const_mul 2).const_sub (1/2 : ℝ)
  convert hp.mul (hasDerivAt_gaussianSeed k u) using 1
  · rfl
  · dsimp [gaussianSeedD1, gaussianSeedD2]
    ring

theorem hasDerivAt_tsum_gaussianSeed (u : ℝ) :
    HasDerivAt (fun v => ∑' k, gaussianSeed k v)
      (∑' k, gaussianSeedD1 k u) u := by
  have hu : u ∈ Ioo (u-1) (u+1) := by constructor <;> linarith
  apply hasDerivAt_tsum_of_isPreconnected
    (summable_seedMajorant 1 (u-1) (u+1)) isOpen_Ioo isPreconnected_Ioo
    (fun k v _ => hasDerivAt_gaussianSeed k v)
    (fun k v hv => ?_) hu (summable_gaussianSeed u) hu
  simpa only [seedRow_one] using
    norm_seedRow_le 1 k (show v ∈ Icc (u-1) (u+1) from ⟨hv.1.le, hv.2.le⟩)

theorem hasDerivAt_tsum_gaussianSeedD1 (u : ℝ) :
    HasDerivAt (fun v => ∑' k, gaussianSeedD1 k v)
      (∑' k, gaussianSeedD2 k u) u := by
  have hu : u ∈ Ioo (u-1) (u+1) := by constructor <;> linarith
  apply hasDerivAt_tsum_of_isPreconnected
    (summable_seedMajorant 2 (u-1) (u+1)) isOpen_Ioo isPreconnected_Ioo
    (fun k v _ => hasDerivAt_gaussianSeedD1 k v)
    (fun k v hv => ?_) hu (summable_gaussianSeedD1 u) hu
  simpa only [seedRow_two] using
    norm_seedRow_le 2 k (show v ∈ Icc (u-1) (u+1) from ⟨hv.1.le, hv.2.le⟩)

def gaussianSum (u : ℝ) : ℝ := ∑' k : ℕ, gaussianSeed k u
def centeredTheta (u : ℝ) : ℝ := 2 * gaussianSum u - Real.exp (u/2)
def centeredThetaD1 (u : ℝ) : ℝ :=
  2 * (∑' k : ℕ, gaussianSeedD1 k u) - (1/2 : ℝ) * Real.exp (u/2)
def centeredThetaD2 (u : ℝ) : ℝ :=
  2 * (∑' k : ℕ, gaussianSeedD2 k u) - (1/4 : ℝ) * Real.exp (u/2)

theorem hasDerivAt_centeredTheta (u : ℝ) :
    HasDerivAt centeredTheta (centeredThetaD1 u) u := by
  convert ((hasDerivAt_tsum_gaussianSeed u).const_mul 2).sub
    ((hasDerivAt_id u).div_const 2).exp using 1
  · rfl
  · dsimp [centeredThetaD1]
    ring
theorem hasDerivAt_centeredThetaD1 (u : ℝ) :
    HasDerivAt centeredThetaD1 (centeredThetaD2 u) u := by
  convert ((hasDerivAt_tsum_gaussianSeedD1 u).const_mul 2).sub
    (((hasDerivAt_id u).div_const 2).exp.const_mul (1/2 : ℝ)) using 1
  · rfl
  · dsimp [centeredThetaD2]
    ring
theorem deriv_centeredTheta :
    deriv centeredTheta = centeredThetaD1 :=
  funext fun u => (hasDerivAt_centeredTheta u).deriv
theorem second_deriv_centeredTheta (u : ℝ) :
    deriv (deriv centeredTheta) u = centeredThetaD2 u := by
  rw [deriv_centeredTheta]
  exact (hasDerivAt_centeredThetaD1 u).deriv

theorem rawShell_eq_seed_derivatives (k : ℕ) (u : ℝ) :
    rawShell k u = 2 * gaussianSeedD2 k u - (1/2 : ℝ) * gaussianSeed k u := by
  dsimp [rawShell, gaussianSeedD2, gaussianSeed]
  ring
theorem raw_sum_eq_centeredTheta (u : ℝ) :
    (∑' k : ℕ, rawShell k u) =
      deriv (deriv centeredTheta) u - centeredTheta u / 4 := by
  have h := ((summable_gaussianSeedD2 u).hasSum.mul_left 2).sub
    ((summable_gaussianSeed u).hasSum.mul_left (1/2 : ℝ))
  have ht : (∑' k : ℕ, rawShell k u) =
      2 * (∑' k : ℕ, gaussianSeedD2 k u) -
        (1/2 : ℝ) * (∑' k : ℕ, gaussianSeed k u) := by
    simpa only [← rawShell_eq_seed_derivatives] using h.tsum_eq
  rw [ht, second_deriv_centeredTheta]
  dsimp [centeredThetaD2, centeredTheta, gaussianSum]
  ring

end ThetaMacdonald.Symmetry

#print axioms ThetaMacdonald.Symmetry.summable_gaussianSeed
#print axioms ThetaMacdonald.Symmetry.summable_gaussianSeedD1
#print axioms ThetaMacdonald.Symmetry.summable_gaussianSeedD2
#print axioms ThetaMacdonald.Symmetry.hasDerivAt_tsum_gaussianSeed
#print axioms ThetaMacdonald.Symmetry.hasDerivAt_tsum_gaussianSeedD1
#print axioms ThetaMacdonald.Symmetry.second_deriv_centeredTheta
#print axioms ThetaMacdonald.Symmetry.raw_sum_eq_centeredTheta
