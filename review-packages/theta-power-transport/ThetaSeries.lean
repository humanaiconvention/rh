import ThetaShellDerivative
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic

/-!
Compact-local summability for the actual theta shells and their first two
explicit derivative rows. Gaussian summability is imported from the existing
Jacobi-theta bounds; no zero-location or desired series estimate is assumed.

The integer index `k = 0` contributes zero to all three actual shell rows.
The accompanying shifted-index theorem therefore uses the source's `k=n+1`.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace ThetaMacdonald.Series

/-- A polynomial monomial in the actual Gaussian phase, not a generic assumed
majorant for the desired sum. -/
def gaussianMonomial (j k : ℕ) (u : ℝ) : ℝ :=
  zArg k u ^ j * Real.exp (u / 2 - zArg k u)

/-- One explicit summable bound on a whole compact interval. -/
def gaussianMajorant (j : ℕ) (L U : ℝ) (k : ℕ) : ℝ :=
  (Real.pi * Real.exp (2 * U)) ^ j * Real.exp (U / 2) *
    HurwitzKernelBounds.f_nat (2 * j) 0 (Real.exp (2 * L)) k

theorem zArg_nonneg (k : ℕ) (u : ℝ) : 0 ≤ zArg k u := by
  unfold zArg
  positivity

theorem zArg_mono (k : ℕ) {u v : ℝ} (h : u ≤ v) :
    zArg k u ≤ zArg k v := by
  unfold zArg
  apply mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith : 2 * u ≤ 2 * v))
  positivity

theorem summable_gaussianMajorant (j : ℕ) (L U : ℝ) :
    Summable (gaussianMajorant j L U) := by
  exact (HurwitzKernelBounds.summable_f_nat (2 * j) 0
    (Real.exp_pos (2 * L))).mul_left
      ((Real.pi * Real.exp (2 * U)) ^ j * Real.exp (U / 2))

theorem norm_gaussianMonomial_le (j k : ℕ) {L U u : ℝ}
    (hu : u ∈ Icc L U) :
    ‖gaussianMonomial j k u‖ ≤ gaussianMajorant j L U k := by
  have hpow : zArg k u ^ j ≤ zArg k U ^ j :=
    pow_le_pow_left₀ (zArg_nonneg k u) (zArg_mono k hu.2) j
  have hexp : Real.exp (u / 2 - zArg k u) ≤
      Real.exp (U / 2 - zArg k L) := by
    apply Real.exp_le_exp.mpr
    exact sub_le_sub (by linarith [hu.2]) (zArg_mono k hu.1)
  have hphase : zArg k U ^ j =
      (Real.pi * Real.exp (2 * U)) ^ j * (k : ℝ) ^ (2 * j) := by
    rw [show zArg k U = (Real.pi * Real.exp (2 * U)) * (k : ℝ) ^ 2 by
      unfold zArg
      ring, mul_pow, ← pow_mul]
  calc
    ‖gaussianMonomial j k u‖ =
        zArg k u ^ j * Real.exp (u / 2 - zArg k u) :=
      Real.norm_of_nonneg (mul_nonneg (pow_nonneg (zArg_nonneg k u) j)
        (Real.exp_pos _).le)
    _ ≤ zArg k U ^ j * Real.exp (U / 2 - zArg k L) :=
      mul_le_mul hpow hexp (Real.exp_pos _).le
        (pow_nonneg (zArg_nonneg k U) j)
    _ = gaussianMajorant j L U k := by
      rw [hphase, sub_eq_add_neg, Real.exp_add]
      simp only [gaussianMajorant, HurwitzKernelBounds.f_nat, add_zero,
        zArg, neg_mul]
      ring

/-- Any fixed finite phase polynomial inherits one explicit common majorant. -/
def polynomialShell (s : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ s, c j * gaussianMonomial j k u

def polynomialMajorant (s : Finset ℕ) (c : ℕ → ℝ)
    (L U : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ s, |c j| * gaussianMajorant j L U k

theorem summable_polynomialMajorant (s : Finset ℕ) (c : ℕ → ℝ) (L U : ℝ) :
    Summable (polynomialMajorant s c L U) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change Summable (fun k : ℕ =>
      ∑ j ∈ (∅ : Finset ℕ), |c j| * gaussianMajorant j L U k)
    simpa only [Finset.sum_empty] using
      (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  | @insert j s hj ih =>
    have heq : polynomialMajorant (insert j s) c L U =
        fun k => |c j| * gaussianMajorant j L U k +
          polynomialMajorant s c L U k := by
      funext k
      simp only [polynomialMajorant, Finset.sum_insert hj]
    rw [heq]
    exact ((summable_gaussianMajorant j L U).mul_left |c j|).add ih

theorem norm_polynomialShell_le (s : Finset ℕ) (c : ℕ → ℝ) (k : ℕ)
    {L U u : ℝ} (hu : u ∈ Icc L U) :
    ‖polynomialShell s c k u‖ ≤ polynomialMajorant s c L U k := by
  unfold polynomialShell polynomialMajorant
  apply (norm_sum_le s _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_gaussianMonomial_le j k hu)
    (abs_nonneg (c j))

/-- Rows 0,1,2 are the actual shell and its two explicitly calculated
derivative rows. Other row indices are zero and carry no derivative claim. -/
def shellCoefficient : ℕ → ℕ → ℝ
  | 0, 1 => -12
  | 0, 2 => 8
  | 1, 1 => -30
  | 1, 2 => 60
  | 1, 3 => -16
  | 2, 1 => -75
  | 2, 2 => 330
  | 2, 3 => -224
  | 2, 4 => 32
  | _, _ => 0

def shellRow (r k : ℕ) (u : ℝ) : ℝ :=
  polynomialShell (Finset.range 5) (shellCoefficient r) k u

def rowMajorant (r : ℕ) (L U : ℝ) (k : ℕ) : ℝ :=
  polynomialMajorant (Finset.range 5) (shellCoefficient r) L U k

theorem shellRow_zero (k : ℕ) (u : ℝ) :
    shellRow 0 k u = rawShell k u := by
  simp [shellRow, polynomialShell, Finset.sum_range_succ, shellCoefficient,
    gaussianMonomial, rawShell]
  <;> ring

theorem shellRow_one (k : ℕ) (u : ℝ) :
    shellRow 1 k u = rawShellD1 k u := by
  simp [shellRow, polynomialShell, Finset.sum_range_succ, shellCoefficient,
    gaussianMonomial, rawShellD1]
  <;> ring

theorem shellRow_two (k : ℕ) (u : ℝ) :
    shellRow 2 k u = rawShellD2 k u := by
  simp [shellRow, polynomialShell, Finset.sum_range_succ, shellCoefficient,
    gaussianMonomial, rawShellD2]
  <;> ring

theorem summable_rowMajorant (r : ℕ) (L U : ℝ) :
    Summable (rowMajorant r L U) :=
  summable_polynomialMajorant _ _ _ _

theorem norm_shellRow_le (r k : ℕ) {L U u : ℝ} (hu : u ∈ Icc L U) :
    ‖shellRow r k u‖ ≤ rowMajorant r L U k :=
  norm_polynomialShell_le _ _ _ hu

theorem summable_shellRow (r : ℕ) (u : ℝ) :
    Summable (fun k => shellRow r k u) :=
  (summable_rowMajorant r u u).of_norm_bounded
    (fun k => norm_shellRow_le r k ⟨le_rfl, le_rfl⟩)

theorem uniformlyOn_shellRow (r : ℕ) (L U : ℝ) :
    TendstoUniformlyOn
      (fun N u => ∑ k ∈ Finset.range N, shellRow r k u)
      (fun u => ∑' k, shellRow r k u) atTop (Icc L U) :=
  tendstoUniformlyOn_tsum_nat (summable_rowMajorant r L U)
    (fun k u hu => norm_shellRow_le r k hu)

theorem summable_rawShell (u : ℝ) :
    Summable (fun k => rawShell k u) := by
  simpa only [shellRow_zero] using summable_shellRow 0 u

theorem summable_rawShellD1 (u : ℝ) :
    Summable (fun k => rawShellD1 k u) := by
  simpa only [shellRow_one] using summable_shellRow 1 u

theorem summable_rawShellD2 (u : ℝ) :
    Summable (fun k => rawShellD2 k u) := by
  simpa only [shellRow_two] using summable_shellRow 2 u

theorem summable_norm_rawShell (u : ℝ) :
    Summable (fun k => ‖rawShell k u‖) :=
  (summable_rawShell u).norm

theorem summable_norm_rawShellD1 (u : ℝ) :
    Summable (fun k => ‖rawShellD1 k u‖) :=
  (summable_rawShellD1 u).norm

theorem summable_norm_rawShellD2 (u : ℝ) :
    Summable (fun k => ‖rawShellD2 k u‖) :=
  (summable_rawShellD2 u).norm

theorem uniformlyOn_rawShell (L U : ℝ) :
    TendstoUniformlyOn
      (fun N u => ∑ k ∈ Finset.range N, rawShell k u)
      (fun u => ∑' k, rawShell k u) atTop (Icc L U) := by
  simpa only [shellRow_zero] using uniformlyOn_shellRow 0 L U

theorem uniformlyOn_rawShellD1 (L U : ℝ) :
    TendstoUniformlyOn
      (fun N u => ∑ k ∈ Finset.range N, rawShellD1 k u)
      (fun u => ∑' k, rawShellD1 k u) atTop (Icc L U) := by
  simpa only [shellRow_one] using uniformlyOn_shellRow 1 L U

theorem uniformlyOn_rawShellD2 (L U : ℝ) :
    TendstoUniformlyOn
      (fun N u => ∑ k ∈ Finset.range N, rawShellD2 k u)
      (fun u => ∑' k, rawShellD2 k u) atTop (Icc L U) := by
  simpa only [shellRow_two] using uniformlyOn_shellRow 2 L U

/-- Actual termwise differentiation, justified by an explicit summable bound
on a neighborhood, not by a formal derivative-of-tsum rewrite. -/
theorem hasDerivAt_tsum_rawShell_Ioo {L U u : ℝ} (hu : u ∈ Ioo L U) :
    HasDerivAt (fun v => ∑' k, rawShell k v)
      (∑' k, rawShellD1 k u) u := by
  apply hasDerivAt_tsum_of_isPreconnected
    (summable_rowMajorant 1 L U) isOpen_Ioo isPreconnected_Ioo
    (fun k v _ => hasDerivAt_rawShell k v)
    (fun k v hv => ?_) hu (summable_rawShell u) hu
  simpa only [shellRow_one] using
    norm_shellRow_le 1 k (show v ∈ Icc L U from ⟨hv.1.le, hv.2.le⟩)

theorem hasDerivAt_tsum_rawShellD1_Ioo {L U u : ℝ} (hu : u ∈ Ioo L U) :
    HasDerivAt (fun v => ∑' k, rawShellD1 k v)
      (∑' k, rawShellD2 k u) u := by
  apply hasDerivAt_tsum_of_isPreconnected
    (summable_rowMajorant 2 L U) isOpen_Ioo isPreconnected_Ioo
    (fun k v _ => hasDerivAt_rawShellD1 k v)
    (fun k v hv => ?_) hu (summable_rawShellD1 u) hu
  simpa only [shellRow_two] using
    norm_shellRow_le 2 k (show v ∈ Icc L U from ⟨hv.1.le, hv.2.le⟩)

theorem hasDerivAt_tsum_rawShell (u : ℝ) :
    HasDerivAt (fun v => ∑' k, rawShell k v)
      (∑' k, rawShellD1 k u) u :=
  hasDerivAt_tsum_rawShell_Ioo (L := u - 1) (U := u + 1)
    (by constructor <;> linarith)

theorem hasDerivAt_tsum_rawShellD1 (u : ℝ) :
    HasDerivAt (fun v => ∑' k, rawShellD1 k v)
      (∑' k, rawShellD2 k u) u :=
  hasDerivAt_tsum_rawShellD1_Ioo (L := u - 1) (U := u + 1)
    (by constructor <;> linarith)

theorem deriv_tsum_rawShell :
    deriv (fun v => ∑' k, rawShell k v) = fun v => ∑' k, rawShellD1 k v :=
  funext fun u => (hasDerivAt_tsum_rawShell u).deriv

theorem second_deriv_tsum_rawShell (u : ℝ) :
    deriv (deriv (fun v => ∑' k, rawShell k v)) u =
      ∑' k, rawShellD2 k u := by
  rw [deriv_tsum_rawShell]
  exact (hasDerivAt_tsum_rawShellD1 u).deriv

theorem summable_rawShell_shifted (u : ℝ) :
    Summable (fun n : ℕ => rawShell (n + 1) u) := by
  simpa only [Function.comp_def, Nat.succ_eq_add_one] using
    (summable_rawShell u).comp_injective Nat.succ_injective

theorem source_phi_summable (u : ℝ) :
    Summable (fun n : ℕ =>
      (8 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (9 * u / 2) -
        12 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) := by
  simpa only [rawShell_eq_expanded] using summable_rawShell_shifted u

theorem rawShell_zero (u : ℝ) : rawShell 0 u = 0 := by
  simp [rawShell, zArg]

theorem tsum_rawShell_eq_shifted (u : ℝ) :
    (∑' k : ℕ, rawShell k u) = ∑' n : ℕ, rawShell (n + 1) u := by
  simpa only [rawShell_zero, zero_add] using
    (summable_rawShell u).tsum_eq_zero_add

end ThetaMacdonald.Series

#print axioms ThetaMacdonald.Series.summable_gaussianMajorant
#print axioms ThetaMacdonald.Series.norm_gaussianMonomial_le
#print axioms ThetaMacdonald.Series.norm_polynomialShell_le
#print axioms ThetaMacdonald.Series.uniformlyOn_rawShell
#print axioms ThetaMacdonald.Series.uniformlyOn_rawShellD1
#print axioms ThetaMacdonald.Series.uniformlyOn_rawShellD2
#print axioms ThetaMacdonald.Series.hasDerivAt_tsum_rawShell
#print axioms ThetaMacdonald.Series.hasDerivAt_tsum_rawShellD1
#print axioms ThetaMacdonald.Series.second_deriv_tsum_rawShell
#print axioms ThetaMacdonald.Series.summable_rawShell_shifted
#print axioms ThetaMacdonald.Series.source_phi_summable
#print axioms ThetaMacdonald.Series.tsum_rawShell_eq_shifted
