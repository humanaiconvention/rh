import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Ring

/-!
Actual theta shells in polynomial-exponential coordinates. No normalization,
evenness, convergence or cumulative inequality is assumed here.
-/
noncomputable section
namespace ThetaMacdonald

def zArg (k : ℕ) (u : ℝ) : ℝ := Real.pi * (k : ℝ)^2 * Real.exp (2*u)

def rawShell (k : ℕ) (u : ℝ) : ℝ :=
  (8 * zArg k u ^ 2 - 12 * zArg k u) * Real.exp (u/2 - zArg k u)

def rawShellD1 (k : ℕ) (u : ℝ) : ℝ :=
  (-16 * zArg k u ^ 3 + 60 * zArg k u ^ 2 - 30 * zArg k u) *
    Real.exp (u/2 - zArg k u)

def rawShellD2 (k : ℕ) (u : ℝ) : ℝ :=
  (32 * zArg k u ^ 4 - 224 * zArg k u ^ 3 + 330 * zArg k u ^ 2 -
    75 * zArg k u) * Real.exp (u/2 - zArg k u)

theorem hasDerivAt_zArg (k : ℕ) (u : ℝ) :
    HasDerivAt (zArg k) (2 * zArg k u) u := by
  have hu : HasDerivAt (fun x : ℝ => 2*x) 2 u := by
    convert (hasDerivAt_id u).const_mul 2 using 1 <;> simp
  convert hu.exp.const_mul (Real.pi * (k : ℝ)^2) using 1
  · rfl
  · dsimp [zArg]
    ring

theorem hasDerivAt_rawShell (k : ℕ) (u : ℝ) :
    HasDerivAt (rawShell k) (rawShellD1 k u) u := by
  have hz := hasDerivAt_zArg k u
  have hp := (hz.pow 2).const_mul 8 |>.sub (hz.const_mul 12)
  have he := ((hasDerivAt_id u).div_const 2 |>.sub hz).exp
  convert hp.mul he using 1
  · rfl
  · dsimp [rawShellD1]
    ring

theorem hasDerivAt_rawShellD1 (k : ℕ) (u : ℝ) :
    HasDerivAt (rawShellD1 k) (rawShellD2 k u) u := by
  have hz := hasDerivAt_zArg k u
  have hp := (((hz.pow 3).const_mul (-16)).add ((hz.pow 2).const_mul 60)).sub
    (hz.const_mul 30)
  have he := ((hasDerivAt_id u).div_const 2 |>.sub hz).exp
  convert hp.mul he using 1
  · rfl
  · dsimp [rawShellD2]
    ring

theorem deriv_rawShell (k : ℕ) :
    deriv (rawShell k) = rawShellD1 k :=
  funext fun u => (hasDerivAt_rawShell k u).deriv

theorem deriv_rawShellD1 (k : ℕ) :
    deriv (rawShellD1 k) = rawShellD2 k :=
  funext fun u => (hasDerivAt_rawShellD1 k u).deriv

theorem rawShell_eq_expanded (k : ℕ) (u : ℝ) :
    rawShell k u =
      (8 * Real.pi^2 * (k : ℝ)^4 * Real.exp (9*u/2) -
        12 * Real.pi * (k : ℝ)^2 * Real.exp (5*u/2)) *
        Real.exp (-Real.pi * (k : ℝ)^2 * Real.exp (2*u)) := by
  have hsplit : Real.exp (u/2-zArg k u) =
      Real.exp (u/2) * Real.exp (-zArg k u) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have hfour : Real.exp (2*u)^2 * Real.exp (u/2) = Real.exp (9*u/2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have htwo : Real.exp (2*u) * Real.exp (u/2) = Real.exp (5*u/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [rawShell, hsplit]
  dsimp [zArg]
  calc
    _ = (8 * Real.pi^2 * (k : ℝ)^4 * (Real.exp (2*u)^2 * Real.exp (u/2)) -
        12 * Real.pi * (k : ℝ)^2 * (Real.exp (2*u) * Real.exp (u/2))) *
        Real.exp (-(Real.pi * (k : ℝ)^2 * Real.exp (2*u))) := by ring
    _ = _ := by rw [hfour, htwo]; congr 2 <;> ring

end ThetaMacdonald

#print axioms ThetaMacdonald.hasDerivAt_rawShell
#print axioms ThetaMacdonald.hasDerivAt_rawShellD1
#print axioms ThetaMacdonald.rawShell_eq_expanded
