/-
Local, uncompiled API-port candidate; not a submitted Mathlib contribution.
Adapted from the preserved EntireDerivativeSeries proof. See ../ATTRIBUTION.md
for dependency attribution and the unresolved contribution-header decision.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.Basic

noncomputable section
public section

set_option autoImplicit false

open Set Filter
open scoped Topology BigOperators

private def egfRow (c : ℕ → ℂ) (k : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => c (n + k) / (Nat.factorial n : ℂ))

private theorem egfStep {f : ℂ → ℂ} {c : ℕ → ℂ} {k : ℕ} {r : ENNReal}
    (hp : HasFPowerSeriesOnBall f (egfRow c k) 0 r) :
    HasFPowerSeriesOnBall (deriv f) (egfRow c (k + 1)) 0 r := by
  let p := egfRow c k
  let D := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries p.derivSeries
  have hd := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall hp.fderiv
  change HasFPowerSeriesOnBall (deriv f) D 0 r at hd
  have hDc (n : ℕ) : D.coeff n = (n + 1 : ℂ) * p.coeff (n + 1) := by
    change p.derivSeries.coeff n 1 = (n + 1 : ℂ) * p.coeff (n + 1)
    simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using p.derivSeries_coeff_one n
  have he : D = egfRow c (k + 1) := by
    apply FormalMultilinearSeries.ext
    intro n
    rw [← FormalMultilinearSeries.mkPiRing_coeff_eq D n,
      ← FormalMultilinearSeries.mkPiRing_coeff_eq (egfRow c (k + 1)) n]
    congr 1
    rw [hDc]
    simp only [p, egfRow, FormalMultilinearSeries.coeff_ofScalars]
    rw [show n + 1 + k = n + (k + 1) by omega, Nat.factorial_succ]
    push_cast
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    have hf : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp [hn, hf] <;> ring
  exact he ▸ hd

/-- Finite derivatives of a scalar exponential-generating series shift its
coefficients and preserve its ball of representation. -/
theorem HasFPowerSeriesOnBall.iteratedDeriv_ofScalars
    {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ENNReal}
    (h : HasFPowerSeriesOnBall f
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => c n / (Nat.factorial n : ℂ))) 0 r)
    (k : ℕ) :
    HasFPowerSeriesOnBall (iteratedDeriv k f)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => c (n + k) / (Nat.factorial n : ℂ))) 0 r := by
  have hp : HasFPowerSeriesOnBall f (egfRow c 0) 0 r := by
    simpa only [egfRow, Nat.add_zero] using h
  have hk : HasFPowerSeriesOnBall (iteratedDeriv k f) (egfRow c k) 0 r := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hp
    | succ k ih => simpa only [iteratedDeriv_succ] using egfStep ih
  simpa only [egfRow] using hk

#print axioms HasFPowerSeriesOnBall.iteratedDeriv_ofScalars
