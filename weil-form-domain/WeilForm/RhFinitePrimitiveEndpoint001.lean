import RhFinitePrimitiveIntegrability001

/-! Specialization to the actual first-prime endpoint; this is an identity, not positivity. -/
noncomputable section
open MeasureTheory Set
open scoped Topology Interval BigOperators
namespace RhAnchored

def schurEndpoint : ℝ := Real.log 3 / 2

lemma schurEndpoint_geometry : 0 < schurEndpoint ∧ schurEndpoint < firstPrimeLog := by
  have h3 := Real.log_pos (by norm_num : 1 < (3 : ℝ))
  have h34 := Real.log_lt_log (by norm_num : 0 < (3 : ℝ))
    (by norm_num : (3 : ℝ) < (2 : ℝ)^2)
  rw [Real.log_pow] at h34
  norm_num only [Nat.cast_ofNat] at h34
  unfold schurEndpoint firstPrimeLog
  constructor <;> linarith

theorem first_prime_endpoint_finite_identity {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure schurEndpoint)) (J : ℕ) :
    (∫ t in interval schurEndpoint, ∫ u in interval schurEndpoint,
      finiteKernel archConstant firstPrimeWeight firstPrimeLog J t u * v u * v t) =
    ∫ t in interval schurEndpoint,
      nativeOperator schurEndpoint archConstant firstPrimeWeight firstPrimeLog J
        (primitive schurEndpoint v) t * primitive schurEndpoint v t :=
  finite_J_Schur_identity schurEndpoint_geometry.1 schurEndpoint_geometry.2 hv
    archConstant firstPrimeWeight J

theorem first_prime_endpoint_integrable {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure schurEndpoint)) (J : ℕ) :
    IntegrableOn (fun t => ∫ u in interval schurEndpoint,
      finiteKernel archConstant firstPrimeWeight firstPrimeLog J t u * v u * v t)
      (interval schurEndpoint) ∧
    IntegrableOn (fun t =>
      nativeOperator schurEndpoint archConstant firstPrimeWeight firstPrimeLog J
        (primitive schurEndpoint v) t * primitive schurEndpoint v t)
      (interval schurEndpoint) :=
  ⟨finiteKernel_outer_integrable schurEndpoint_geometry.1 schurEndpoint_geometry.2 hv
      archConstant firstPrimeWeight J,
    native_quadratic_integrable schurEndpoint_geometry.1 schurEndpoint_geometry.2 hv
      archConstant firstPrimeWeight J⟩

end RhAnchored
#print axioms RhAnchored.first_prime_endpoint_finite_identity
#print axioms RhAnchored.first_prime_endpoint_integrable
