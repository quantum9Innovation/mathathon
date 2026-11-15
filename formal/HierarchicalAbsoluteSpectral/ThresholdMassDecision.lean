import HierarchicalAbsoluteSpectral.MinMaxNegation
import HierarchicalAbsoluteSpectral.ThresholdNearTransfer
import HierarchicalAbsoluteSpectral.ThresholdRepeatedSafe

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped InnerProductSpace MatrixOrder
variable {k : ℕ}

def massThresholdOperator (Q R Rb : Core k) (t : ℝ) : Core k :=
  1-Rᵀ*(t • inverseMetric Rb-Q)*R

theorem massThresholdOperator_isHermitian (Q R Rb : Core k) (hQ : Q.IsHermitian) (t : ℝ) :
    (massThresholdOperator Q R Rb t).IsHermitian := by
  have hm : (inverseMetric Rb).IsHermitian := by
    simp only [inverseMetric,Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_mul,Matrix.transpose_transpose]
  exact Matrix.isHermitian_one.sub (normalized_isHermitian R _ (by
    exact ((hm.smul (by simp : star t = t)).sub hQ).eq))

theorem massThresholdOperator_shift (Q R Rb : Core k) (t : ℝ) :
    massThresholdOperator Q R Rb t-1 • (1 : Core k) = Rᵀ*(Q-t • inverseMetric Rb)*R := by
  simp only [massThresholdOperator,one_smul,Matrix.mul_sub,Matrix.sub_mul]
  module

theorem normalized_mass_shift (Q Rb : Core k) (hRb : IsUnit Rb.det) (t : ℝ) :
    Rbᵀ*(Q-t • inverseMetric Rb)*Rb = Rbᵀ*Q*Rb-t • (1 : Core k) := by
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    inverseMetric_normalized Rb hRb]

/-- Strict below/above answers retain the exact generalized eigenvalue sign;
no gap or simplicity assumption is imposed on the spectrum. -/
theorem massThresholdOperator_below_iff (Q R Rb : Core k) (hQ : Q.IsHermitian)
    (hR : IsUnit R.det) (hRb : IsUnit Rb.det) (t : ℝ) (j : Fin k) :
    1 < orderedEigenvalue (massThresholdOperator Q R Rb t)
      (massThresholdOperator_isHermitian Q R Rb hQ t) j ↔
    t < orderedEigenvalue (Rbᵀ*Q*Rb) (normalized_isHermitian Rb Q hQ.eq) j := by
  let A := Q-t • inverseMetric Rb
  have hm : (inverseMetric Rb).IsHermitian := (inverseMetric_posDef Rb hRb).isHermitian
  have hA : A.IsHermitian := hQ.sub (hm.smul (by simp : star t = t))
  have h₁ := orderedEigenvalue_shift (massThresholdOperator Q R Rb t)
    (massThresholdOperator_isHermitian Q R Rb hQ t) 1 j
  have h₂ := orderedEigenvalue_shift (Rbᵀ*Q*Rb) (normalized_isHermitian Rb Q hQ.eq) t j
  have hr := positive_eigenvalue_congruence A R hA hR j
  have hb := positive_eigenvalue_congruence A Rb hA hRb j
  have ht : (massThresholdOperator Q R Rb t-1 • (1 : Core k)) = Rᵀ*A*R :=
    massThresholdOperator_shift Q R Rb t
  have hmass : Rbᵀ*A*Rb = Rbᵀ*Q*Rb-t • (1 : Core k) := normalized_mass_shift Q Rb hRb t
  have hsign : 0 < orderedEigenvalue (massThresholdOperator Q R Rb t-1 • (1 : Core k))
      (shifted_isHermitian _ (massThresholdOperator_isHermitian Q R Rb hQ t) 1) j ↔
      0 < orderedEigenvalue (Rbᵀ*Q*Rb-t • (1 : Core k))
        (shifted_isHermitian _ (normalized_isHermitian Rb Q hQ.eq) t) j := by
    simpa only [← ht,hmass,one_smul] using hr.trans hb.symm
  rw [h₁,h₂] at hsign
  simpa only [sub_pos] using hsign

theorem massThresholdOperator_above_iff (Q R Rb : Core k) (hQ : Q.IsHermitian)
    (hR : IsUnit R.det) (hRb : IsUnit Rb.det) (t : ℝ) (j : Fin k) :
    orderedEigenvalue (massThresholdOperator Q R Rb t)
      (massThresholdOperator_isHermitian Q R Rb hQ t) j < 1 ↔
    orderedEigenvalue (Rbᵀ*Q*Rb) (normalized_isHermitian Rb Q hQ.eq) j < t := by
  let A := Q-t • inverseMetric Rb
  have hm : (inverseMetric Rb).IsHermitian := (inverseMetric_posDef Rb hRb).isHermitian
  have hA : A.IsHermitian := hQ.sub (hm.smul (by simp : star t = t))
  have h₁ := orderedEigenvalue_shift (massThresholdOperator Q R Rb t)
    (massThresholdOperator_isHermitian Q R Rb hQ t) 1 j
  have h₂ := orderedEigenvalue_shift (Rbᵀ*Q*Rb) (normalized_isHermitian Rb Q hQ.eq) t j
  have hr := negative_eigenvalue_congruence A R hA hR j
  have hb := negative_eigenvalue_congruence A Rb hA hRb j
  have ht : (massThresholdOperator Q R Rb t-1 • (1 : Core k)) = Rᵀ*A*R :=
    massThresholdOperator_shift Q R Rb t
  have hmass : Rbᵀ*A*Rb = Rbᵀ*Q*Rb-t • (1 : Core k) := normalized_mass_shift Q Rb hRb t
  have hsign : orderedEigenvalue (massThresholdOperator Q R Rb t-1 • (1 : Core k))
      (shifted_isHermitian _ (massThresholdOperator_isHermitian Q R Rb hQ t) 1) j < 0 ↔
      orderedEigenvalue (Rbᵀ*Q*Rb-t • (1 : Core k))
        (shifted_isHermitian _ (normalized_isHermitian Rb Q hQ.eq) t) j < 0 := by
    simpa only [← ht,hmass,one_smul] using hr.trans hb.symm
  rw [h₁,h₂] at hsign
  simpa only [sub_neg] using hsign

theorem massThresholdOperator_near (Q R Rb : Core k) (hQ : Q.IsHermitian)
    (t α : ℝ) (j : Fin k)
    (hnear : |1-orderedEigenvalue (massThresholdOperator Q R Rb t)
      (massThresholdOperator_isHermitian Q R Rb hQ t) j| ≤ α) :
    orderedEigenvalue (Rᵀ*(t • inverseMetric Rb-Q)*R)
      (normalized_isHermitian R _ (by
        simp [inverseMetric,Matrix.transpose_mul,real_hermitian_transpose hQ])) j.rev ≤ α := by
  have hh := orderedEigenvalue_id_sub (Rᵀ*(t • inverseMetric Rb-Q)*R)
    (normalized_isHermitian R _ (by
      simp [inverseMetric,Matrix.transpose_mul,real_hermitian_transpose hQ])) j
  change |1-orderedEigenvalue (1-Rᵀ*(t • inverseMetric Rb-Q)*R) _ j| ≤ α at hnear
  rw [hh] at hnear
  simpa only [sub_sub_cancel] using (le_abs_self _).trans hnear

theorem massThresholdOperator_near_abs (Q R Rb : Core k) (hQ : Q.IsHermitian)
    (t α : ℝ) (j : Fin k)
    (hnear : |1-orderedEigenvalue (massThresholdOperator Q R Rb t)
      (massThresholdOperator_isHermitian Q R Rb hQ t) j| ≤ α) :
    |orderedEigenvalue (Rᵀ*(t • inverseMetric Rb-Q)*R)
      (normalized_isHermitian R _ (by
        simp [inverseMetric,Matrix.transpose_mul,real_hermitian_transpose hQ])) j.rev| ≤ α := by
  have hh := orderedEigenvalue_id_sub (Rᵀ*(t • inverseMetric Rb-Q)*R)
    (normalized_isHermitian R _ (by
      simp [inverseMetric,Matrix.transpose_mul,real_hermitian_transpose hQ])) j
  change |1-orderedEigenvalue (1-Rᵀ*(t • inverseMetric Rb-Q)*R) _ j| ≤ α at hnear
  rw [hh] at hnear
  simpa only [sub_sub_cancel] using hnear

theorem massThresholdOperator_safe_decision (Q R Rb : Core k) (hQ : Q.IsHermitian)
    (hR : IsUnit R.det) (hRb : IsUnit Rb.det) (t ε : ℝ) (j : Fin k)
    (d : ThresholdDecision)
    (hsafe : ThresholdDecisionSafe (orderedEigenvalue (massThresholdOperator Q R Rb t)
      (massThresholdOperator_isHermitian Q R Rb hQ t) j) ε d) :
    match d with
    | .below => t ≤ orderedEigenvalue (Rbᵀ*Q*Rb) (normalized_isHermitian Rb Q hQ.eq) j
    | .above => orderedEigenvalue (Rbᵀ*Q*Rb) (normalized_isHermitian Rb Q hQ.eq) j ≤ t
    | .near => |orderedEigenvalue (Rᵀ*(t • inverseMetric Rb-Q)*R)
        (normalized_isHermitian R _ (by
          simp [inverseMetric,Matrix.transpose_mul,real_hermitian_transpose hQ])) j.rev| ≤ 2*ε := by
  cases d with
  | below => exact ((massThresholdOperator_below_iff Q R Rb hQ hR hRb t j).mp hsafe).le
  | above => exact ((massThresholdOperator_above_iff Q R Rb hQ hR hRb t j).mp hsafe).le
  | near => exact massThresholdOperator_near_abs Q R Rb hQ t (2*ε) j hsafe

end
end HierarchicalAbsoluteSpectral
