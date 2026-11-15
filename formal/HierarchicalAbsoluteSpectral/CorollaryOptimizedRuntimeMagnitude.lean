import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeCounters

/-! Fixed-schedule scalar magnitudes reduce to the two original accuracy
and confidence logarithms.  Capping a larger input accuracy only changes
the inverse-root bound by a fixed constant. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {N m r : ℕ}

def comparatorAlphaDenominator : ℝ := 1000000*(hierarchyConstant 1+1)*(1/1048576)

def comparatorConditionConstant : ℝ :=
  (1+hierarchyUpper 0/(8*(1/1048576)))*(1+hierarchyUpper 1/(8*(1/1024)))

def comparatorScalarLogConstant : ℝ :=
  1000+|Real.log comparatorConditionConstant|+|Real.log comparatorAlphaDenominator|+|Real.log 20|

def comparatorMagnitudeCoefficient (Dtheta Ddelta : ℝ) : ℝ :=
  2*comparatorScalarLogConstant+2+Dtheta+Ddelta

theorem comparatorAlphaDenominator_positive : 0 < comparatorAlphaDenominator := by
  have hC := hierarchyConstant_ge_one 1
  unfold comparatorAlphaDenominator
  positivity

theorem comparatorAlphaDenominator_ge_one : 1 ≤ comparatorAlphaDenominator := by
  have hC := hierarchyConstant_ge_one 1
  unfold comparatorAlphaDenominator
  nlinarith

theorem comparator_alpha_eq (I : FixedProblem N m N r 1)
    (haccuracy : I.accuracy=comparatorAccuracy) : I.alpha=I.theta/comparatorAlphaDenominator := by
  unfold FixedProblem.alpha literalFinalAlpha comparatorAlphaDenominator
  rw [haccuracy,comparatorAccuracy_one]

theorem comparator_condition_eq (I : FixedProblem N m N r 1)
    (haccuracy : I.accuracy=comparatorAccuracy) : mainConditionBound I=comparatorConditionConstant := by
  unfold mainConditionBound comparatorConditionConstant
  rw [haccuracy,comparatorAccuracy_zero,comparatorAccuracy_one]

theorem comparator_magnitude_log_bound (I : FixedProblem N m N r 1)
    (haccuracy : I.accuracy=comparatorAccuracy) (Dtheta Ddelta : ℝ)
    (hm : 2 ≤ m)
    (hTheta : Real.log (1/I.theta) ≤ Dtheta*Real.log (m:ℝ))
    (hDelta : Real.log (1/I.delta) ≤ Ddelta*Real.log (m:ℝ)) :
    comparatorScalarMagnitude I ≤ comparatorMagnitudeCoefficient Dtheta Ddelta*Real.log (m:ℝ) := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hlog : (1/2:ℝ) ≤ Real.log (m:ℝ) := family_log_two_lower.trans
    (Real.log_le_log (by norm_num) hmR)
  have hlogm : Real.log (m+1:ℝ) ≤ 2*Real.log (m:ℝ) := by
    have hh := Real.log_le_log (show (0:ℝ) < (m:ℝ)+1 by positivity)
      (show (m:ℝ)+1 ≤ (m:ℝ)^2 by nlinarith)
    rw [Real.log_pow] at hh
    norm_num at hh
    exact hh
  have hloga : Real.log (1/I.alpha)=Real.log comparatorAlphaDenominator+Real.log (1/I.theta) := by
    rw [comparator_alpha_eq I haccuracy,one_div,Real.log_inv,
      Real.log_div I.theta_positive.ne' comparatorAlphaDenominator_positive.ne',one_div,Real.log_inv]
    ring
  have hlogb : Real.log (1/I.singleFailure)=Real.log 20+Real.log (1/I.delta) := by
    unfold FixedProblem.singleFailure
    rw [one_div,Real.log_inv,Real.log_div I.delta_positive.ne' (by norm_num),one_div,Real.log_inv]
    ring
  have hconstant : 0 ≤ comparatorScalarLogConstant := by unfold comparatorScalarLogConstant; positivity
  have hc : comparatorScalarLogConstant ≤ 2*comparatorScalarLogConstant*Real.log (m:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hconstant]
  have hraw : comparatorScalarMagnitude I ≤ comparatorScalarLogConstant+(2+Dtheta+Ddelta)*Real.log (m:ℝ) := by
    unfold comparatorScalarMagnitude
    rw [comparator_condition_eq I haccuracy,hloga,hlogb]
    unfold comparatorScalarLogConstant
    linarith [le_abs_self (Real.log comparatorConditionConstant),
      le_abs_self (Real.log comparatorAlphaDenominator),le_abs_self (Real.log 20)]
  unfold comparatorMagnitudeCoefficient
  nlinarith

theorem comparator_magnitude_coefficient_ge_one (Dtheta Ddelta : ℝ)
    (ht : 0 ≤ Dtheta) (hd : 0 ≤ Ddelta) : 1 ≤ comparatorMagnitudeCoefficient Dtheta Ddelta := by
  have hc : 1000 ≤ comparatorScalarLogConstant := by
    unfold comparatorScalarLogConstant
    linarith [abs_nonneg (Real.log comparatorConditionConstant),
      abs_nonneg (Real.log comparatorAlphaDenominator),abs_nonneg (Real.log 20)]
  unfold comparatorMagnitudeCoefficient
  linarith

theorem comparator_inverse_alpha_sqrt (I : FixedProblem N m N r 1)
    (haccuracy : I.accuracy=comparatorAccuracy) :
    1/Real.sqrt I.alpha=Real.sqrt comparatorAlphaDenominator/Real.sqrt I.theta := by
  rw [comparator_alpha_eq I haccuracy,Real.sqrt_div I.theta_positive.le]
  have h1 := (Real.sqrt_pos.mpr I.theta_positive).ne'
  have h2 := (Real.sqrt_pos.mpr comparatorAlphaDenominator_positive).ne'
  field_simp

theorem comparator_inverse_capped_sqrt (theta : ℝ) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    1/Real.sqrt (min theta (1/1048576)) ≤ 1024/Real.sqrt theta := by
  have hs := Real.sqrt_pos.mpr ht
  have hroot : Real.sqrt theta ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ht1
  by_cases h : theta ≤ 1/1048576
  · rw [min_eq_left h]
    exact div_le_div_of_nonneg_right (by norm_num) hs.le
  · rw [min_eq_right (le_of_not_ge h)]
    have hconst : Real.sqrt (1/1048576:ℝ)=1/1024 := by norm_num
    rw [hconst]
    norm_num only [one_div_div,div_one]
    apply (le_div_iff₀ hs).mpr
    nlinarith

end
end HierarchicalAbsoluteSpectral
