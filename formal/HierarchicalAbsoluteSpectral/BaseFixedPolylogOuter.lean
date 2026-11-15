import HierarchicalAbsoluteSpectral.BaseFixedPolylogParameters

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
variable {n m p r L : ℕ}

def fixedPolylogOuterCoefficient (L : ℕ) : ℝ :=
  10*(fixedPolylogAlphaScale L+hierarchyUpper L+1000)

theorem fixedPolylog_log_one_add_ratio (B h : ℝ) (hB : 0 ≤ B) (hh : 0 < h) (hh1 : h ≤ 1) :
    Real.log (1+B/(8*h)) ≤ B+Real.log (1/h) := by
  have hmul : (1+B/(8*h))*h = h+B/8 := by field_simp [hh.ne']
  have hbound : 1+B/(8*h) ≤ (1+B)/h := by
    apply (le_div_iff₀ hh).mpr
    rw [hmul]
    nlinarith
  have hl := Real.log_le_log (by positivity : 0<1+B/(8*h)) hbound
  rw [Real.log_div (by positivity) hh.ne'] at hl
  have hc := Real.log_le_sub_one_of_pos (by positivity : 0<1+B)
  rw [one_div,Real.log_inv]
  linarith

theorem fixedPolylog_condition_log_bound (I : FixedProblem n m p r L) :
    Real.log (mainConditionBound I) ≤ (hierarchyUpper L+10)*fixedPolylogGauge I := by
  have h0 := I.accuracy_positive 0 (by omega)
  have hL := I.accuracy_positive L le_rfl
  have hB0 := hierarchyUpper_nonneg 0
  have hBL := hierarchyUpper_nonneg L
  have hfirst := fixedPolylog_log_one_add_ratio (hierarchyUpper 0) (I.accuracy L) hB0 hL
    (by linarith [I.accuracy_bounded L le_rfl])
  have hsecond := fixedPolylog_log_one_add_ratio (hierarchyUpper L) (I.accuracy 0) hBL h0
    (by linarith [I.accuracy_bounded 0 (by omega)])
  have hlog0 := fixedPolylog_accuracy_log_le I 0 (by omega)
  have hlogL := fixedPolylog_accuracy_log_le I L le_rfl
  have hz := fixedPolylogGauge_ge_one I
  have hc := mul_le_mul_of_nonneg_left hz (show 0≤hierarchyUpper L+2 by positivity)
  norm_num only [hierarchyUpper,zero_add,pow_one] at hfirst
  unfold mainConditionBound
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [show hierarchyUpper 0 = (2:ℝ) by norm_num [hierarchyUpper]]
  nlinarith only [hfirst,hsecond,hlog0,hlogL,hc,hz]

theorem fixedPolylog_capture_log_bound
    (I : FixedProblem n m p r L) (c β α a b : ℝ)
    (hc : 0 < c) (hβ : 0 < β) (hα : 0 < α)
    (hβlog : Real.log (1/β) ≤ b*fixedPolylogGauge I)
    (hαlog : Real.log (1/α) ≤ a*fixedPolylogGauge I) :
    Real.log (c*gaussianCaptureRadius m (mainConditionBound I) β/α) ≤
      (c+3*(100+hierarchyUpper L+10+b)+a)*fixedPolylogGauge I := by
  have hm : (0:ℝ) < m := by
    have hh := I.rank_positive.trans I.rank_le_core
    exact_mod_cast (by omega : 0 < m)
  have hU : 0 < mainConditionBound I := by linarith [mainConditionBound_ge_one I]
  have hUlog := fixedPolylog_condition_log_bound I
  have hmlog := (fixedPolylog_primitive_le I).2.2.1
  have hz := fixedPolylogGauge_ge_one I
  have hcLog := Real.log_le_sub_one_of_pos hc
  have h100 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<100)
  have hcZ := mul_le_mul_of_nonneg_left hz hc.le
  have he : Real.log (c*gaussianCaptureRadius m (mainConditionBound I) β/α) =
      Real.log c+3*(Real.log 100+Real.log (m:ℝ)+Real.log (mainConditionBound I)+Real.log (1/β))+
        Real.log (1/α) := by
    unfold gaussianCaptureRadius
    rw [Real.log_div (by positivity) hα.ne',Real.log_mul hc.ne' (by positivity),
      Real.log_pow,Real.log_div (by positivity) hβ.ne',
      Real.log_mul (by positivity) hU.ne',Real.log_mul (by norm_num) hm.ne',
      one_div,Real.log_inv,one_div,Real.log_inv]
    ring
  rw [he]
  nlinarith only [hUlog,hmlog,hz,hcLog,h100,hcZ,hβlog,hαlog]

theorem fixedPolylog_outerLog_bound (I : FixedProblem n m p r L) :
    fixedOuterLogBudget I ≤ fixedPolylogOuterCoefficient L*fixedPolylogGauge I := by
  have hz := fixedPolylogGauge_ge_one I
  have hA := fixedPolylogAlphaScale_ge_one L
  have hB := hierarchyUpper_nonneg L
  have hα := fixedPolylog_alpha_log_bound I
  have hβ := fixedPolylog_singleFailure_log I
  have hhalf : Real.log (1/(1/2:ℝ)) ≤ fixedPolylogGauge I := by
    norm_num only [one_div_div,div_one,inv_div,inv_one]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    linarith
  have hε : Real.log (1/(I.alpha/100)) ≤
      (fixedPolylogAlphaScale L+100)*fixedPolylogGauge I := by
    have he : Real.log (1/(I.alpha/100)) = Real.log 100+Real.log (1/I.alpha) := by
      rw [one_div,Real.log_inv,Real.log_div I.alpha_positive.ne' (by norm_num),one_div,Real.log_inv]
      ring
    rw [he]
    have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<100)
    nlinarith only [hc,hα,hz]
  have hfirst := fixedPolylog_capture_log_bound I 20 (1/2) (I.alpha/100)
    (fixedPolylogAlphaScale L+100) 1 (by norm_num) (by norm_num)
    (div_pos I.alpha_positive (by norm_num)) (by simpa using hhalf) hε
  have hsecond := fixedPolylog_capture_log_bound I 4 I.singleFailure I.alpha
    (fixedPolylogAlphaScale L+1) 20 (by norm_num)
    (div_pos I.delta_positive (by norm_num)) I.alpha_positive hβ hα
  have hsum : fixedOuterLogBudget I ≤
      (2*fixedPolylogAlphaScale L+6*hierarchyUpper L+849)*fixedPolylogGauge I := by
    unfold fixedOuterLogBudget
    nlinarith only [hfirst,hsecond,hz]
  have hc : 2*fixedPolylogAlphaScale L+6*hierarchyUpper L+849 ≤ fixedPolylogOuterCoefficient L := by
    unfold fixedPolylogOuterCoefficient
    linarith
  exact hsum.trans (mul_le_mul_of_nonneg_right hc (by linarith))

end
end HierarchicalAbsoluteSpectral
