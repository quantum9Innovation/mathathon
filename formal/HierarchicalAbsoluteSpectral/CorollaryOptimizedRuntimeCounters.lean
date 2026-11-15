import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeConstants
import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeDegrees

/-! The actual mass-inverse count, bisection cap and repetition counter
are logarithmic scalar budgets for the constant comparator schedule. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {N m r : ℕ}

theorem comparator_halving_linear_bound (x epsilon H : ℝ) (hx : 0 < x)
    (hepsilon : 0 < epsilon) (hH : 0 ≤ H) (hlog : Real.log (x/epsilon) ≤ H) :
    (leastHalvings x epsilon hepsilon:ℝ) ≤ 2*H+1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : H/Real.log 2 ≤ 2*H := by
    apply (div_le_iff₀ hlog2).mpr
    nlinarith [mul_le_mul_of_nonneg_left family_log_two_lower hH]
  exact (comparator_halving_log_bound x epsilon H hx hepsilon hH hlog).trans (by linarith)

theorem comparator_mass_accuracy_eq (I : FixedProblem N m N r 1)
    (haccuracy : I.accuracy=comparatorAccuracy) : I.massAccuracy=I.alpha*(1/1048576) := by
  have hC : hierarchyConstant 1+1 ≠ 0 := by linarith [hierarchyConstant_ge_one 1]
  unfold FixedProblem.massAccuracy FixedProblem.alpha literalFinalMass literalFinalAlpha
  rw [haccuracy,comparatorAccuracy_one]
  field_simp

theorem comparator_neumann_count_bound (I : FixedProblem N m N r 1)
    (haccuracy : I.accuracy=comparatorAccuracy) :
    (neumannCount I.massAccuracy I.final_budget.mass_positive:ℝ) ≤ 10000*comparatorScalarMagnitude I := by
  have hb := comparatorScalarMagnitude_bounds I
  have hα1 : I.alpha ≤ 1 := by have hh:=I.final_budget.alpha_small; change I.alpha ≤ _ at hh; linarith
  have hm1 : I.massAccuracy < 1 := by
    rw [comparator_mass_accuracy_eq I haccuracy]
    linarith
  have hraw := neumannCount_bound I.massAccuracy I.final_budget.mass_positive hm1
  have hc : Real.log (1048576:ℝ) ≤ 1048575 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 1048576)
    linarith
  have he : Real.log (1/I.massAccuracy)=Real.log (1/I.alpha)+Real.log 1048576 := by
    rw [comparator_mass_accuracy_eq I haccuracy,one_div,Real.log_inv,
      Real.log_mul I.alpha_positive.ne' (by norm_num),Real.log_div (by norm_num) (by norm_num),
      Real.log_one,one_div,Real.log_inv]
    ring
  rw [he] at hraw
  linarith [hb.1,hb.2.2.2.1]

theorem comparator_query_cap_bound (I : FixedProblem N m N r 1)
    (haccuracy : I.accuracy=comparatorAccuracy) :
    (I.queryCap:ℝ) ≤ 10000*comparatorScalarMagnitude I := by
  let M := comparatorScalarMagnitude I
  have hb := comparatorScalarMagnitude_bounds I
  have hM : 1000 ≤ M := hb.1
  have hm : 1 ≤ m := I.rank_positive.trans I.rank_le_core
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hlogm : Real.log (m:ℝ) ≤ M :=
    (Real.log_le_log hm0 (by have h : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith)).trans hb.2.1
  have hβ0 : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
  have hβ1 : I.singleFailure ≤ 1 := by
    have hh := I.delta_lt_one
    dsimp [FixedProblem.singleFailure]
    linarith
  let R := gaussianCaptureRadius m 1 I.singleFailure
  have hR : 1 ≤ R := gaussianCaptureRadius_ge_one m 1 I.singleFailure hm le_rfl hβ0 hβ1
  have hRp : 0 < R := by linarith
  have hlog100 : Real.log (100:ℝ) ≤ 99 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 100)
    linarith
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hlog16 : Real.log (16:ℝ) ≤ 15 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 16)
    linarith
  have hlogR : Real.log R ≤ 297+6*M := by
    have he : Real.log R=3*(Real.log 100+Real.log (m:ℝ)+Real.log (1/I.singleFailure)) := by
      dsimp [R,gaussianCaptureRadius]
      rw [Real.log_pow,Real.log_div (by positivity) hβ0.ne',
        Real.log_mul (by norm_num) hm0.ne',one_div,Real.log_inv]
      norm_num
      ring
    rw [he]
    linarith [hb.2.2.2.2]
  have hlogSum : Real.log (1+R) ≤ 298+6*M := by
    have hh := Real.log_le_log (show 0 < 1+R by linarith) (show 1+R ≤ 2*R by linarith)
    rw [Real.log_mul (by norm_num) hRp.ne'] at hh
    linarith
  have hnear : I.alpha*(1/1048576) ≤ I.nearTolerance := by
    have hC := hierarchyConstant_ge_one 1
    change I.alpha*(1/1048576) ≤ 4*hierarchyConstant 1*I.alpha*I.accuracy 1
    rw [haccuracy,comparatorAccuracy_one]
    nlinarith [mul_le_mul_of_nonneg_right hC I.alpha_positive.le]
  have hlogNear : Real.log (1/I.nearTolerance) ≤ M+1048575 := by
    have hh := Real.log_le_log (one_div_pos.mpr I.nearTolerance_positive)
      (one_div_le_one_div_of_le (by positivity : 0 < I.alpha*(1/1048576)) hnear)
    have hc : Real.log (1048576:ℝ) ≤ 1048575 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 1048576)
      linarith
    have he : Real.log (1/(I.alpha*(1/1048576)))=Real.log (1/I.alpha)+Real.log 1048576 := by
      rw [one_div,Real.log_inv,Real.log_mul I.alpha_positive.ne' (by norm_num),
        Real.log_div (by norm_num) (by norm_num),Real.log_one,one_div,Real.log_inv]
      ring
    rw [he] at hh
    linarith [hb.2.2.2.1]
  have hinit : 0 < initializerRatio m I.singleFailure := by
    unfold initializerRatio
    have hh := Real.sqrt_pos.mpr hm0
    dsimp [R] at hRp
    positivity
  have hlog : Real.log ((16*initializerRatio m I.singleFailure)/I.nearTolerance) ≤ 2000*M := by
    have he : Real.log ((16*initializerRatio m I.singleFailure)/I.nearTolerance)=
        Real.log 16+Real.log (m:ℝ)/2+Real.log (1+R)+Real.log (1/I.nearTolerance) := by
      rw [Real.log_div (by positivity) I.nearTolerance_positive.ne',
        Real.log_mul (by norm_num) hinit.ne']
      unfold initializerRatio
      rw [Real.log_mul (Real.sqrt_pos.mpr hm0).ne' (by positivity),Real.log_sqrt hm0.le,
        one_div,Real.log_inv]
      rfl
    rw [he]
    linarith
  have hh := comparator_halving_linear_bound (16*initializerRatio m I.singleFailure) I.nearTolerance
    (2000*M) (by positivity) I.nearTolerance_positive (by linarith) hlog
  change (I.queryCap:ℝ) ≤ _ at hh
  linarith

theorem comparator_repetitions_bound (I : FixedProblem N m N r 1)
    (haccuracy : I.accuracy=comparatorAccuracy) :
    (I.repetitions:ℝ) ≤ 30000*comparatorScalarMagnitude I := by
  let M := comparatorScalarMagnitude I
  have hb := comparatorScalarMagnitude_bounds I
  have hM : 1000 ≤ M := hb.1
  have hcap := comparator_query_cap_bound I haccuracy
  have hβ0 : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
  have he : 1/I.queryFailure=((I.queryCap:ℝ)+1)*(1/I.singleFailure) := by
    unfold FixedProblem.queryFailure FixedProblem.singleFailure
    field_simp
    <;> ring
  have hlog : Real.log (1/I.queryFailure) ≤ 10001*M := by
    rw [he,Real.log_mul (by positivity) (by positivity)]
    have hh := Real.log_le_sub_one_of_pos (show (0:ℝ) < (I.queryCap:ℝ)+1 by positivity)
    linarith [hb.2.2.2.2]
  have hh := comparator_halving_linear_bound 1 I.queryFailure (10001*M)
    (by norm_num) I.queryFailure_positive (by linarith) hlog
  change (I.repetitions:ℝ) ≤ _ at hh
  linarith

end
end HierarchicalAbsoluteSpectral
