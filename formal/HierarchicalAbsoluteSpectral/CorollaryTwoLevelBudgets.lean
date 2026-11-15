import HierarchicalAbsoluteSpectral.CorollaryTwoLevelProgram
import HierarchicalAbsoluteSpectral.MainScalarProgram

/-! Logarithmic budgets for the actual threshold cap, repetition count,
and scalar preparation of the two-level caller. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
variable {N m r : ℕ}

def twoLevelQueryCapCoefficient (c : ℝ) : ℝ := (3*c+73)/Real.log 2
def twoLevelRepetitionCoefficient (c : ℝ) : ℝ :=
  (c+6+twoLevelQueryCapCoefficient c)/Real.log 2

theorem TwoLevelProblem.failure_log_bound (I : TwoLevelProblem N m r)
    (c : ℝ) (hδ : (m:ℝ)^(-c) ≤ I.delta) :
    Real.log (1/I.delta) ≤ c*Real.log m := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast I.core_positive
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hm0 _) hδ
  rw [Real.log_rpow hm0] at hl
  rw [one_div,Real.log_inv]
  linarith

theorem TwoLevelProblem.singleFailure_log_bound (I : TwoLevelProblem N m r)
    (c : ℝ) (hm : Real.log 2 ≤ Real.log (m:ℝ)) (hδ : (m:ℝ)^(-c) ≤ I.delta) :
    Real.log (1/I.fixed.singleFailure) ≤ (c+5)*Real.log m := by
  have hlogδ := I.failure_log_bound c hδ
  have h20 : Real.log (20:ℝ) ≤ 5*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ) < 20)
      (by norm_num : (20:ℝ) ≤ (2:ℝ)^5)
    rwa [Real.log_pow] at hh
  change Real.log (1/(I.delta/20)) ≤ _
  have he : Real.log (1/(I.delta/20)) = Real.log 20+Real.log (1/I.delta) := by
    rw [one_div,Real.log_inv,Real.log_div I.delta_positive.ne' (by norm_num),one_div,Real.log_inv]
    ring
  rw [he]
  nlinarith only [hlogδ,h20,hm]

theorem TwoLevelProblem.near_lower_bound (I : TwoLevelProblem N m r) :
    (m:ℝ)^(-(11/25:ℝ))/2000000 ≤ I.fixed.nearTolerance := by
  have hm : (1:ℝ) ≤ m := by exact_mod_cast I.core_positive
  have hb := (twoLevelParameters_bounds m hm).2.2.2.2.1
  have ht := (twoLevelParameters_positive m).2.2
  have hh := (twoLevelParameters_positive m).2.1
  have he : I.fixed.nearTolerance = (148/37010000:ℝ)*twoLevelTheta m := by
    simp only [FixedProblem.nearTolerance,literalFinalX,FixedProblem.alpha,literalFinalAlpha,
      TwoLevelProblem.fixed_theta,TwoLevelProblem.fixed_accuracy,twoLevelAccuracy,
      one_ne_zero,ite_false,hierarchyConstant]
    norm_num
    field_simp [hh.ne']
    <;> ring
  rw [he]
  nlinarith only [hb,ht]

theorem TwoLevelProblem.near_log_bound (I : TwoLevelProblem N m r)
    (hm : Real.log 2 ≤ Real.log (m:ℝ)) :
    Real.log (1/I.fixed.nearTolerance) ≤ 22*Real.log m := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast I.core_positive
  have hi : 1/I.fixed.nearTolerance ≤ 2000000*(m:ℝ)^(11/25:ℝ) := by
    calc
      _ ≤ 1/((m:ℝ)^(-(11/25:ℝ))/2000000) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) I.near_lower_bound
      _ = _ := by rw [Real.rpow_neg hm0.le]; field_simp <;> ring
  have hl := Real.log_le_log (one_div_pos.mpr I.fixed.nearTolerance_positive) hi
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hm0 _).ne',Real.log_rpow hm0] at hl
  have hC : Real.log (2000000:ℝ) ≤ 21*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ) < 2000000)
      (by norm_num : (2000000:ℝ) ≤ (2:ℝ)^21)
    rwa [Real.log_pow] at hh
  have hlog0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).le.trans hm
  nlinarith only [hl,hC,hm,hlog0]

theorem TwoLevelProblem.initializer_log_bound (I : TwoLevelProblem N m r)
    (c : ℝ) (hm : Real.log 2 ≤ Real.log (m:ℝ)) (hδ : (m:ℝ)^(-c) ≤ I.delta) :
    Real.log (16*initializerRatio m I.fixed.singleFailure) ≤ (3*c+50)*Real.log m := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast I.core_positive
  have hβ : 0 < I.fixed.singleFailure := div_pos I.delta_positive (by norm_num)
  have hβ1 : I.fixed.singleFailure ≤ 1 := by
    change I.delta/20 ≤ 1
    linarith [I.delta_lt_one]
  have hβlog := I.singleFailure_log_bound c hm hδ
  have hR := gaussianCaptureRadius_ge_one m 1 I.fixed.singleFailure I.core_positive le_rfl hβ hβ1
  have hRpos : 0 < gaussianCaptureRadius m 1 I.fixed.singleFailure := by linarith
  have hbudget : 16*initializerRatio m I.fixed.singleFailure ≤
      32*Real.sqrt (m:ℝ)*gaussianCaptureRadius m 1 I.fixed.singleFailure := by
    unfold initializerRatio
    nlinarith [mul_nonneg (Real.sqrt_nonneg (m:ℝ)) (sub_nonneg.mpr hR)]
  have hbudgetpos : 0 < 16*initializerRatio m I.fixed.singleFailure := by
    unfold initializerRatio
    positivity
  have hl := Real.log_le_log hbudgetpos hbudget
  have h100 : Real.log (100:ℝ) ≤ 7*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ) < 100)
      (by norm_num : (100:ℝ) ≤ (2:ℝ)^7)
    rwa [Real.log_pow] at hh
  have he : Real.log (32*Real.sqrt (m:ℝ)*gaussianCaptureRadius m 1 I.fixed.singleFailure) =
      5*Real.log 2+Real.log (m:ℝ)/2+
        3*(Real.log 100+Real.log (m:ℝ)+Real.log (1/I.fixed.singleFailure)) := by
    unfold gaussianCaptureRadius
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity),
      Real.log_sqrt hm0.le,Real.log_pow,Real.log_div (by positivity) hβ.ne',mul_one,
      Real.log_mul (by norm_num) hm0.ne',one_div,Real.log_inv,
      show (32:ℝ) = 2^5 by norm_num,Real.log_pow]
    ring
  rw [he] at hl
  have hlog0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).le.trans hm
  nlinarith only [hl,h100,hβlog,hm,hlog0]

theorem TwoLevelProblem.queryCap_log_bound (I : TwoLevelProblem N m r)
    (c : ℝ) (hc : 0 ≤ c) (hm : Real.log 2 ≤ Real.log (m:ℝ))
    (hδ : (m:ℝ)^(-c) ≤ I.delta) :
    (I.fixed.queryCap:ℝ) ≤ twoLevelQueryCapCoefficient c*Real.log m := by
  have hn := I.near_log_bound hm
  have hb := I.initializer_log_bound c hm hδ
  have hm0 : (0:ℝ) < m := by exact_mod_cast I.core_positive
  have hβ : 0 < I.fixed.singleFailure := div_pos I.delta_positive (by norm_num)
  have hR : 0 < initializerRatio m I.fixed.singleFailure := by unfold initializerRatio gaussianCaptureRadius; positivity
  have hl : Real.log ((16*initializerRatio m I.fixed.singleFailure)/I.fixed.nearTolerance) ≤
      (3*c+72)*Real.log m := by
    rw [Real.log_div (by positivity) I.fixed.nearTolerance_positive.ne']
    rw [one_div,Real.log_inv] at hn
    linarith
  have hmax : Real.log (max 1 ((16*initializerRatio m I.fixed.singleFailure)/I.fixed.nearTolerance)) ≤
      (3*c+72)*Real.log m := by
    by_cases h : (16*initializerRatio m I.fixed.singleFailure)/I.fixed.nearTolerance ≤ 1
    · rw [max_eq_left h,Real.log_one]
      have hlog0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).le.trans hm
      positivity
    · rw [max_eq_right (le_of_not_ge h)]
      exact hl
  have hu := leastHalvings_log_bound (16*initializerRatio m I.fixed.singleFailure)
    I.fixed.nearTolerance I.fixed.nearTolerance_positive
  change (I.fixed.queryCap:ℝ) ≤ _ at hu
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hd := div_le_div_of_nonneg_right hmax hl2.le
  have hone : 1 ≤ Real.log (m:ℝ)/Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa only [one_mul] using hm)
  calc
    _ ≤ 1+Real.log (max 1 ((16*initializerRatio m I.fixed.singleFailure)/I.fixed.nearTolerance))/Real.log 2 := hu
    _ ≤ Real.log (m:ℝ)/Real.log 2+(3*c+72)*Real.log m/Real.log 2 := add_le_add hone hd
    _ = _ := by unfold twoLevelQueryCapCoefficient; ring

theorem TwoLevelProblem.repetitions_log_bound (I : TwoLevelProblem N m r)
    (c : ℝ) (hc : 0 ≤ c) (hm : Real.log 2 ≤ Real.log (m:ℝ))
    (hδ : (m:ℝ)^(-c) ≤ I.delta) :
    (I.fixed.repetitions:ℝ) ≤ twoLevelRepetitionCoefficient c*Real.log m := by
  have hcap := I.queryCap_log_bound c hc hm hδ
  have hlogδ := I.failure_log_bound c hδ
  have h20 : Real.log (20:ℝ) ≤ 5*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ) < 20)
      (by norm_num : (20:ℝ) ≤ (2:ℝ)^5)
    rwa [Real.log_pow] at hh
  have hlogQ : Real.log ((I.fixed.queryCap:ℝ)+1) ≤ I.fixed.queryCap := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < (I.fixed.queryCap:ℝ)+1)
    linarith
  have hlogβ : Real.log (1/I.fixed.queryFailure) ≤
      (c+5+twoLevelQueryCapCoefficient c)*Real.log m := by
    change Real.log (1/(I.delta/(20*((I.fixed.queryCap:ℝ)+1)))) ≤ _
    rw [one_div,Real.log_inv,Real.log_div I.delta_positive.ne' (by positivity),
      Real.log_mul (by norm_num) (by positivity)]
    rw [one_div,Real.log_inv] at hlogδ
    linarith
  have hmax : Real.log (max 1 (1/I.fixed.queryFailure)) ≤
      (c+5+twoLevelQueryCapCoefficient c)*Real.log m := by
    by_cases h : 1/I.fixed.queryFailure ≤ 1
    · rw [max_eq_left h,Real.log_one]
      have hlog0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).le.trans hm
      unfold twoLevelQueryCapCoefficient
      positivity
    · rw [max_eq_right (le_of_not_ge h)]
      exact hlogβ
  have hu := leastHalvings_log_bound 1 I.fixed.queryFailure I.fixed.queryFailure_positive
  change (I.fixed.repetitions:ℝ) ≤ _ at hu
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hd := div_le_div_of_nonneg_right hmax hl2.le
  have hone : 1 ≤ Real.log (m:ℝ)/Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa only [one_mul] using hm)
  calc
    _ ≤ 1+Real.log (max 1 (1/I.fixed.queryFailure))/Real.log 2 := hu
    _ ≤ Real.log (m:ℝ)/Real.log 2+(c+5+twoLevelQueryCapCoefficient c)*Real.log m/Real.log 2 := add_le_add hone hd
    _ = _ := by unfold twoLevelRepetitionCoefficient; ring

end
end HierarchicalAbsoluteSpectral
