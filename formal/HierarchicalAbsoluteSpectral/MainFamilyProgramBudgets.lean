import HierarchicalAbsoluteSpectral.MainFamilyProgramAnalytic

/-! Confidence allocation and the two rounded scalar loop counts used by
the actual fixed-depth caller, with one uniform logarithmic budget. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {N m r : ℕ}

def familyQueryCapCoefficient (D c : ℝ) : ℝ := (5*D+3*c+70)/Real.log 2

theorem family_singleFailure_log_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (c : ℝ) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) :
    Real.log (1/P.fixed.singleFailure) ≤ (c+5)*Real.log (m : ℝ) := by
  have hlogδ := familyProgram_confidence_log_bound I c hδ
  have h20 : Real.log (20 : ℝ) ≤ 5*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 20)
      (by norm_num : (20 : ℝ) ≤ (2 : ℝ)^5)
    rwa [Real.log_pow] at hh
  rw [FixedProblem.singleFailure,P.input_failure]
  have he : Real.log (1/(I.delta/20)) = Real.log 20+Real.log (1/I.delta) := by
    rw [one_div,Real.log_inv,Real.log_div I.delta_positive.ne' (by norm_num),one_div,Real.log_inv]
    ring
  rw [he]
  nlinarith

theorem PreparedFamilyProblem.near_log_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D : ℝ) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    Real.log (1/P.fixed.nearTolerance) ≤ (5*D+19)*Real.log (m : ℝ) := by
  let s := Real.sqrt (m/N : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr I.ratio_positive
  have hC := hierarchyConstant_ge_one P.depth
  have hh := P.fixed.accuracy_positive P.depth le_rfl
  have hθ : P.fixed.theta = s^5 := by
    rw [P.normal_theta hL]
    exact (family_theta_square_root _ _ (Nat.cast_nonneg _) (by exact_mod_cast I.side_positive)).symm
  have hnear : s^5/500000 ≤ P.fixed.nearTolerance := by
    unfold FixedProblem.nearTolerance literalFinalX literalFinalAlpha
    rw [hθ]
    have he : 4*hierarchyConstant P.depth*(s^5/(1000000*(hierarchyConstant P.depth+1)*P.fixed.accuracy P.depth))*
        P.fixed.accuracy P.depth =
        (4*hierarchyConstant P.depth*s^5)/(1000000*(hierarchyConstant P.depth+1)) := by
      field_simp [hh.ne',show hierarchyConstant P.depth+1 ≠ 0 by linarith]
      <;> ring
    rw [he]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 500000) (by positivity)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (pow_pos hs 5).le]
  have hi : 1/P.fixed.nearTolerance ≤ 500000/s^5 := by
    have hb := one_div_le_one_div_of_le (by positivity : 0 < s^5/500000) hnear
    simpa only [one_div_div] using hb
  have hlog := Real.log_le_log (one_div_pos.mpr P.fixed.nearTolerance_positive) hi
  have h500000 : Real.log (500000 : ℝ) ≤ 19*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 500000)
      (by norm_num : (500000 : ℝ) ≤ (2 : ℝ)^19)
    rwa [Real.log_pow] at hh
  have he : Real.log (500000/s^5) = Real.log 500000+5*Real.log (1/s) := by
    rw [Real.log_div (by norm_num) (pow_pos hs 5).ne',Real.log_pow,one_div,Real.log_inv]
    ring
  rw [he] at hlog
  change Real.log (1/s) ≤ D*Real.log (m : ℝ) at hscale
  nlinarith

theorem PreparedFamilyProblem.initializer_budget_log_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (c : ℝ) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) :
    Real.log (16*initializerRatio m P.fixed.singleFailure) ≤ (3*c+50)*Real.log (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast I.core_positive
  have hβ : 0 < P.fixed.singleFailure := div_pos P.fixed.delta_positive (by norm_num)
  have hβ1 : P.fixed.singleFailure ≤ 1 := by
    have hh := P.fixed.delta_lt_one
    unfold FixedProblem.singleFailure
    linarith
  have hβlog := family_singleFailure_log_bound I P c hm hδ
  have hR := gaussianCaptureRadius_ge_one m 1 P.fixed.singleFailure I.core_positive le_rfl hβ hβ1
  have hRpos : 0 < gaussianCaptureRadius m 1 P.fixed.singleFailure := by linarith
  have hbudget : 16*initializerRatio m P.fixed.singleFailure ≤
      32*Real.sqrt (m : ℝ)*gaussianCaptureRadius m 1 P.fixed.singleFailure := by
    unfold initializerRatio
    nlinarith [mul_nonneg (Real.sqrt_nonneg (m : ℝ)) (sub_nonneg.mpr hR)]
  have hbudgetpos : 0 < 16*initializerRatio m P.fixed.singleFailure := by
    unfold initializerRatio
    positivity
  have hlog := Real.log_le_log hbudgetpos hbudget
  have h100 : Real.log (100 : ℝ) ≤ 7*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 100)
      (by norm_num : (100 : ℝ) ≤ (2 : ℝ)^7)
    rwa [Real.log_pow] at hh
  have he : Real.log (32*Real.sqrt (m : ℝ)*gaussianCaptureRadius m 1 P.fixed.singleFailure) =
      5*Real.log 2+Real.log (m : ℝ)/2+
        3*(Real.log 100+Real.log (m : ℝ)+Real.log (1/P.fixed.singleFailure)) := by
    unfold gaussianCaptureRadius
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity),
      Real.log_sqrt hm0.le,Real.log_pow,Real.log_div (by positivity) hβ.ne',mul_one,
      Real.log_mul (by norm_num) hm0.ne',one_div,Real.log_inv,
      show (32 : ℝ) = 2^5 by norm_num,Real.log_pow]
    ring
  rw [he] at hlog
  have hlogm0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hm
  nlinarith

theorem PreparedFamilyProblem.queryCap_log_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) :
    (P.fixed.queryCap : ℝ) ≤ familyQueryCapCoefficient D c*Real.log (m : ℝ) := by
  have hnear := P.near_log_bound I hL D hm hscale
  have hbudget := P.initializer_budget_log_bound I c hm hδ
  have hβ : 0 < P.fixed.singleFailure := div_pos P.fixed.delta_positive (by norm_num)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast I.core_positive
  have hRpos : 0 < initializerRatio m P.fixed.singleFailure := by
    unfold initializerRatio gaussianCaptureRadius
    positivity
  have hlog : Real.log ((16*initializerRatio m P.fixed.singleFailure)/P.fixed.nearTolerance) ≤
      (5*D+3*c+69)*Real.log (m : ℝ) := by
    rw [Real.log_div (by positivity) P.fixed.nearTolerance_positive.ne']
    rw [one_div,Real.log_inv] at hnear
    linarith
  have hlogmax : Real.log (max 1 ((16*initializerRatio m P.fixed.singleFailure)/P.fixed.nearTolerance)) ≤
      (5*D+3*c+69)*Real.log (m : ℝ) := by
    by_cases h : (16*initializerRatio m P.fixed.singleFailure)/P.fixed.nearTolerance ≤ 1
    · rw [max_eq_left h,Real.log_one]
      have hlogm := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hm
      positivity
    · rw [max_eq_right (le_of_not_ge h)]
      exact hlog
  have hu := leastHalvings_log_bound (16*initializerRatio m P.fixed.singleFailure)
    P.fixed.nearTolerance P.fixed.nearTolerance_positive
  change (P.fixed.queryCap : ℝ) ≤ _ at hu
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hdiv := div_le_div_of_nonneg_right hlogmax hlog2.le
  have hone : 1 ≤ Real.log (m : ℝ)/Real.log 2 := (le_div_iff₀ hlog2).mpr (by simpa using hm)
  unfold familyQueryCapCoefficient
  calc
    _ ≤ 1+Real.log (max 1 ((16*initializerRatio m P.fixed.singleFailure)/P.fixed.nearTolerance))/Real.log 2 := hu
    _ ≤ Real.log (m : ℝ)/Real.log 2+(5*D+3*c+69)*Real.log (m : ℝ)/Real.log 2 := add_le_add hone hdiv
    _ = _ := by ring

theorem PreparedFamilyProblem.repetitions_log_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) :
    (P.fixed.repetitions : ℝ) ≤
      ((c+6+familyQueryCapCoefficient D c)/Real.log 2)*Real.log (m : ℝ) := by
  have hcap := P.queryCap_log_bound I hL D c hD hc hm hscale hδ
  have hδlog := familyProgram_confidence_log_bound I c hδ
  have h20 : Real.log (20 : ℝ) ≤ 5*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 20)
      (by norm_num : (20 : ℝ) ≤ (2 : ℝ)^5)
    rwa [Real.log_pow] at hh
  have hlogQ : Real.log ((P.fixed.queryCap : ℝ)+1) ≤ P.fixed.queryCap := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < (P.fixed.queryCap : ℝ)+1)
    linarith
  have hlogβ : Real.log (1/P.fixed.queryFailure) ≤
      (c+5+familyQueryCapCoefficient D c)*Real.log (m : ℝ) := by
    unfold FixedProblem.queryFailure
    rw [P.input_failure,one_div,Real.log_inv,Real.log_div I.delta_positive.ne' (by positivity),
      Real.log_mul (by norm_num) (by positivity)]
    rw [one_div,Real.log_inv] at hδlog
    linarith
  have hlogmax : Real.log (max 1 (1/P.fixed.queryFailure)) ≤
      (c+5+familyQueryCapCoefficient D c)*Real.log (m : ℝ) := by
    by_cases h : 1/P.fixed.queryFailure ≤ 1
    · rw [max_eq_left h,Real.log_one]
      have hlogm := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hm
      unfold familyQueryCapCoefficient
      positivity
    · rw [max_eq_right (le_of_not_ge h)]
      exact hlogβ
  have hu := leastHalvings_log_bound 1 P.fixed.queryFailure P.fixed.queryFailure_positive
  change (P.fixed.repetitions : ℝ) ≤ _ at hu
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hdiv := div_le_div_of_nonneg_right hlogmax hlog2.le
  have hone : 1 ≤ Real.log (m : ℝ)/Real.log 2 := (le_div_iff₀ hlog2).mpr (by simpa using hm)
  calc
    _ ≤ 1+Real.log (max 1 (1/P.fixed.queryFailure))/Real.log 2 := hu
    _ ≤ Real.log (m : ℝ)/Real.log 2+
      (c+5+familyQueryCapCoefficient D c)*Real.log (m : ℝ)/Real.log 2 := add_le_add hone hdiv
    _ = _ := by ring

theorem PreparedFamilyProblem.sketchFailure_log_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D c : ℝ) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) :
    Real.log (1/P.fixed.sketchFailure) ≤ (c+5+2*D)*Real.log (m : ℝ) := by
  have hδlog := familyProgram_confidence_log_bound I c hδ
  have hdepth := familySchedule_depth_log_linear (Real.sqrt_pos.mpr I.ratio_positive)
    P.scalars.schedule_scale (by rw [familyScalarSchedule_scale_depth]; exact Nat.pos_of_ne_zero hL) hscale
  rw [← P.normal_depth I hL] at hdepth
  have h20 : Real.log (20 : ℝ) ≤ 5*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 20)
      (by norm_num : (20 : ℝ) ≤ (2 : ℝ)^5)
    rwa [Real.log_pow] at hh
  have hlogL : Real.log ((P.depth : ℝ)+1) ≤ P.depth := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < (P.depth : ℝ)+1)
    linarith
  have hlogtwo := mul_le_mul_of_nonneg_left family_log_two_lower (Nat.cast_nonneg P.depth)
  unfold FixedProblem.sketchFailure
  rw [P.input_failure,one_div,Real.log_inv,Real.log_div I.delta_positive.ne' (by positivity),
    Real.log_mul (by norm_num) (by positivity)]
  rw [one_div,Real.log_inv] at hδlog
  nlinarith

theorem PreparedFamilyProblem.embedding_rows_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) (n j : ℕ) (hj : j ≤ P.depth) :
    (embeddingComputedRowCount n m (P.fixed.accuracy j) P.fixed.sketchFailure : ℝ) ≤
      1+8192*((m : ℝ)+27*(((c+2*D+10)/Real.log 2)*Real.log (m : ℝ))^3)/(P.fixed.accuracy j)^2 := by
  have hβ : 0 < P.fixed.sketchFailure := by
    unfold FixedProblem.sketchFailure
    exact div_pos P.fixed.delta_positive (by positivity)
  have hβ1 : P.fixed.sketchFailure ≤ 1 := by
    unfold FixedProblem.sketchFailure
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := P.fixed.delta_lt_one
    have hdepth : (0 : ℝ) ≤ P.depth := Nat.cast_nonneg _
    linarith
  have hb := family_embedding_rows_uniform_bound n m (P.fixed.accuracy j) P.fixed.sketchFailure
    (c+5+2*D) hm (P.fixed.accuracy_positive j hj) hβ hβ1 (by positivity)
    (P.sketchFailure_log_bound I hL D c hmLog hscale hδ)
  simpa only [show c+5+2*D+5 = c+2*D+10 by ring] using hb

end
end HierarchicalAbsoluteSpectral
