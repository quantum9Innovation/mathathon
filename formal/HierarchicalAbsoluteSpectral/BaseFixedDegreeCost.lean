import HierarchicalAbsoluteSpectral.BaseMainRandomizedCost
import HierarchicalAbsoluteSpectral.BaseFixedActionCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {n m p r L : ℕ}

theorem gaussianCaptureRadius_mono_dimension {k m : ℕ} (hkm : k ≤ m)
    (U β : ℝ) (hU : 0 ≤ U) (hβ : 0 < β) :
    gaussianCaptureRadius k U β ≤ gaussianCaptureRadius m U β := by
  unfold gaussianCaptureRadius
  gcongr

def fixedOuterLogBudget (I : FixedProblem n m p r L) : ℝ :=
  1+Real.log (20*gaussianCaptureRadius m (mainConditionBound I) (1/2)/(I.alpha/100))+
    Real.log (4*gaussianCaptureRadius m (mainConditionBound I) I.singleFailure/I.alpha)

theorem fixedOuterLogBudget_ge_one (I : FixedProblem n m p r L) : 1 ≤ fixedOuterLogBudget I := by
  have hm := I.rank_positive.trans I.rank_le_core
  have hU := mainConditionBound_ge_one I
  have hR := gaussianCaptureRadius_ge_one m (mainConditionBound I) (1/2) hm hU (by norm_num) (by norm_num)
  have hβ : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
  have hβ1 : I.singleFailure ≤ 1 := by
    have hh:=I.delta_lt_one
    dsimp [FixedProblem.singleFailure]
    linarith
  have hS := gaussianCaptureRadius_ge_one m (mainConditionBound I) I.singleFailure hm hU hβ hβ1
  have hα := I.alpha_positive
  have hα1 := I.final_budget.alpha_small
  change I.alpha ≤ _ at hα1
  have hlog1 : 0 ≤ Real.log (20*gaussianCaptureRadius m (mainConditionBound I) (1/2)/(I.alpha/100)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (div_pos hα (by norm_num))).mpr
    linarith
  have hlog2 : 0 ≤ Real.log (4*gaussianCaptureRadius m (mainConditionBound I) I.singleFailure/I.alpha) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hα).mpr
    linarith
  dsimp [fixedOuterLogBudget]
  linarith

def fixedOuterDegreeEnvelope (I : FixedProblem n m p r L) : ℝ :=
  200*fixedOuterLogBudget I/Real.sqrt I.alpha+1

theorem mainQueryDegree_fixed_bound
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) :
    (mainQueryDegree I S C hr:ℝ) ≤ fixedOuterDegreeEnvelope I := by
  have hU := mainConditionBound_ge_one I
  have hU0 : 0 ≤ mainConditionBound I := by linarith
  have hα := I.alpha_positive
  have hα1 : I.alpha/100 ≤ 1 := by
    have hh:=I.final_budget.alpha_small
    change I.alpha ≤ _ at hh
    linarith
  have hk : 1 ≤ C.pair.dimension := by omega
  have hR := gaussianCaptureRadius_mono_dimension C.pair.dimension_le_fin
    (mainConditionBound I) (1/2) hU0 (by norm_num)
  have hdeg := krylovDegree_bound C.pair.dimension (mainConditionBound I) (1/2) (I.alpha/100)
    hk hU (by norm_num) (by norm_num) (div_pos hα (by norm_num)) hα1
  have hlog : Real.log (20*gaussianCaptureRadius C.pair.dimension (mainConditionBound I) (1/2)/(I.alpha/100)) ≤
      Real.log (20*gaussianCaptureRadius m (mainConditionBound I) (1/2)/(I.alpha/100)) := by
    apply Real.log_le_log
    · have hh := gaussianCaptureRadius_ge_one C.pair.dimension (mainConditionBound I) (1/2)
        hk hU (by norm_num) (by norm_num)
      positivity
    · gcongr
  have hβ : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
  have hβ1 : I.singleFailure ≤ 1 := by
    have hh:=I.delta_lt_one
    dsimp [FixedProblem.singleFailure]
    linarith
  have hS := gaussianCaptureRadius_ge_one m (mainConditionBound I) I.singleFailure
    (I.rank_positive.trans I.rank_le_core) hU hβ hβ1
  have hlogS : 0 ≤ Real.log (4*gaussianCaptureRadius m (mainConditionBound I) I.singleFailure/I.alpha) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hα).mpr
    have hh:=I.final_budget.alpha_small
    change I.alpha ≤ _ at hh
    linarith
  have hlog' : Real.log (20*gaussianCaptureRadius C.pair.dimension (mainConditionBound I) (1/2)/(I.alpha/100)) ≤
      fixedOuterLogBudget I := by dsimp [fixedOuterLogBudget]; linarith
  have hsqrt : Real.sqrt (I.alpha/100/100)=Real.sqrt I.alpha/100 := by
    rw [div_div,show (100:ℝ)*100=10000 by norm_num,Real.sqrt_div hα.le]
    norm_num
  rw [hsqrt] at hdeg
  have hmul := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog' (by norm_num : (0:ℝ)≤200))
    (Real.sqrt_nonneg I.alpha)
  change (mainQueryDegree I S C hr:ℝ) ≤ _ at hdeg
  have hdeg' : (mainQueryDegree I S C hr:ℝ) ≤
      200*Real.log (20*gaussianCaptureRadius C.pair.dimension (mainConditionBound I) (1/2)/(I.alpha/100))/
        Real.sqrt I.alpha+1 := by
    convert hdeg using 1 <;> ring
  unfold fixedOuterDegreeEnvelope
  exact hdeg'.trans (add_le_add hmul (le_refl 1))

theorem mainStrongDegree_fixed_bound
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) :
    (mainStrongDegree I S C hk:ℝ) ≤ fixedOuterDegreeEnvelope I := by
  have hU := mainConditionBound_ge_one I
  have hU0 : 0 ≤ mainConditionBound I := by linarith
  have hα := I.alpha_positive
  have hα1 : I.alpha ≤ 1 := by
    have hh:=I.final_budget.alpha_small
    change I.alpha ≤ _ at hh
    linarith
  have hβ : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
  have hβ1 : I.singleFailure ≤ 1 := by
    have hh:=I.delta_lt_one
    dsimp [FixedProblem.singleFailure]
    linarith
  have hR := gaussianCaptureRadius_mono_dimension C.pair.dimension_le_fin
    (mainConditionBound I) I.singleFailure hU0 hβ
  have hdeg := strongGaussianDegree_bound C.pair.dimension (mainConditionBound I) I.singleFailure I.alpha
    hk hU hβ hβ1 hα hα1
  have hlog : Real.log (4*gaussianCaptureRadius C.pair.dimension (mainConditionBound I) I.singleFailure/I.alpha) ≤
      Real.log (4*gaussianCaptureRadius m (mainConditionBound I) I.singleFailure/I.alpha) := by
    apply Real.log_le_log
    · have hh := gaussianCaptureRadius_ge_one C.pair.dimension (mainConditionBound I) I.singleFailure hk hU hβ hβ1
      positivity
    · gcongr
  have hQ := gaussianCaptureRadius_ge_one m (mainConditionBound I) (1/2)
    (I.rank_positive.trans I.rank_le_core) hU (by norm_num) (by norm_num)
  have hlogQ : 0 ≤ Real.log (20*gaussianCaptureRadius m (mainConditionBound I) (1/2)/(I.alpha/100)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (div_pos hα (by norm_num))).mpr
    linarith
  have hlog' : Real.log (4*gaussianCaptureRadius C.pair.dimension (mainConditionBound I) I.singleFailure/I.alpha) ≤
      fixedOuterLogBudget I := by dsimp [fixedOuterLogBudget]; linarith
  have hL := fixedOuterLogBudget_ge_one I
  have htwo : 2*Real.log (4*gaussianCaptureRadius C.pair.dimension (mainConditionBound I) I.singleFailure/I.alpha) ≤
      200*fixedOuterLogBudget I := by linarith
  have hmul := div_le_div_of_nonneg_right htwo (Real.sqrt_nonneg I.alpha)
  change (mainStrongDegree I S C hk:ℝ) ≤ _ at hdeg
  unfold fixedOuterDegreeEnvelope
  linarith

theorem fixedOuterDegreeEnvelope_accuracy (I : FixedProblem n m p r L) :
    fixedOuterDegreeEnvelope I=
      200*fixedOuterLogBudget I*Real.sqrt (1000000*(hierarchyConstant L+1))*
        Real.sqrt (I.accuracy L/I.theta)+1 := by
  have hC := hierarchyConstant_ge_one L
  have hH := I.accuracy_positive L le_rfl
  have hθ := I.theta_positive
  have hA : 0 < 1000000*(hierarchyConstant L+1) := by positivity
  have he : 1/Real.sqrt I.alpha=
      Real.sqrt (1000000*(hierarchyConstant L+1))*Real.sqrt (I.accuracy L/I.theta) := by
    unfold FixedProblem.alpha literalFinalAlpha
    rw [Real.sqrt_div hθ.le,Real.sqrt_mul hA.le,Real.sqrt_div hH.le]
    field_simp
  unfold fixedOuterDegreeEnvelope
  rw [div_eq_mul_one_div,he]
  ring

def fixedOuterDegreeCap (I : FixedProblem n m p r L) : ℕ := ⌈fixedOuterDegreeEnvelope I⌉₊

def fixedKrylovRawWidth (I : FixedProblem n m p r L) : ℕ :=
  (2*fixedOuterDegreeCap I+1)*(r+1)

theorem mainQueryDegree_le_fixed_cap
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : mainQueryDegree I S C hr ≤ fixedOuterDegreeCap I := by
  exact_mod_cast (mainQueryDegree_fixed_bound I S C hr).trans (Nat.le_ceil (fixedOuterDegreeEnvelope I))

theorem mainStrongDegree_le_fixed_cap
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) : mainStrongDegree I S C hk ≤ fixedOuterDegreeCap I := by
  exact_mod_cast (mainStrongDegree_fixed_bound I S C hk).trans (Nat.le_ceil (fixedOuterDegreeEnvelope I))

theorem mainKrylovRawWidth_le_fixed
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) :
    (mainQueryDegree I S C hr+1)*(r+1) ≤ fixedKrylovRawWidth I := by
  have hh := mainQueryDegree_le_fixed_cap I S C hr
  apply Nat.mul_le_mul_right (r+1)
  omega

end
end HierarchicalAbsoluteSpectral
