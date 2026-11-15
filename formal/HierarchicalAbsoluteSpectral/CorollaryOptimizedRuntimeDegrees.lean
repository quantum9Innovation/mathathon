import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeScalars
import HierarchicalAbsoluteSpectral.BaseMainStrongCost

/-! One scalar-computable degree cap works uniformly for every computed
support dimension.  Its only accuracy power is alpha^(-1/2). -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {n m p r L : ℕ}

def comparatorScalarMagnitude (I : FixedProblem n m p r L) : ℝ :=
  1000+Real.log (m+1:ℝ)+Real.log (mainConditionBound I)+
    Real.log (1/I.alpha)+Real.log (1/I.singleFailure)

theorem comparatorScalarMagnitude_bounds (I : FixedProblem n m p r L) :
    1000 ≤ comparatorScalarMagnitude I ∧
      Real.log (m+1:ℝ) ≤ comparatorScalarMagnitude I ∧
      Real.log (mainConditionBound I) ≤ comparatorScalarMagnitude I ∧
      Real.log (1/I.alpha) ≤ comparatorScalarMagnitude I ∧
      Real.log (1/I.singleFailure) ≤ comparatorScalarMagnitude I := by
  have hm : 0 ≤ Real.log (m+1:ℝ) := Real.log_nonneg
    (by have hmn : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  have hU : 0 ≤ Real.log (mainConditionBound I) := Real.log_nonneg (mainConditionBound_ge_one I)
  have hα1 : I.alpha ≤ 1 := by have hh:=I.final_budget.alpha_small; change I.alpha ≤ _ at hh; linarith
  have hα : 0 ≤ Real.log (1/I.alpha) := Real.log_nonneg
    ((one_le_div I.alpha_positive).mpr hα1)
  have hβ0 : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
  have hβ1 : I.singleFailure ≤ 1 := by
    have hh := I.delta_lt_one
    dsimp [FixedProblem.singleFailure]
    linarith
  have hβ : 0 ≤ Real.log (1/I.singleFailure) := Real.log_nonneg ((one_le_div hβ0).mpr hβ1)
  dsimp [comparatorScalarMagnitude]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

def comparatorOuterDegreeCap (I : FixedProblem n m p r L) : ℕ :=
  ⌈10000*comparatorScalarMagnitude I*(1+Real.log (m:ℝ))/Real.sqrt I.alpha+1⌉₊

theorem comparator_log_scale (m : ℕ) (hm : 2 ≤ m) (M x : ℝ)
    (hM : 0 ≤ M) (hx : x ≤ M) : x ≤ (2*M)*Real.log (m:ℝ) := by
  have hlog : (1/2:ℝ) ≤ Real.log (m:ℝ) := family_log_two_lower.trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hm))
  nlinarith [mul_le_mul_of_nonneg_left hlog hM]

theorem mainQueryDegree_comparator_cap (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (hm : 2 ≤ m) (hr : r < C.pair.dimension) :
    mainQueryDegree I S C hr ≤ comparatorOuterDegreeCap I := by
  let M := comparatorScalarMagnitude I
  have hb := comparatorScalarMagnitude_bounds I
  have hM : 1000 ≤ M := hb.1
  have hM0 : 0 ≤ M := by linarith
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlogm : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hU := comparator_log_scale m hm M (Real.log (mainConditionBound I)) hM0 hb.2.2.1
  have hlogα := comparator_log_scale m hm M (Real.log (1/I.alpha)) hM0 hb.2.2.2.1
  have hα1 : I.alpha ≤ 1 := by have hh:=I.final_budget.alpha_small; change I.alpha ≤ _ at hh; linarith
  have hε : 0 < I.alpha/100 := div_pos I.alpha_positive (by norm_num)
  have hε1 : I.alpha/100 ≤ 1 := by linarith
  have hlog100 : Real.log (100:ℝ) ≤ 99 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 100)
    linarith
  have he : Real.log (1/(I.alpha/100))=Real.log 100+Real.log (1/I.alpha) := by
    rw [one_div,Real.log_inv,Real.log_div I.alpha_positive.ne' (by norm_num),one_div,Real.log_inv]
    ring
  have hεlog : Real.log (1/(I.alpha/100)) ≤ (4*M)*Real.log (m:ℝ) := by
    rw [he]
    have hh' := comparator_log_scale m hm (2*M) (Real.log 100+Real.log (1/I.alpha))
      (by positivity) (by linarith)
    nlinarith
  have hβlog : Real.log (1/(1/2:ℝ)) ≤ (1:ℝ)*Real.log (m:ℝ) := by
    norm_num only [one_div_div,div_one,one_mul]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hm)
  have hq := comparator_krylov_degree_bound C.pair.dimension (m:ℝ)
    (mainConditionBound I) (1/2) (I.alpha/100) (2*M) 1 (4*M)
    (by omega) (by exact_mod_cast C.pair.dimension_le_fin) (by exact_mod_cast hm)
    (mainConditionBound_ge_one I) (by norm_num) (by norm_num) hε hε1 hU hβlog hεlog
  have hroot : Real.sqrt (I.alpha/100)=Real.sqrt I.alpha/10 := by
    rw [Real.sqrt_div I.alpha_positive.le]
    norm_num
  rw [hroot] at hq
  have hco : 200*(29+3*(2*M)+3*1+4*M) ≤ 10000*M := by nlinarith
  have hnum : 200*(29+3*(2*M)+3*1+4*M)*Real.log (m:ℝ) ≤
      10000*M*(1+Real.log (m:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hco hlogm
    nlinarith
  have hqr : (mainQueryDegree I S C hr:ℝ) ≤
      10000*M*(1+Real.log (m:ℝ))/Real.sqrt I.alpha+1 := by
    apply hq.trans
    convert add_le_add_right (div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg I.alpha)) 1 using 1 <;> ring
  exact_mod_cast hqr.trans (Nat.le_ceil _)

theorem mainStrongDegree_comparator_cap (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (hm : 2 ≤ m) (hk : 1 ≤ C.pair.dimension) :
    mainStrongDegree I S C hk ≤ comparatorOuterDegreeCap I := by
  let M := comparatorScalarMagnitude I
  have hb := comparatorScalarMagnitude_bounds I
  have hM : 1000 ≤ M := hb.1
  have hM0 : 0 ≤ M := by linarith
  have hlogm : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hU := comparator_log_scale m hm M (Real.log (mainConditionBound I)) hM0 hb.2.2.1
  have ha := comparator_log_scale m hm M (Real.log (1/I.alpha)) hM0 hb.2.2.2.1
  have hβ := comparator_log_scale m hm M (Real.log (1/I.singleFailure)) hM0 hb.2.2.2.2
  have hβ0 : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
  have hβ1 : I.singleFailure ≤ 1 := by
    have hh := I.delta_lt_one
    dsimp [FixedProblem.singleFailure]
    linarith
  have hα1 : I.alpha ≤ 1 := by have hh:=I.final_budget.alpha_small; change I.alpha ≤ _ at hh; linarith
  have hq := comparator_strong_degree_bound C.pair.dimension (m:ℝ)
    (mainConditionBound I) I.singleFailure I.alpha (2*M) (2*M) (2*M)
    hk (by exact_mod_cast C.pair.dimension_le_fin) (by exact_mod_cast hm)
    (mainConditionBound_ge_one I) hβ0 hβ1 I.alpha_positive hα1 hU hβ ha
  have hco : 2*(29+3*(2*M)+3*(2*M)+2*M) ≤ 10000*M := by nlinarith
  have hnum : 2*(29+3*(2*M)+3*(2*M)+2*M)*Real.log (m:ℝ) ≤
      10000*M*(1+Real.log (m:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hco hlogm
    nlinarith
  have hqr : (mainStrongDegree I S C hk:ℝ) ≤
      10000*M*(1+Real.log (m:ℝ))/Real.sqrt I.alpha+1 := by
    apply hq.trans
    convert (add_le_add_right (div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg I.alpha)) 1) using 1 <;> ring
  exact_mod_cast hqr.trans (Nat.le_ceil _)

end
end HierarchicalAbsoluteSpectral
