import HierarchicalAbsoluteSpectral.MainFamilyProgramSequences
import HierarchicalAbsoluteSpectral.MainStatementsCore
import HierarchicalAbsoluteSpectral.RuntimeFamilyConstants
import HierarchicalAbsoluteSpectral.RuntimeFamilyQueryDegree

/-! The actual fixed-input tolerances and covariance bound, instantiated
with the executed family schedule. These identities connect the scalar
family analysis to the quantities used by the approximation program. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
variable {N m r : ℕ}

theorem familyScalarSchedule_scale_depth (out : FamilyScalarParameters (m : ℝ) (N : ℝ)) :
    out.schedule_scale.depth = out.schedule.depth := by
  rcases out with ⟨ρ,scale,ideal,theta,hρ,hscale,hideal,hθ,hs,hi,schedule⟩
  subst scale
  subst ideal
  rfl

theorem familyScalarSchedule_scale_terminal (out : FamilyScalarParameters (m : ℝ) (N : ℝ)) :
    out.schedule_scale.terminal = out.schedule.terminal := by
  rcases out with ⟨ρ,scale,ideal,theta,hρ,hscale,hideal,hθ,hs,hi,schedule⟩
  subst scale
  subst ideal
  rfl

theorem PreparedFamilyProblem.normal_depth (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0) :
    P.depth = P.scalars.schedule_scale.depth := by
  rw [familyScalarSchedule_scale_depth,P.depth_eq,if_neg hL]

theorem PreparedFamilyProblem.normal_accuracy_scale (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0) (j : ℕ) (hj : j ≤ P.depth) :
    P.fixed.accuracy j = familyScheduleValue (1/1024) (Real.sqrt (m/N : ℝ)/1024) j := by
  rw [P.normal_accuracy hL j hj,P.scalars.ideal_eq,P.scalars.scale_eq]

theorem PreparedFamilyProblem.normal_initial (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0) :
    P.fixed.accuracy 0 = 1/1024 := by
  rw [P.normal_accuracy_scale I hL 0 (Nat.zero_le _)]
  rfl

theorem PreparedFamilyProblem.normal_last (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0) :
    P.fixed.accuracy P.depth = P.scalars.schedule_scale.terminal := by
  rw [P.normal_accuracy_scale I hL _ le_rfl,P.normal_depth I hL,
    ← P.scalars.schedule_scale.terminal_eq]

theorem PreparedFamilyProblem.normal_alpha (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0) :
    P.fixed.alpha = familyOuterAccuracy P.scalars.schedule_scale := by
  unfold FixedProblem.alpha
  rw [hierarchy_final_alpha_eq,P.normal_theta hL,P.normal_last I hL]
  change I.theta/(accuracyScale P.depth*P.scalars.schedule_scale.terminal) = _
  rw [P.normal_depth I hL]
  unfold familyOuterAccuracy FamilyProblem.theta
  rw [family_theta_square_root _ _ (Nat.cast_nonneg _) (by exact_mod_cast I.side_positive)]

theorem PreparedFamilyProblem.normal_square_step (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (j : ℕ) (hj : j < P.depth) :
    (P.fixed.accuracy (j+1))^2 = P.fixed.accuracy j*(Real.sqrt (m/N : ℝ)/1024) := by
  rw [P.normal_accuracy_scale I hL (j+1) (by omega),P.normal_accuracy_scale I hL j (by omega),
    familyScheduleValue,Real.sq_sqrt]
  exact mul_nonneg (familyScheduleValue_pos _ _ (by norm_num)
    (by exact div_pos (Real.sqrt_pos.mpr I.ratio_positive) (by norm_num)) j).le
    (by positivity)

theorem PreparedFamilyProblem.condition_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0) :
    mainConditionBound P.fixed ≤ 1024*(2 : ℝ)^P.depth/Real.sqrt (m/N : ℝ) := by
  let s := Real.sqrt (m/N : ℝ)
  let h := P.fixed.accuracy P.depth
  have hs : 0 < s := Real.sqrt_pos.mpr I.ratio_positive
  have hh : 0 < h := P.fixed.accuracy_positive _ le_rfl
  have hb := P.normal_terminal I hL
  change s ≤ h ∧ h < 1024*s at hb
  have hhi : h ≤ 1/1024 := by
    dsimp only [h]
    rw [P.normal_last I hL,P.scalars.schedule_scale.terminal_eq]
    exact P.scalars.schedule_scale.level_le (by norm_num) (by positivity) _ le_rfl
  have hs1 : s ≤ 1 := by linarith
  have hp : 1 ≤ (2 : ℝ)^P.depth := one_le_pow₀ (by norm_num)
  have hinv : 1/h ≤ 1/s := one_div_le_one_div_of_le hs hb.1
  have hfirst : 1+2/(8*h) ≤ 2/s := by
    have hdiv : 1 ≤ 1/s := (le_div_iff₀ hs).mpr (by simpa using hs1)
    rw [show 2/(8*h) = (1/4)*(1/h) by ring,show 2/s = 2*(1/s) by ring]
    nlinarith
  have hsecond : 1+(2 : ℝ)^(P.depth+1)/(8*(1/1024)) ≤ 512*(2 : ℝ)^P.depth := by
    rw [pow_succ]
    norm_num <;> nlinarith
  unfold mainConditionBound
  rw [P.normal_initial I hL]
  simp only [hierarchyUpper,zero_add,pow_one]
  change (1+2/(8*h))*(1+(2 : ℝ)^(P.depth+1)/(8*(1/1024))) ≤ _
  calc
    _ ≤ (2/s)*(512*(2 : ℝ)^P.depth) := mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = _ := by dsimp only [s]; ring

theorem PreparedFamilyProblem.condition_log_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D : ℝ) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    Real.log (mainConditionBound P.fixed) ≤ (2*D+10)*Real.log (m : ℝ) := by
  have hs := Real.sqrt_pos.mpr I.ratio_positive
  have hU : 0 < mainConditionBound P.fixed := lt_of_lt_of_le (by norm_num) (mainConditionBound_ge_one _)
  have hlog := Real.log_le_log hU (P.condition_bound I hL)
  have hdepth := familySchedule_depth_log_linear hs P.scalars.schedule_scale
    (by rw [familyScalarSchedule_scale_depth]; exact Nat.pos_of_ne_zero hL) hscale
  rw [← P.normal_depth I hL] at hdepth
  have he : Real.log (1024*(2 : ℝ)^P.depth/Real.sqrt (m/N : ℝ)) =
      10*Real.log 2+(P.depth : ℝ)*Real.log 2+Real.log (1/Real.sqrt (m/N : ℝ)) := by
    rw [Real.log_div (by positivity) hs.ne',Real.log_mul (by norm_num) (by positivity),
      Real.log_pow,show (1024 : ℝ) = 2^10 by norm_num,Real.log_pow,one_div,Real.log_inv]
    norm_num
    ring
  rw [he] at hlog
  nlinarith

end
end HierarchicalAbsoluteSpectral
