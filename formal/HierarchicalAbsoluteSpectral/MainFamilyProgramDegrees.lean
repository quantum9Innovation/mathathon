import HierarchicalAbsoluteSpectral.MainFamilyProgramAnalytic
import HierarchicalAbsoluteSpectral.MainFamilyProgramBudgets
import HierarchicalAbsoluteSpectral.MainStatementsQueryViews
import HierarchicalAbsoluteSpectral.MainStatementsArrays

/-! Uniform degree bounds for the covariance envelope and Krylov degree
actually executed by the fixed-depth caller, rather than a different
scalar proxy. All constants are independent of the hierarchy level. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
variable {N m r : ℕ}

theorem PreparedFamilyProblem.alpha_inverse_sqrt_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0) :
    1/Real.sqrt P.fixed.alpha ≤
      224000*(10 : ℝ)^P.depth/(Real.sqrt (m/N : ℝ))^2 := by
  let out := P.scalars.schedule_scale
  have hs := Real.sqrt_pos.mpr I.ratio_positive
  have hdepth : P.depth = out.depth := P.normal_depth I hL
  have hpos : 0 < out.terminal := out.terminal_positive (by norm_num) (by positivity)
  have hA : 0 < accuracyScale out.depth := lt_of_lt_of_le (by norm_num) (family_accuracyScale_ge_one _)
  have hb := out.nonzero_terminal_bounds hs (by rw [← hdepth]; exact P.fixed.depth_positive)
  have hi := family_inverse_accuracy_sqrt_bound (Real.sqrt (m/N : ℝ))
    (accuracyScale out.depth) out.terminal hs hA hpos hb.2.le
  rw [P.normal_alpha I hL,hdepth]
  apply hi.trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  nlinarith [family_accuracyScale_sqrt_bound out.depth]

theorem PreparedFamilyProblem.alpha_log_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D : ℝ) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    Real.log (1/P.fixed.alpha) ≤ (12*D+26)*Real.log (m : ℝ) := by
  rw [P.normal_alpha I hL]
  exact family_accuracy_log_bound (Real.sqrt_pos.mpr I.ratio_positive) P.scalars.schedule_scale
    (by rw [familyScalarSchedule_scale_depth]; exact Nat.pos_of_ne_zero hL) hm hscale

theorem PreparedFamilyProblem.gaussian_log_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (hkm : (k : ℝ) ≤ m)
    (D Dβ β : ℝ) (hβ : 0 < β) (hD : 0 ≤ D)
    (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hconfidence : Real.log (1/β) ≤ Dβ*Real.log (m : ℝ)) :
    Real.log (4*gaussianCaptureRadius k (mainConditionBound P.fixed) β/P.fixed.alpha) ≤
      (18*D+3*Dβ+90)*Real.log (m : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hU : 0 < mainConditionBound P.fixed := lt_of_lt_of_le (by norm_num) (mainConditionBound_ge_one _)
  have hα := P.fixed.alpha_positive
  have hlogk := Real.log_le_log hk0 hkm
  have hlogU := P.condition_log_bound I hL D hm hscale
  have hlogα := P.alpha_log_bound I hL D hm hscale
  have h100 : Real.log (100 : ℝ) ≤ 7*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 100)
      (by norm_num : (100 : ℝ) ≤ (2 : ℝ)^7)
    rwa [Real.log_pow] at hh
  have he : Real.log (4*gaussianCaptureRadius k (mainConditionBound P.fixed) β/P.fixed.alpha) =
      2*Real.log 2+3*(Real.log 100+Real.log (k : ℝ)+Real.log (mainConditionBound P.fixed)+
        Real.log (1/β))+Real.log (1/P.fixed.alpha) := by
    unfold gaussianCaptureRadius
    rw [Real.log_div (by positivity) hα.ne',Real.log_mul (by norm_num) (by positivity),
      Real.log_pow,Real.log_div (by positivity) hβ.ne',Real.log_mul (by positivity) hU.ne',
      Real.log_mul (by norm_num) hk0.ne',one_div,Real.log_inv,one_div,Real.log_inv,
      show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
    ring
  rw [he]
  have hm0 : 0 ≤ Real.log (m : ℝ) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hm
  nlinarith

theorem PreparedFamilyProblem.strong_degree_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (hkm : (k : ℝ) ≤ m)
    (D Dβ β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hD : 0 ≤ D)
    (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hconfidence : Real.log (1/β) ≤ Dβ*Real.log (m : ℝ))
    (hα1 : P.fixed.alpha ≤ 1) :
    (strongGaussianDegree k (mainConditionBound P.fixed) β P.fixed.alpha hk
      (mainConditionBound_ge_one _) hβ hβ1 P.fixed.alpha_positive hα1 : ℝ) ≤
      448000*(18*D+3*Dβ+90)*((10 : ℝ)^P.depth/(Real.sqrt (m/N : ℝ))^2)*Real.log (m : ℝ)+1 := by
  have hlog := P.gaussian_log_bound I hL k hk hkm D Dβ β hβ hD hm hscale hconfidence
  have hi := P.alpha_inverse_sqrt_bound I hL
  have hu := gaussianDegree_scalar_bound k (mainConditionBound P.fixed) β P.fixed.alpha
    ((18*D+3*Dβ+90)*Real.log (m : ℝ)) (224000*(10 : ℝ)^P.depth/(Real.sqrt (m/N : ℝ))^2)
    hk (mainConditionBound_ge_one _) hβ hβ1 P.fixed.alpha_positive hα1 hlog hi
  convert hu using 1 <;> ring

theorem PreparedFamilyProblem.krylov_degree_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (hkm : (k : ℝ) ≤ m)
    (D : ℝ) (hD : 0 ≤ D) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hε : 0 < P.fixed.alpha/100) (hε1 : P.fixed.alpha/100 ≤ 1) :
    (krylovDegree k (mainConditionBound P.fixed) (1/2) (P.fixed.alpha/100) hk
      (mainConditionBound_ge_one _) (by norm_num) (by norm_num) hε hε1 : ℝ) ≤
      44800000*(18*D+110)*((10 : ℝ)^P.depth/(Real.sqrt (m/N : ℝ))^2)*Real.log (m : ℝ)+1 := by
  have hα := P.fixed.alpha_positive
  have hlog4 := P.gaussian_log_bound I hL k hk hkm D 1 (1/2) (by norm_num) hD hm hscale
    (by convert hm using 1 <;> norm_num)
  have hR := gaussianCaptureRadius_ge_one k (mainConditionBound P.fixed) (1/2) hk
    (mainConditionBound_ge_one _) (by norm_num) (by norm_num)
  have hRpos : 0 < gaussianCaptureRadius k (mainConditionBound P.fixed) (1/2) := by linarith
  have h500 : Real.log (500 : ℝ) ≤ 9*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 500)
      (by norm_num : (500 : ℝ) ≤ (2 : ℝ)^9)
    rwa [Real.log_pow] at hh
  have hlog : Real.log (20*gaussianCaptureRadius k (mainConditionBound P.fixed) (1/2)/(P.fixed.alpha/100)) ≤
      (18*D+110)*Real.log (m : ℝ) := by
    have he : 20*gaussianCaptureRadius k (mainConditionBound P.fixed) (1/2)/(P.fixed.alpha/100) =
        (4*gaussianCaptureRadius k (mainConditionBound P.fixed) (1/2)/P.fixed.alpha)*500 := by ring
    rw [he,Real.log_mul (by positivity) (by norm_num)]
    have hm0 : 0 ≤ Real.log (m : ℝ) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hm
    nlinarith
  have htarget : 1 ≤ 20*gaussianCaptureRadius k (mainConditionBound P.fixed) (1/2)/(P.fixed.alpha/100) :=
    (le_div_iff₀ hε).mpr (by linarith)
  have hbudget : 0 ≤ (18*D+110)*Real.log (m : ℝ) :=
    (Real.log_nonneg htarget).trans hlog
  have hroot : Real.sqrt (P.fixed.alpha/100/100) = Real.sqrt P.fixed.alpha/100 := by
    rw [div_div,show (100 : ℝ)*100 = 10000 by norm_num,Real.sqrt_div hα.le]
    norm_num
  have hi : 1/Real.sqrt (P.fixed.alpha/100/100) ≤
      22400000*(10 : ℝ)^P.depth/(Real.sqrt (m/N : ℝ))^2 := by
    rw [hroot]
    have he : 1/(Real.sqrt P.fixed.alpha/100) = 100*(1/Real.sqrt P.fixed.alpha) := by ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_left (P.alpha_inverse_sqrt_bound I hL) (by norm_num : (0 : ℝ) ≤ 100)
    exact hh.trans_eq (by ring)
  have hu := krylovDegree_bound k (mainConditionBound P.fixed) (1/2) (P.fixed.alpha/100) hk
    (mainConditionBound_ge_one _) (by norm_num) (by norm_num) hε hε1
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 2)) hi
    (by positivity : 0 ≤ 1/Real.sqrt (P.fixed.alpha/100/100)) (by linarith : 0 ≤ 2*((18*D+110)*Real.log (m : ℝ)))
  calc
    _ ≤ 2*Real.log (20*gaussianCaptureRadius k (mainConditionBound P.fixed) (1/2)/(P.fixed.alpha/100))/
      Real.sqrt (P.fixed.alpha/100/100)+1 := hu
    _ = (2*Real.log (20*gaussianCaptureRadius k (mainConditionBound P.fixed) (1/2)/(P.fixed.alpha/100)))*
      (1/Real.sqrt (P.fixed.alpha/100/100))+1 := by ring
    _ ≤ (2*((18*D+110)*Real.log (m : ℝ)))*
      (22400000*(10 : ℝ)^P.depth/(Real.sqrt (m/N : ℝ))^2)+1 := add_le_add hprod le_rfl
    _ = _ := by ring

def familyQueryDegreeCoefficient (D : ℝ) : ℝ := 44800000*(18*D+110)*D^4

def familyStrongDegreeCoefficient (D Dβ : ℝ) : ℝ := 448000*(18*D+3*Dβ+90)*D^4

theorem PreparedFamilyProblem.krylov_degree_polylog (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (hkm : (k : ℝ) ≤ m)
    (D : ℝ) (hD : 0 ≤ D) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hε : 0 < P.fixed.alpha/100) (hε1 : P.fixed.alpha/100 ≤ 1) :
    (krylovDegree k (mainConditionBound P.fixed) (1/2) (P.fixed.alpha/100) hk
      (mainConditionBound_ge_one _) (by norm_num) (by norm_num) hε hε1 : ℝ) ≤
      familyQueryDegreeCoefficient D*((N : ℝ)/m)*(Real.log (m : ℝ))^5+1 := by
  have hu := P.krylov_degree_bound I hL k hk hkm D hD hm hscale hε hε1
  have hs := Real.sqrt_pos.mpr I.ratio_positive
  have h10 := (family_depth_constants_polylog hs P.scalars.schedule_scale
    (by rw [familyScalarSchedule_scale_depth]; exact Nat.pos_of_ne_zero hL) hscale).2.1
  rw [← P.normal_depth I hL] at h10
  have hlogm : 0 ≤ Real.log (m : ℝ) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hm
  have hprod := mul_le_mul_of_nonneg_left h10
    (by positivity : 0 ≤ 44800000*(18*D+110)*Real.log (m : ℝ)/(Real.sqrt (m/N : ℝ))^2)
  apply hu.trans
  unfold familyQueryDegreeCoefficient
  rw [Real.sq_sqrt I.ratio_positive.le] at hprod ⊢
  convert add_le_add hprod (le_rfl : (1 : ℝ) ≤ 1) using 1 <;> simp only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv] <;> ring

theorem PreparedFamilyProblem.mainKrylov_degree_polylog (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (S : StoredSketches N m N P.depth) (C : MainSupportData S) (hr : r < C.pair.dimension)
    (D : ℝ) (hD : 0 ≤ D) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    (mainKrylovDegree P.fixed S C hr : ℝ) ≤
      familyQueryDegreeCoefficient D*((N : ℝ)/m)*(Real.log (m : ℝ))^5+1 := by
  unfold mainKrylovDegree mainRitzAccuracy
  apply P.krylov_degree_polylog I hL C.pair.dimension (by omega)
    (by exact_mod_cast mainSupport_dimension_le S C) D hD hm hscale

theorem PreparedFamilyProblem.strong_degree_polylog (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (hkm : (k : ℝ) ≤ m)
    (D Dβ β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hD : 0 ≤ D) (hDβ : 0 ≤ Dβ)
    (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hconfidence : Real.log (1/β) ≤ Dβ*Real.log (m : ℝ)) (hα1 : P.fixed.alpha ≤ 1) :
    (strongGaussianDegree k (mainConditionBound P.fixed) β P.fixed.alpha hk
      (mainConditionBound_ge_one _) hβ hβ1 P.fixed.alpha_positive hα1 : ℝ) ≤
      familyStrongDegreeCoefficient D Dβ*((N : ℝ)/m)*(Real.log (m : ℝ))^5+1 := by
  have hu := P.strong_degree_bound I hL k hk hkm D Dβ β hβ hβ1 hD hm hscale hconfidence hα1
  have hs := Real.sqrt_pos.mpr I.ratio_positive
  have h10 := (family_depth_constants_polylog hs P.scalars.schedule_scale
    (by rw [familyScalarSchedule_scale_depth]; exact Nat.pos_of_ne_zero hL) hscale).2.1
  rw [← P.normal_depth I hL] at h10
  have hlogm : 0 ≤ Real.log (m : ℝ) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hm
  have hprod := mul_le_mul_of_nonneg_left h10
    (by positivity : 0 ≤ 448000*(18*D+3*Dβ+90)*Real.log (m : ℝ)/(Real.sqrt (m/N : ℝ))^2)
  apply hu.trans
  unfold familyStrongDegreeCoefficient
  rw [Real.sq_sqrt I.ratio_positive.le] at hprod ⊢
  convert add_le_add hprod (le_rfl : (1 : ℝ) ≤ 1) using 1 <;> simp only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv] <;> ring

theorem PreparedFamilyProblem.mass_log_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D : ℝ) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    Real.log (1/P.fixed.massAccuracy) ≤ (13*D+26)*Real.log (m : ℝ) := by
  have hαlog := P.alpha_log_bound I hL D hm hscale
  have hs := Real.sqrt_pos.mpr I.ratio_positive
  have hh := P.fixed.accuracy_positive P.depth le_rfl
  have hlogh := Real.log_le_log hs (P.normal_terminal I hL).1
  have hmass : P.fixed.massAccuracy = P.fixed.alpha*P.fixed.accuracy P.depth := by
    have hC := hierarchyConstant_ge_one P.depth
    unfold FixedProblem.massAccuracy FixedProblem.alpha literalFinalMass literalFinalAlpha
    field_simp [hh.ne',show hierarchyConstant P.depth+1 ≠ 0 by linarith]
  rw [hmass,one_div,Real.log_inv,Real.log_mul P.fixed.alpha_positive.ne' hh.ne']
  rw [one_div,Real.log_inv] at hαlog hscale
  nlinarith

theorem PreparedFamilyProblem.mass_neumann_count_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D : ℝ) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    (neumannCount P.fixed.massAccuracy P.fixed.final_budget.mass_positive : ℝ) ≤
      (52*D+106)*Real.log (m : ℝ) := by
  have hsmall := P.fixed.final_budget.mass_floor
  have hh : P.fixed.accuracy P.depth ≤ 1/1024 := by
    rw [P.normal_last I hL,P.scalars.schedule_scale.terminal_eq]
    exact P.scalars.schedule_scale.level_le (by norm_num)
      (div_pos (Real.sqrt_pos.mpr I.ratio_positive) (by norm_num)) _ le_rfl
  have hmass1 : P.fixed.massAccuracy < 1 := by
    change P.fixed.massAccuracy ≤ P.fixed.accuracy P.depth/100 at hsmall
    linarith
  have hu := neumannCount_bound P.fixed.massAccuracy P.fixed.final_budget.mass_positive hmass1
  have hlog := P.mass_log_bound I hL D hm hscale
  have hlogm : 1/2 ≤ Real.log (m : ℝ) := family_log_two_lower.trans hm
  nlinarith

theorem PreparedFamilyProblem.fine_mass_log_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D : ℝ) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (j : ℕ) (hj : j ≤ P.depth) :
    Real.log (1/(P.fixed.accuracy j/100)) ≤ (D+7)*Real.log (m : ℝ) := by
  have hs := Real.sqrt_pos.mpr I.ratio_positive
  have hdepth := P.normal_depth I hL
  have hj' : j ≤ P.scalars.schedule_scale.depth := by omega
  have hb := P.scalars.schedule_scale.level_bounds hs
    (by rw [← hdepth]; exact P.fixed.depth_positive) j hj'
  rw [← P.normal_accuracy_scale I hL j hj] at hb
  have hlogh := Real.log_le_log hs hb.1
  have hh := P.fixed.accuracy_positive j hj
  have h100 : Real.log (100 : ℝ) ≤ 7*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 100)
      (by norm_num : (100 : ℝ) ≤ (2 : ℝ)^7)
    rwa [Real.log_pow] at hh
  rw [one_div,Real.log_inv,Real.log_div hh.ne' (by norm_num)]
  rw [one_div,Real.log_inv] at hscale
  nlinarith

theorem PreparedFamilyProblem.fine_neumann_count_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D : ℝ) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (j : ℕ) (hj : j ≤ P.depth) (hε : 0 < P.fixed.accuracy j/100) :
    (neumannCount (P.fixed.accuracy j/100) hε : ℝ) ≤ (4*D+30)*Real.log (m : ℝ) := by
  have hs := Real.sqrt_pos.mpr I.ratio_positive
  have hdepth := P.normal_depth I hL
  have hj' : j ≤ P.scalars.schedule_scale.depth := by omega
  have hb := P.scalars.schedule_scale.level_bounds hs
    (by rw [← hdepth]; exact P.fixed.depth_positive) j hj'
  rw [← P.normal_accuracy_scale I hL j hj] at hb
  have hε1 : P.fixed.accuracy j/100 < 1 := by linarith [hb.2]
  have hu := neumannCount_bound (P.fixed.accuracy j/100) hε hε1
  have hlog := P.fine_mass_log_bound I hL D hm hscale j hj
  have hlogm : 1/2 ≤ Real.log (m : ℝ) := family_log_two_lower.trans hm
  nlinarith

end
end HierarchicalAbsoluteSpectral
