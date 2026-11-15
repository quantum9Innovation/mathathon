import HierarchicalAbsoluteSpectral.MainFamilyProgramAnalytic
import HierarchicalAbsoluteSpectral.BaseMainOperatorCost
import HierarchicalAbsoluteSpectral.RuntimeFamilyOneLevel

/-! Uniform recurrence and its weighted unfolding for the literal
`mainFactorActionCost` used by the actual approximation program. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
variable {N m r : ℕ}

theorem PreparedFamilyProblem.safe_accuracy (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (j : ℕ) (hj : j ≤ P.depth) :
    safeAccuracy P.fixed j = familyScheduleValue (1/1024) (Real.sqrt (m/N : ℝ)/1024) j := by
  simp only [safeAccuracy,Nat.min_eq_left hj]
  exact P.normal_accuracy_scale I hL j hj

theorem PreparedFamilyProblem.factor_action_recurrence
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I)
    (hL : P.scalars.schedule.depth ≠ 0)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (S : StoredSketches N m N P.depth) (C : MainSupportData S)
    (D : ℝ) (hD : 1 ≤ D) (hm : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (b j : ℕ) (hj : j < P.depth) :
    (mainFactorActionCost kernels P.fixed S C b (j+1) : ℝ) ≤
      (2*familyActionCostConstant D*(Real.log (m : ℝ))^2)*
        (P.fixed.accuracy j/P.fixed.accuracy (j+1))*
        ((mainFactorActionCost kernels P.fixed S C b j : ℝ)+
          (mainFineActionCost kernels P.fixed S C j b : ℝ)+(C.pair.dimension : ℝ)*b+1) := by
  have hs := Real.sqrt_pos.mpr I.ratio_positive
  have hdepth := P.normal_depth I hL
  have hj' : j < P.scalars.schedule_scale.depth := by omega
  obtain ⟨hε,hh,hB,hbound⟩ := family_refinement_envelope_bound hs P.scalars.schedule_scale
    (by rw [← hdepth]; exact P.fixed.depth_positive) hD hm hscale j hj'
    (mainFactorActionCost kernels P.fixed S C b j) (mainFactorActionCost kernels P.fixed S C b j)
    (mainFineActionCost kernels P.fixed S C j b) C.pair.dimension b
  rw [mainFactorActionCost]
  simp only [P.safe_accuracy I hL j (by omega),P.safe_accuracy I hL (j+1) (by omega)]
  rw [P.normal_accuracy_scale I hL j (by omega),P.normal_accuracy_scale I hL (j+1) (by omega)]
  apply hbound.trans
  have hK : 0 ≤ familyActionCostConstant D := by linarith [familyActionCostConstant_ge_one D hD]
  have hH := familyScheduleValue_pos (1/1024) (Real.sqrt (m/N : ℝ)/1024)
    (by norm_num) (by positivity) j
  have hh' := familyScheduleValue_pos (1/1024) (Real.sqrt (m/N : ℝ)/1024)
    (by norm_num) (by positivity) (j+1)
  have hsum : (mainFactorActionCost kernels P.fixed S C b j : ℝ)+
      (mainFactorActionCost kernels P.fixed S C b j : ℝ)+(mainFineActionCost kernels P.fixed S C j b : ℝ)+
        (C.pair.dimension : ℝ)*b+1 ≤
      2*((mainFactorActionCost kernels P.fixed S C b j : ℝ)+
        (mainFineActionCost kernels P.fixed S C j b : ℝ)+(C.pair.dimension : ℝ)*b+1) := by
    have hJ : (0 : ℝ) ≤ mainFineActionCost kernels P.fixed S C j b := Nat.cast_nonneg _
    have hkb : (0 : ℝ) ≤ (C.pair.dimension : ℝ)*b := by positivity
    linarith
  have hh := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ familyActionCostConstant D*
      (familyScheduleValue (1/1024) (Real.sqrt (m/N : ℝ)/1024) j/
        familyScheduleValue (1/1024) (Real.sqrt (m/N : ℝ)/1024) (j+1))*(Real.log (m : ℝ))^2 by positivity)
  convert hh using 1 <;> ring

theorem PreparedFamilyProblem.factor_action_cost_unfold
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I)
    (hL : P.scalars.schedule.depth ≠ 0)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (S : StoredSketches N m N P.depth) (C : MainSupportData S)
    (D : ℝ) (hD : 1 ≤ D) (hm : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) (b : ℕ) :
    P.fixed.accuracy P.depth*(mainFactorActionCost kernels P.fixed S C b P.depth : ℝ) ≤
      (2*familyActionCostConstant D*(Real.log (m : ℝ))^2)^P.depth*
        (P.fixed.accuracy 0*((kernels C.pair.dimension C.pair.dimension b).cost : ℝ)+
          ∑ j ∈ Finset.range P.depth, P.fixed.accuracy j*
            ((mainFineActionCost kernels P.fixed S C j b : ℝ)+(C.pair.dimension : ℝ)*b+1)) := by
  let a := 2*familyActionCostConstant D*(Real.log (m : ℝ))^2
  let c := fun j => (mainFactorActionCost kernels P.fixed S C b j : ℝ)
  let leaf := fun j => (mainFineActionCost kernels P.fixed S C j b : ℝ)+(C.pair.dimension : ℝ)*b+1
  have hK := familyActionCostConstant_ge_one D hD
  have ha : 1 ≤ a := by dsimp [a]; nlinarith [sq_nonneg (Real.log (m : ℝ)-1)]
  have hpositive : ∀ j ≤ P.depth, 0 < P.fixed.accuracy j := P.fixed.accuracy_positive
  have hleaf : ∀ j < P.depth, 0 ≤ leaf j := by intro j hj; dsimp [leaf]; positivity
  have hstep : ∀ j < P.depth, c (j+1) ≤ a*(P.fixed.accuracy j/P.fixed.accuracy (j+1))*(c j+leaf j) := by
    intro j hj
    simpa only [a,c,leaf,add_assoc] using P.factor_action_recurrence I hL kernels S C D hD hm hscale b j hj
  have hu := family_cost_recurrence_unfold a P.fixed.accuracy c leaf P.depth ha hpositive hleaf hstep
  simpa only [a,c,leaf,mainFactorActionCost] using hu

theorem PreparedFamilyProblem.factor_action_overhead_bound
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I)
    (hL : P.scalars.schedule.depth ≠ 0)
    (D : ℝ) (hD : 1 ≤ D) (hm : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    (2*familyActionCostConstant D*(Real.log (m : ℝ))^2)^P.depth ≤
      Real.exp ((3+2*Real.log D)*(Real.log (2*familyActionCostConstant D)+2)*
        (1+Real.log (Real.log (2*(m : ℝ))))^2) := by
  have hs := Real.sqrt_pos.mpr I.ratio_positive
  have hK := familyActionCostConstant_ge_one D hD
  have hm0 : (0 : ℝ) < m := by exact_mod_cast I.core_positive
  have hlog := Real.log_le_log hm0 (by linarith : (m : ℝ) ≤ 2*m)
  have hlogm : 0 ≤ Real.log (m : ℝ) := by linarith
  have hlog2m : 0 ≤ Real.log (2*(m : ℝ)) := hlogm.trans hlog
  have hsq := (sq_le_sq₀ hlogm hlog2m).mpr hlog
  have hp := pow_le_pow_left₀
    (by positivity : 0 ≤ 2*familyActionCostConstant D*(Real.log (m : ℝ))^2)
    (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2*familyActionCostConstant D)) P.depth
  have hu := family_actual_overhead_bound hs P.scalars.schedule_scale hD
    (by linarith : 1 ≤ 2*familyActionCostConstant D) hm hm0 hscale
  rw [← P.normal_depth I hL] at hu
  exact hp.trans hu

end
end HierarchicalAbsoluteSpectral
