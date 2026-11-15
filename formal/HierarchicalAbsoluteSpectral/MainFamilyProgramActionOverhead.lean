import HierarchicalAbsoluteSpectral.MainFamilyProgramActionUniform

/-! The normalized factor-action overhead used by the final core-cost
assembly, with every dependence on the computed depth exposed. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {N m r : ℕ}

def familyFactorActionOverhead (I : FamilyProblem N m r) (P : PreparedFamilyProblem I)
    (D c : ℝ) : ℝ :=
  (2*familyActionCostConstant D*(Real.log (m : ℝ))^2)^P.depth*
    ((P.depth+1 : ℕ) : ℝ)*familyActionLeafCoefficient D c*(Real.log (m : ℝ))^4

def familyFactorLoglogConstant (D : ℝ) : ℝ :=
  (3+2*Real.log D)*(Real.log (2*familyActionCostConstant D)+2)

theorem familyActionWorkScale_eq (I : FamilyProblem N m r) (P : PreparedFamilyProblem I)
    (D c χ : ℝ) :
    familyActionWorkScale I P D c χ = familyFactorActionOverhead I P D c*χ*(N : ℝ)*(m : ℝ) := by
  unfold familyActionWorkScale familyFactorActionOverhead
  ring

theorem familyFactorActionOverhead_ge_one (I : FamilyProblem N m r) (P : PreparedFamilyProblem I)
    (D c : ℝ) (hD : 1 ≤ D) (hc : 0 ≤ c) (hmLog : 1 ≤ Real.log (m : ℝ)) :
    1 ≤ familyFactorActionOverhead I P D c := by
  have hK := familyActionCostConstant_ge_one D hD
  have hE := familyRowCoefficient_ge_one D c (by linarith) hc
  have hf : 0 ≤ familyFineLeafCoefficient D c := by unfold familyFineLeafCoefficient; positivity
  have hB : 1 ≤ familyActionLeafCoefficient D c := by unfold familyActionLeafCoefficient; linarith
  have ha : 1 ≤ 2*familyActionCostConstant D*(Real.log (m : ℝ))^2 := by
    nlinarith [sq_nonneg (Real.log (m : ℝ)-1)]
  have hp : 1 ≤ (2*familyActionCostConstant D*(Real.log (m : ℝ))^2)^P.depth := one_le_pow₀ ha
  have hdepth : (1 : ℝ) ≤ ((P.depth+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ P.depth+1 by omega)
  have hell : 1 ≤ (Real.log (m : ℝ))^4 := one_le_pow₀ hmLog
  have mul1 : ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → 1 ≤ x*y := by
    intro x y hx hy
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  exact mul1 _ _ (mul1 _ _ (mul1 _ _ hp hdepth) hB) hell

theorem PreparedFamilyProblem.factor_action_normalized_bound
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (D c : ℝ) (hD : 1 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) (g : MainRandomTape P.fixed)
    (C : MainSupportData (mainSketchProgram P.fixed g).eval) (b : ℕ) (hb : b ≤ r+1) :
    (mainFactorActionCost kernels P.fixed (mainSketchProgram P.fixed g).eval C b P.depth : ℝ) ≤
      familyFactorActionOverhead I P D c*χ*(N : ℝ)*(m : ℝ) := by
  rw [← familyActionWorkScale_eq]
  exact P.factor_action_uniform_bound I hL kernels χ hχ hrow D c hD hc hm hmLog hscale hδ g C b hb

theorem PreparedFamilyProblem.factor_action_overhead_polylog
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D c : ℝ) (hD : 1 ≤ D) (hc : 0 ≤ c) (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    familyFactorActionOverhead I P D c ≤
      ((2*D+1)*familyActionLeafCoefficient D c)*(Real.log (m : ℝ))^5*
        Real.exp (familyFactorLoglogConstant D*(1+Real.log (Real.log (2*(m : ℝ))))^2) := by
  have hs := Real.sqrt_pos.mpr I.ratio_positive
  have hdepth := familySchedule_depth_log_linear hs P.scalars.schedule_scale
    (by rw [familyScalarSchedule_scale_depth]; exact Nat.pos_of_ne_zero hL) hscale
  rw [← P.normal_depth I hL] at hdepth
  have hhalf := mul_le_mul_of_nonneg_left family_log_two_lower (Nat.cast_nonneg P.depth)
  have hcount : ((P.depth+1 : ℕ) : ℝ) ≤ (2*D+1)*Real.log (m : ℝ) := by
    push_cast
    nlinarith
  have hK := familyActionCostConstant_ge_one D hD
  have hE := familyRowCoefficient_ge_one D c (by linarith) hc
  have hf : 0 ≤ familyFineLeafCoefficient D c := by unfold familyFineLeafCoefficient; positivity
  have hB : 0 ≤ familyActionLeafCoefficient D c := by unfold familyActionLeafCoefficient; positivity
  have ha : 0 ≤ 2*familyActionCostConstant D*(Real.log (m : ℝ))^2 := by positivity
  have hmult := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount (pow_nonneg ha P.depth)) hB)
      (show 0 ≤ (Real.log (m : ℝ))^4 by positivity)
  have hover := P.factor_action_overhead_bound I hL D hD hmLog hscale
  calc
    _ ≤ (2*familyActionCostConstant D*(Real.log (m : ℝ))^2)^P.depth*
        ((2*D+1)*Real.log (m : ℝ))*familyActionLeafCoefficient D c*(Real.log (m : ℝ))^4 := hmult
    _ = ((2*D+1)*familyActionLeafCoefficient D c)*(Real.log (m : ℝ))^5*
        (2*familyActionCostConstant D*(Real.log (m : ℝ))^2)^P.depth := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hover (by positivity)

end
end HierarchicalAbsoluteSpectral
