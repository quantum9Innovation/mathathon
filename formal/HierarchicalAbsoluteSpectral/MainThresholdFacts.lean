import HierarchicalAbsoluteSpectral.MainInitializerCorrectnessBase
import HierarchicalAbsoluteSpectral.MainOperatorSpectral
import HierarchicalAbsoluteSpectral.ThresholdNearBudget
import HierarchicalAbsoluteSpectral.MassSpectrumSupport

/-! The actual threshold constructor uses the same canonical mass target as
the initializer.  These deterministic facts connect safe query answers, the
near-threshold hierarchy transfer, and the physical singular-value tail. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {n m p r L : ℕ}

theorem mainThresholdOperator_eq_massThresholdOperator
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (base : MainBaseData I S C t) :
    mainThresholdOperator I S C t base =
      massThresholdOperator (mainTrueRightGram I S C)
        (mainRefinedFactor I S C t base) (massInverseFactor (mainInitializerMass I S C)) t := by
  rw [massThresholdOperator, massInverseFactor_metric _ (mainInitializerMass_posDef I S C)]
  rfl

theorem MainSketchGood.actual_threshold_below_iff
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (t : ℝ) (ht : 0 < t) :
    let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t ht
      (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
    1 < orderedEigenvalue (mainThresholdOperator I S C t base)
        (mainThresholdOperator_isHermitian I S C t base) ⟨r,hr⟩ ↔
      t < mainInitializerMassTarget I S C hr := by
  dsimp only
  have hf := hg.actual_hierarchy kernels I S C t ht
  have hh := massThresholdOperator_below_iff (mainTrueRightGram I S C)
    _ (massInverseFactor (mainInitializerMass I S C))
    (mainTrueRightGram_posSemidef I S C).isHermitian hf.isUnit
    (massInverseFactor_isUnit _ (mainInitializerMass_posDef I S C)) t ⟨r,hr⟩
  simpa only [← mainThresholdOperator_eq_massThresholdOperator,
    mainInitializerMassTarget, massEigenvalue] using hh

theorem MainSketchGood.actual_threshold_above_iff
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (t : ℝ) (ht : 0 < t) :
    let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t ht
      (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
    orderedEigenvalue (mainThresholdOperator I S C t base)
        (mainThresholdOperator_isHermitian I S C t base) ⟨r,hr⟩ < 1 ↔
      mainInitializerMassTarget I S C hr < t := by
  dsimp only
  have hf := hg.actual_hierarchy kernels I S C t ht
  have hh := massThresholdOperator_above_iff (mainTrueRightGram I S C)
    _ (massInverseFactor (mainInitializerMass I S C))
    (mainTrueRightGram_posSemidef I S C).isHermitian hf.isUnit
    (massInverseFactor_isUnit _ (mainInitializerMass_posDef I S C)) t ⟨r,hr⟩
  simpa only [← mainThresholdOperator_eq_massThresholdOperator,
    mainInitializerMassTarget, massEigenvalue] using hh

theorem MainSketchGood.actual_threshold_le_one_iff
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (t : ℝ) (ht : 0 < t) :
    let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t ht
      (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
    orderedEigenvalue (mainThresholdOperator I S C t base)
        (mainThresholdOperator_isHermitian I S C t base) ⟨r,hr⟩ ≤ 1 ↔
      mainInitializerMassTarget I S C hr ≤ t := by
  simpa only [not_lt] using
    (not_congr (hg.actual_threshold_below_iff kernels I S C hr t ht))

theorem MainSketchGood.actual_threshold_safe_decision
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (t : ℝ) (ht : 0 < t)
    (ε : ℝ) (d : ThresholdDecision)
    (hsafe : let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t ht
      (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
      ThresholdDecisionSafe (orderedEigenvalue (mainThresholdOperator I S C t base)
        (mainThresholdOperator_isHermitian I S C t base) ⟨r,hr⟩) ε d) :
    let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t ht
      (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
    match d with
    | .below => t ≤ mainInitializerMassTarget I S C hr
    | .above => mainInitializerMassTarget I S C hr ≤ t
    | .near => |1-orderedEigenvalue (mainThresholdOperator I S C t base)
        (mainThresholdOperator_isHermitian I S C t base) ⟨r,hr⟩| ≤ 2*ε := by
  cases d with
  | below => exact ((hg.actual_threshold_below_iff kernels I S C hr t ht).mp hsafe).le
  | above => exact ((hg.actual_threshold_above_iff kernels I S C hr t ht).mp hsafe).le
  | near => exact hsafe

theorem MainSketchGood.actual_threshold_D_bound
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (t : ℝ) (ht : 0 ≤ t) :
    t • (1 : Core C.pair.dimension)+C.rightGram ≤
      (2 : ℝ) • (t • mainInitializerMass I S C+mainTrueRightGram I S C) := by
  have hId : (1 : Core C.pair.dimension) ≤ (2 : ℝ) • mainInitializerMass I S C := by
    have hh := smul_le_smul_of_nonneg_left (hg.initializer_mass_bands I S C).1
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [smul_smul, show (2 : ℝ)*(1/2)=1 by norm_num, one_smul] using hh
  have hh := add_le_add (smul_le_smul_of_nonneg_left hId ht)
    (hg.right_gram_comparison I S C).2
  convert hh using 1
  module

theorem MainSketchGood.actual_threshold_near_upper
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (t : ℝ) (ht : 0 < t)
    (hnear : let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t ht
      (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
      |1-orderedEigenvalue (mainThresholdOperator I S C t base)
        (mainThresholdOperator_isHermitian I S C t base) ⟨r,hr⟩| ≤ I.alpha) :
    t ≤ ((1+I.nearTolerance)/(1-I.nearTolerance))*mainInitializerMassTarget I S C hr := by
  let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t ht
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
  let R := mainRefinedFactor I S C t base
  let Rb := massInverseFactor (mainInitializerMass I S C)
  have hmetric : inverseMetric Rb = mainInitializerMass I S C :=
    massInverseFactor_metric _ (mainInitializerMass_posDef I S C)
  have hQ := mainTrueRightGram_posSemidef I S C
  have hf := hg.actual_hierarchy kernels I S C t ht
  have hnear' : |1-orderedEigenvalue
      (massThresholdOperator (mainTrueRightGram I S C) R Rb t)
      (massThresholdOperator_isHermitian _ _ _ hQ.isHermitian t) ⟨r,hr⟩| ≤ I.alpha := by
    simpa only [R, Rb, base, ← mainThresholdOperator_eq_massThresholdOperator] using hnear
  have hn := massThresholdOperator_near (mainTrueRightGram I S C) R Rb
    hQ.isHermitian t I.alpha ⟨r,hr⟩ hnear'
  have hdom : -(inverseMetric R) ≤ t • inverseMetric Rb-mainTrueRightGram I S C := by
    rw [hmetric]
    exact hf.lower_pencil
  have hinvariant : inverseMetric R-hierarchyRelaxation L •
      ((t • inverseMetric Rb-mainTrueRightGram I S C)*(inverseMetric R)⁻¹*
        (t • inverseMetric Rb-mainTrueRightGram I S C)) ≤
      (hierarchyConstant L*I.accuracy L) • (t • (1 : Core C.pair.dimension)+C.rightGram) := by
    rw [hmetric]
    exact hf.defect
  have hD : t • (1 : Core C.pair.dimension)+C.rightGram ≤
      (2 : ℝ) • (t • inverseMetric Rb+mainTrueRightGram I S C) := by
    rw [hmetric]
    exact hg.actual_threshold_D_bound I S C t ht.le
  have hκ : 1 ≤ hierarchyRelaxation L := by cases L <;> norm_num [hierarchyRelaxation]
  have hθ1 : I.theta ≤ 1 :=
    I.theta_le_last.trans ((I.accuracy_bounded L le_rfl).trans (by norm_num))
  exact near_threshold_literal_upper (mainTrueRightGram I S C)
    (t • (1 : Core C.pair.dimension)+C.rightGram) R Rb hQ hf.isUnit
    (massInverseFactor_isUnit _ (mainInitializerMass_posDef I S C))
    t (hierarchyRelaxation L) (hierarchyConstant L) (I.accuracy L) I.theta ht.le
    hκ (hierarchyRelaxation_bounds L).2 (hierarchyConstant_ge_one L)
    (I.accuracy_positive L le_rfl) I.theta_positive I.theta_le_last hθ1
    hdom hinvariant hD ⟨r,hr⟩ hn

theorem MainSketchGood.initializer_mass_tail_comparison
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) :
    (tailSingularValue (I.A*I.B) r)^2/(1+I.massAccuracy) ≤
        mainInitializerMassTarget I S C hr ∧
      mainInitializerMassTarget I S C hr ≤
        (tailSingularValue (I.A*I.B) r)^2/(1-I.massAccuracy) := by
  let Z := supportLeftFactor I.A S.initialA C.pair
  let Bcal := supportRightFactor S.initialA C.pair I.B
  have hb := hg.gram_bands I S C
  have hG : (mainTrueGram I S C).PosDef := posDef_of_half_identity_le _ hb.1
  have hm := constructedNeumannMass_relative (mainTrueGram I S C) hG I.massAccuracy
    I.final_budget.mass_positive hb.1 hb.2
  have hG' : (Zᵀ*Z).PosDef := by rw [← mainTrueGram_eq]; exact hG
  have hlo : (1-I.massAccuracy) • (Zᵀ*Z)⁻¹ ≤ mainInitializerMass I S C := by
    rw [← mainTrueGram_eq]
    exact hm.1
  have hup : mainInitializerMass I S C ≤ (1+I.massAccuracy) • (Zᵀ*Z)⁻¹ := by
    rw [← mainTrueGram_eq]
    exact hm.2
  have hθ1 : I.theta ≤ 1 :=
    I.theta_le_last.trans ((I.accuracy_bounded L le_rfl).trans (by norm_num))
  have hε1 : I.massAccuracy < 1 := by
    have hh := I.final_budget.mass_error
    change I.massAccuracy ≤ I.theta/1000 at hh
    linarith
  have hrp : r < p := hr.trans_le ((mainSupport_dimension_le S C).trans I.core_le_cols)
  have hh := support_approximate_mass_compare Z Bcal (mainInitializerMass I S C)
    hG' (mainInitializerMass_posDef I S C) I.massAccuracy I.final_budget.mass_positive.le
    hε1 hlo hup ⟨r,hr⟩ hrp
  simpa only [Z, Bcal, ← hg.support_exact I S C, ← mainTrueRightGram_eq,
    mainInitializerMassTarget] using hh

theorem MainSketchGood.actual_threshold_near_tail
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (t : ℝ) (ht : 0 < t)
    (hnear : let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t ht
      (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
      |1-orderedEigenvalue (mainThresholdOperator I S C t base)
        (mainThresholdOperator_isHermitian I S C t base) ⟨r,hr⟩| ≤ I.alpha) :
    t ≤ ((1+I.nearTolerance)/(1-I.nearTolerance))*(1/(1-I.massAccuracy))*
      (tailSingularValue (I.A*I.B) r)^2 := by
  have hθ1 : I.theta ≤ 1 :=
    I.theta_le_last.trans ((I.accuracy_bounded L le_rfl).trans (by norm_num))
  have hratio : 0 ≤ (1+I.nearTolerance)/(1-I.nearTolerance) :=
    div_nonneg (by linarith [I.nearTolerance_positive])
      (I.final_budget.denominators hθ1).2.1.le
  have hh := (hg.actual_threshold_near_upper kernels I S C hr t ht hnear).trans
    (mul_le_mul_of_nonneg_left (hg.initializer_mass_tail_comparison I S C hr).2 hratio)
  calc
    t ≤ ((1+I.nearTolerance)/(1-I.nearTolerance))*
        ((tailSingularValue (I.A*I.B) r)^2/(1-I.massAccuracy)) := hh
    _ = ((1+I.nearTolerance)/(1-I.nearTolerance))*(1/(1-I.massAccuracy))*
        (tailSingularValue (I.A*I.B) r)^2 := by ring

end
end HierarchicalAbsoluteSpectral
