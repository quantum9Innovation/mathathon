import HierarchicalAbsoluteSpectral.MainOperatorCorrectness
import HierarchicalAbsoluteSpectral.MainStatementsCore
import HierarchicalAbsoluteSpectral.CarriedCondition

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

theorem MainSketchGood.actual_base_hierarchy (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (t : ℝ) (ht : 0 < t) :
    HierarchyInvariant (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t ht
      (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval.inverseFactor
      (mainTruePencil I S C t) (t • (1 : Core C.pair.dimension)+C.rightGram) 0 (I.accuracy 0) := by
  have hG := hg.normalized_gram_bounds I S C
  have hQ := hg.coarse_right_bounds I S C
  exact base_hierarchy_invariant kernels (mainTrueGram I S C) (mainTrueRightGram I S C)
    C.rightGram (mainTrueRightGram_posSemidef I S C) C.rightGram_posSemidef
    (I.accuracy 0) I.massAccuracy t (I.accuracy_positive 0 (by omega)) I.initial_accuracy_le
    I.final_budget.mass_positive (I.massAccuracy_le_level 0 (by omega)) ht hG.1 hG.2 hQ.1 hQ.2

theorem HierarchyInvariant.threshold_operator_bounds {k j : ℕ} {R K D : Core k} {h : ℝ}
    (H : HierarchyInvariant R K D j h) :
    (1-normalizedPencil R K).PosSemidef ∧ 1-normalizedPencil R K ≤ (2 : ℝ) • (1 : Core k) := by
  have hu : normalizedPencil R K ≤ 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      inverseMetric_normalized R H.isUnit,normalizedPencil] using
      star_left_conjugate_le_conjugate H.upper_pencil R
  have hl : -(1 : Core k) ≤ normalizedPencil R K := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.mul_neg,Matrix.neg_mul,inverseMetric_normalized R H.isUnit,normalizedPencil] using
      star_left_conjugate_le_conjugate H.lower_pencil R
  refine ⟨(sub_nonneg.mpr hu).posSemidef,?_⟩
  have hh := sub_le_sub_left hl (1 : Core k)
  convert hh using 1 <;> module

theorem MainSketchGood.actual_threshold_bounds (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (t : ℝ) (ht : 0 < t) :
    let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t ht
      (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
    (mainThresholdOperator I S C t base).PosSemidef ∧
      mainThresholdOperator I S C t base ≤ (2 : ℝ) • (1 : Core C.pair.dimension) :=
  (hg.actual_hierarchy kernels I S C t ht).threshold_operator_bounds

theorem MainSketchGood.actual_source_condition (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (t : ℝ) (ht : 0 < t) :
    let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t ht
      (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
    let Sinv := (mainRefinedFactor I S C t base)⁻¹*base.inverseFactor
    let a := (1+hierarchyUpper L/(8*I.accuracy 0))⁻¹
    let b := 1+hierarchyUpper 0/(8*I.accuracy L)
    Sinv*mainSourceFactor I S C t base=1 ∧ 0<a ∧ ‖Sinv‖≤1/a ∧
      ‖mainSourceFactor I S C t base‖ ≤ b ∧ b/a ≤ mainConditionBound I ∧ 1 ≤ mainConditionBound I := by
  dsimp only
  let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t ht
      (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
  have hb := hg.actual_base_hierarchy kernels I S C t ht
  have hf := hg.actual_hierarchy kernels I S C t ht
  have hc := carried_factor_condition base.inverseFactor (mainRefinedFactor I S C t base)
    (t • (1 : Core C.pair.dimension)+C.rightGram) (hierarchyUpper 0) (hierarchyUpper L)
    (I.accuracy 0) (I.accuracy L) hb.isUnit hf.isUnit (hierarchyUpper_nonneg 0)
    (hierarchyUpper_nonneg L) (I.accuracy_positive 0 (by omega)) (I.accuracy_positive L le_rfl)
    hb.floor hb.upper hf.floor hf.upper
  simpa only [mainSourceFactor_eq,mainConditionBound] using hc

end
end HierarchicalAbsoluteSpectral
