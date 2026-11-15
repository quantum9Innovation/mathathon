import HierarchicalAbsoluteSpectral.MainOperatorSpectral
import HierarchicalAbsoluteSpectral.BaseHierarchyContinuity
import HierarchicalAbsoluteSpectral.ThresholdAdaptiveRitz

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}
local instance queryViewMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance queryViewMatrixBorelInstance (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩

abbrev mainBaseAt (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : {t : ℝ // 0 < t}) : MainBaseData I S C t.val :=
  (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval

def mainThresholdView (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : {t : ℝ // 0 < t}) : {T : Core C.pair.dimension // T.IsHermitian} :=
  ⟨mainThresholdOperator I S C t.val (mainBaseAt kernels I S C t),
    mainThresholdOperator_isHermitian I S C t.val _⟩

def mainSourceView (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : {t : ℝ // 0 < t}) : Core C.pair.dimension :=
  mainSourceFactor I S C t.val (mainBaseAt kernels I S C t)

def mainFineMasses (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (j : ℕ) : Core C.pair.dimension :=
  constructedNeumannMass (mainFineGram S C (j+1)) (safeAccuracy I (j+1)/100)
    (by have := safeAccuracy_pos I (j+1); positivity)

theorem mainThresholdView_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) :
    Measurable (mainThresholdView kernels I S C) := by
  have hc := coarse_threshold_operator_continuous kernels C.rightGram C.rightGram_posSemidef
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))
    (mainFineMasses I S C) (fun j => mainFineRightGram S C (j+1)) (safeAccuracy I) L
    (constructedNeumannMass (mainTrueGram I S C) I.massAccuracy I.final_budget.mass_positive)
    (mainTrueRightGram I S C)
  have hFine (t : {t : ℝ // 0 < t}) :
      (fun i => t.val • mainFineMasses I S C i-mainFineRightGram S C (i+1)) =
        mainFinePencil I S C t.val := by rfl
  simp only [hFine] at hc
  have hm : Measurable (fun t : {t : ℝ // 0 < t} => (mainThresholdView kernels I S C t).val) := by
    simpa only [mainThresholdView,mainThresholdOperator,mainRefinedFactor,mainTruePencil,
      trueNeumannPencil,mainBaseAt,normalizedPencil] using hc.measurable
  exact hm.subtype_mk

theorem mainSourceView_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) :
    Measurable (mainSourceView kernels I S C) := by
  change Measurable (fun t : {t : ℝ // 0 < t} =>
    mainSourceFactor I S C t.val (mainBaseAt kernels I S C t))
  have hc := coarse_threshold_change_continuous kernels C.rightGram C.rightGram_posSemidef
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))
    (mainFineMasses I S C) (fun j => mainFineRightGram S C (j+1)) (safeAccuracy I) L
  have hFine (t : {t : ℝ // 0 < t}) :
      (fun i => t.val • mainFineMasses I S C i-mainFineRightGram S C (i+1)) =
        mainFinePencil I S C t.val := by rfl
  simp only [hFine] at hc
  simpa only [mainSourceView,mainSourceFactor_eq,mainRefinedFactor,mainBaseAt] using hc.measurable

def mainRitzAccuracy (I : FixedProblem n m p r L) : ℝ := I.alpha/100

theorem mainRitzAccuracy_positive (I : FixedProblem n m p r L) : 0 < mainRitzAccuracy I :=
  div_pos I.alpha_positive (by norm_num)

theorem mainRitzAccuracy_le_one (I : FixedProblem n m p r L) : mainRitzAccuracy I ≤ 1 := by
  have ha := I.final_budget.alpha_small
  change I.alpha ≤ _ at ha
  unfold mainRitzAccuracy
  linarith

def mainKrylovDegree (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : r < C.pair.dimension) : ℕ :=
  krylovDegree C.pair.dimension (mainConditionBound I) (1/2) (mainRitzAccuracy I)
    (by omega) (mainConditionBound_ge_one I) (by norm_num) (by norm_num)
    (mainRitzAccuracy_positive I) (mainRitzAccuracy_le_one I)

def mainIdealQuery (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ) :
    Fin I.queryCap → ℝ → ThresholdDecision :=
  idealRitzDecisions kernels (mainThresholdView kernels I S C) (mainSourceView kernels I S C)
    (mainKrylovDegree I S C hr) ⟨r,hr⟩ (mainRitzAccuracy I) samples

end
end HierarchicalAbsoluteSpectral
