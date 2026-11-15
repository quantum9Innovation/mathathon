import HierarchicalAbsoluteSpectral.BaseFixedActionBudget
import HierarchicalAbsoluteSpectral.BaseFixedCoreAlgebraCostMain
import HierarchicalAbsoluteSpectral.BaseFixedQueryAggregationRange
import HierarchicalAbsoluteSpectral.MainSketchCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
variable {n m p r L : ℕ}

def fixedPaperFineSum (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (b : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L, I.accuracy j*(fixedFineProductCost K I j b:ℝ)

theorem mainActualFineSum_static (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) (b : ℕ) :
    fixedFineProductSum K I (mainSketchProgram I g).eval b=fixedPaperFineSum K I b := by
  apply Finset.sum_congr rfl
  intro j _
  rw [mainActualFineProductCost_static]

def fixedPaperFineCoefficient (I : FixedProblem n m p r L) : ℝ :=
  84*fixedOuterAccuracyConstant I*fixedFineLog I*(fixedRefinementCostMultiplier I)^L

def fixedPaperInputCoefficient (I : FixedProblem n m p r L) : ℝ :=
  (40*fixedTrueNeumannLog I+2)*fixedOuterAccuracyConstant I

def fixedPaperActionBudget (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) : ℝ :=
  fixedPaperFineCoefficient I*(fixedPaperFineSum K I (r+1)/Real.sqrt (I.accuracy L*I.theta))+
    fixedPaperInputCoefficient I*
      (Real.sqrt (I.accuracy L/I.theta)*(mainInputProductCost K n m p (r+1):ℝ))

theorem mainActualActionBudget_static (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    fixedActionWorkBudget K I (mainSketchProgram I g).eval (r+1)=fixedPaperActionBudget K I := by
  unfold fixedActionWorkBudget fixedFactorOuterEnvelope fixedInputOuterEnvelope
  rw [mainActualFineSum_static]
  unfold fixedPaperActionBudget fixedPaperFineCoefficient fixedPaperInputCoefficient
  ring

def fixedPaperCoreBudget (Ck exponent : ℝ) (I : FixedProblem n m p r L) : ℝ :=
  300*(Ck+1)*(m:ℝ)^exponent*baseFixedInitialLog I+fixedQueryRangeBudget I Ck exponent

def fixedPaperWidePenalty (I : FixedProblem n m p r L) : ℝ :=
  if fixedKrylovRawWidth I ≤ m then 0 else (m:ℝ)*(fixedKrylovRawWidth I:ℝ)^2

/-- The terms in the fixed-depth tradeoff, with an all-outcome width cap.
The fine sum starts at j=0 and uses the sketch accuracy h_(j+1). -/
def fixedPaperMainTerm (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (exponent : ℝ) (I : FixedProblem n m p r L) : ℝ :=
  (m*(n+p):ℕ)+(fixedCoarseProductCost K I:ℝ)+(m:ℝ)^exponent+
    Real.sqrt (I.accuracy L/I.theta)*(mainInputProductCost K n m p (r+1):ℝ)+
    fixedPaperFineSum K I (r+1)/Real.sqrt (I.accuracy L*I.theta)+
    (n*p:ℕ)+(matrixProductCost K n r p:ℝ)+fixedPaperWidePenalty I

def fixedSketchLogFactor (I : FixedProblem n m p r L) : ℕ :=
  (L+1)*(128*(dyadicPaddingLevel n+dyadicPaddingLevel p+2)+
    6*embeddingMomentOrder m I.sketchFailure+40)

theorem mainSketchProgram_work_input_log_bound (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (mainSketchProgram I g).work ≤ fixedSketchLogFactor I*(m*(n+p)) := by
  have hm : 1 ≤ m := I.rank_positive.trans I.rank_le_core
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < m) I.core_le_rows
  have hp : 0 < p := lt_of_lt_of_le (by omega : 0 < m) I.core_le_cols
  have hA := sketchFormationCap_input_bound n m I.sketchFailure hn hm
  have hB := sketchFormationCap_input_bound p m I.sketchFailure hp hm
  let D := dyadicPaddingLevel n+dyadicPaddingLevel p+2
  let V := 6*embeddingMomentOrder m I.sketchFailure+40
  have hdA : dyadicPaddingLevel n+1 ≤ D := by dsimp [D]; omega
  have hdB : dyadicPaddingLevel p+1 ≤ D := by dsimp [D]; omega
  have hsA := Nat.mul_le_mul_left (128*m*n) hdA
  have hsB := Nat.mul_le_mul_left (128*m*p) hdB
  have hinput : 1 ≤ m*(n+p) := by have hh:=Nat.mul_pos (by omega : 0 < m) (by omega : 0 < n+p); omega
  have hv := Nat.mul_le_mul_left V hinput
  have hs : sketchFormationCap n m I.sketchFailure+sketchFormationCap p m I.sketchFailure ≤
      (128*D+V)*(m*(n+p)) := by dsimp [V] at hv ⊢; nlinarith
  have hs' := Nat.mul_le_mul_left (L+1) hs
  apply (mainSketchProgram_work_le I g).trans
  simpa only [fixedSketchLogFactor,D,V,Nat.mul_assoc,Nat.add_assoc] using hs'

def fixedPaperPreparationCoefficient (Ck : ℝ) (I : FixedProblem n m p r L) : ℝ :=
  1+(fixedSketchLogFactor I:ℝ)+6*(L+1:ℕ)+
    (2+4*(I.queryCap:ℝ)*I.repetitions)+(4*(L:ℝ)+3*I.queryCap+2*I.repetitions+29)+11*(Ck+1)

def fixedPaperWorkCoefficient (Ck : ℝ) (I : FixedProblem n m p r L) : ℝ :=
  fixedPaperFineCoefficient I+fixedPaperInputCoefficient I+311*(Ck+1)*baseFixedInitialLog I+23

/-- Every dependence hidden by the manuscript's fixed-depth tilde is
displayed here. It contains no factor entries, singular values or threshold. -/
def fixedPaperPrefactor (Ck : ℝ) (I : FixedProblem n m p r L) : ℝ :=
  fixedPaperPreparationCoefficient Ck I+
    11000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*fixedPaperWorkCoefficient Ck I

theorem mainActualCoarseGramCost_le_static
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    baseFixedCoarseGramCost K m ((mainSketchProgram I g).eval.levelA 0).1
      ((mainSketchProgram I g).eval.levelB 0).1 ≤ (fixedCoarseProductCost K I:ℝ) := by
  rw [mainSketchProgram_rowsA_static,mainSketchProgram_rowsB_static]
  have hA := kernel_cost_le_matrixProductCost K m (fixedSketchRowsA I 0) m
    m (fixedSketchRowsA I 0) m le_rfl le_rfl le_rfl
  have hB := kernel_cost_le_matrixProductCost K m (fixedSketchRowsB I 0) m
    m (fixedSketchRowsB I 0) m le_rfl le_rfl le_rfl
  unfold baseFixedCoarseGramCost fixedCoarseProductCost
  push_cast
  exact_mod_cast Nat.add_le_add hA hB

end
end HierarchicalAbsoluteSpectral
