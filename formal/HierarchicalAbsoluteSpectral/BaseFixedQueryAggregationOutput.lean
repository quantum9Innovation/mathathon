import HierarchicalAbsoluteSpectral.BaseFixedQueryAggregationConcrete
import HierarchicalAbsoluteSpectral.BaseFixedOutputCostPaper

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
variable {n m p r L : ℕ}

def fixedQueryOutputBudget (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (Ck exponent : ℝ) : ℝ :=
  10*(fixedActionWorkBudget K I S (r+1)+fixedQueryCoreBudget I Ck exponent)+
    (matrixProductCost K n r p:ℝ)

/-- All numerical premises of the generic core aggregation are discharged
by the literal hierarchy, deflation and physical-output programs. -/
theorem fixedFlexibleCoreWorkCap_concrete_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hRowsA : ∀ j<L, m ≤ (S.levelA (safeSketchIndex L (j+1))).1)
    (hRowsB : ∀ j<L, m ≤ (S.levelB (safeSketchIndex L (j+1))).1) :
    (mainCoreWorkCapWithQuery K I S C (fun hr => mainFlexibleQueryWorkCap K
      (rangeDeflationWorkCap K) I S C hr Ck exponent):ℝ) ≤
      11000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*
        (fixedActionWorkBudget K I S (r+1)+fixedQueryCoreBudget I Ck exponent+
          (matrixProductCost K n r p:ℝ)) := by
  let E := fixedOuterDegreeEnvelope I
  let A := fixedActionWorkBudget K I S (r+1)
  let B := fixedQueryCoreBudget I Ck exponent
  let O := fixedQueryOutputBudget K I S Ck exponent
  have h := fixedFlexibleQueryEnvelope_concrete K Ck exponent hC hexponent hK I S C hRowsA hRowsB
  have hA : 1 ≤ A := h.action_positive K _ I S C Ck exponent E A B
  have hB : 1 ≤ B := h.core_positive
  have hO : 0 ≤ O := by dsimp only [O,fixedQueryOutputBudget]; positivity
  have hexact : (mainExactOutputWorkCap K I S C:ℝ) ≤ O := by
    dsimp only [O,fixedQueryOutputBudget]
    simpa only [fixedOutputCoreCost,fixedOutputBaseLog,fixedQueryCoreBudget,baseFixedInitialLog,mul_assoc]
      using mainExactOutputWorkCap_paper_callback K Ck exponent hC hexponent hK I S C hRowsA hRowsB
  have hstrong (hk : 1 ≤ C.pair.dimension) : (mainStrongWorkCap K I S C hk:ℝ) ≤ 100*(A+B+O) := by
    dsimp only [A,B,O,fixedQueryOutputBudget]
    simpa only [fixedOutputCoreCost,fixedOutputBaseLog,fixedQueryCoreBudget,baseFixedInitialLog,mul_assoc]
      using mainStrongWorkCap_paper_callback K Ck exponent hC hexponent hK I S C hk hRowsA hRowsB
  have hc := fixedFlexibleCoreWorkCap_bound K (rangeDeflationWorkCap K) I S C Ck exponent E A B O h hO
    (fixedQueryCoreBudget_psd_bound K Ck exponent hC hexponent hK I S C)
    (fixedQueryCoreBudget_dimension_bound K Ck exponent hC hexponent hK I S C) hexact hstrong
  have hOsmall : A+B+O ≤ 11*(A+B+(matrixProductCost K n r p:ℝ)) := by
    dsimp only [O,fixedQueryOutputBudget]
    have hM := Nat.cast_nonneg (α:=ℝ) (matrixProductCost K n r p)
    dsimp only [A,B]
    linarith
  calc
    _ ≤ 1000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*(A+B+O) := hc
    _ ≤ 1000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*
        (11*(A+B+(matrixProductCost K n r p:ℝ))) :=
      mul_le_mul_of_nonneg_left hOsmall (by positivity)
    _ = _ := by dsimp only [A,B]; ring

/-- The concrete core bound applies on every Gaussian tape, including
deflation, zero products and exact initializer branches. -/
theorem fixedFlexibleCoreProgram_concrete_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (K a b c).cost ≤ 2*a*b*c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hRowsA : ∀ j<L, m ≤ (S.levelA (safeSketchIndex L (j+1))).1)
    (hRowsB : ∀ j<L, m ≤ (S.levelB (safeSketchIndex L (j+1))).1)
    (g : MainRandomTape I) :
    ((mainCoreProgram K I S C g).work:ℝ) ≤
      11000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*
        (fixedActionWorkBudget K I S (r+1)+fixedQueryCoreBudget I Ck exponent+
          (matrixProductCost K n r p:ℝ)) := by
  have hw := mainCoreProgram_work_bound_of_query K I S C g
    (fun hr => mainFlexibleQueryWorkCap K (rangeDeflationWorkCap K) I S C hr Ck exponent)
    (fun hr number t => mainPositiveQueryProgram_work_bound_flexible K (rangeDeflationWorkCap K)
      (rangeDeflationWorkCap_correct K hClassical) Ck exponent hC hexponent hK I S C hr t
      (mainQueryArray I S C g number) (mainInertiaArray I S C g number))
  exact (Nat.cast_le.mpr hw).trans
    (fixedFlexibleCoreWorkCap_concrete_bound K Ck exponent hC hexponent hK I S C hRowsA hRowsB)

end
end HierarchicalAbsoluteSpectral
