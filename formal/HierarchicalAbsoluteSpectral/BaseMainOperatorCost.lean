import HierarchicalAbsoluteSpectral.MainStatementsCore

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
variable {n m p r L : ℕ}

def mainFineActionCost (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (j b : ℕ) : ℕ :=
  (mainFinePencilAction kernels I S C 0 j b).cost

@[simp] theorem mainFinePencilAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (j b : ℕ) : (mainFinePencilAction kernels I S C t j b).cost = mainFineActionCost kernels I S C j b := by
  rfl

def mainFactorActionCost (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) (b : ℕ) : ℕ → ℕ
  | 0 => (kernels C.pair.dimension C.pair.dimension b).cost
  | j+1 => refinementActionEnvelope
      (mainFactorActionCost kernels I S C b j) (mainFactorActionCost kernels I S C b j)
      (mainFineActionCost kernels I S C j b)
      (safeAccuracy I (j+1)/safeAccuracy I j) (safeAccuracy I (j+1)) (hierarchyUpper j)
      (div_pos (safeAccuracy_pos I (j+1)) (safeAccuracy_pos I j))
      (safeAccuracy_pos I (j+1)) (hierarchyUpper_nonneg j) C.pair.dimension b

theorem mainFactorActionCost_correct (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainFactorActions kernels I S C t base b).forward.cost = mainFactorActionCost kernels I S C b L ∧
      (mainFactorActions kernels I S C t base b).transpose.cost = mainFactorActionCost kernels I S C b L := by
  have hh (j : ℕ) (hj : j ≤ L) :
      let out := hierarchicalFactorActions base.inverseFactor (mainFinePencil I S C t) (safeAccuracy I) L
        (fun j _ => safeAccuracy_pos I j) (fun j _ => mainFinePencil_transpose I S C t j)
        { forward := (kernels _ _ b).action base.inverseFactor
          transpose := (kernels _ _ b).action base.inverseFactorᵀ }
        (fun j => mainFinePencilAction kernels I S C t j b) j hj
      out.forward.cost = mainFactorActionCost kernels I S C b j ∧
      out.transpose.cost = mainFactorActionCost kernels I S C b j := by
    induction j with
    | zero =>
      rw [hierarchicalFactorActions,mainFactorActionCost]
      exact ⟨rfl,rfl⟩
    | succ j ih =>
      have hj' : j ≤ L := by omega
      have hi := ih hj'
      rw [hierarchicalFactorActions,mainFactorActionCost]
      simp only [FactorActions.refine,constructedRefinementAction,constructedRefinementTransposeAction,
        refinementActionEnvelope,hi.1,hi.2,mainFinePencilAction_cost,max_self]
      constructor <;> trivial
  exact hh L le_rfl

def mainTrueActionCost (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) (b : ℕ) : ℕ :=
  (mainTruePencilAction kernels I S C 0 b).cost

@[simp] theorem mainTruePencilAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (b : ℕ) : (mainTruePencilAction kernels I S C t b).cost = mainTrueActionCost kernels I S C b := rfl

def mainThresholdActionCost (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) (b : ℕ) : ℕ :=
  2*mainFactorActionCost kernels I S C b L+mainTrueActionCost kernels I S C b+C.pair.dimension*b

@[simp] theorem mainThresholdAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainThresholdAction kernels I S C t base b).cost = mainThresholdActionCost kernels I S C b := by
  change 0+((mainFactorActions kernels I S C t base b).transpose.cost+
    ((mainTruePencilAction kernels I S C t b).cost+
      (mainFactorActions kernels I S C t base b).forward.cost))+C.pair.dimension*b = _
  rw [(mainFactorActionCost_correct kernels I S C t base b).1,
    (mainFactorActionCost_correct kernels I S C t base b).2,mainTruePencilAction_cost]
  dsimp [mainThresholdActionCost]
  omega

theorem mainSourceAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainSourceAction kernels I S C t base b).cost = mainFactorActionCost kernels I S C b L+
      (kernels C.pair.dimension C.pair.dimension b).cost := by
  change (mainFactorActions kernels I S C t base b).transpose.cost+
    (kernels C.pair.dimension C.pair.dimension b).cost = _
  rw [(mainFactorActionCost_correct kernels I S C t base b).2]

def mainCarriedActionCost (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) (b : ℕ) : ℕ :=
  2*(kernels C.pair.dimension C.pair.dimension b).cost+
    2*mainFactorActionCost kernels I S C b L+mainTrueActionCost kernels I S C b+C.pair.dimension*b

theorem mainCarriedAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainCarriedAction kernels I S C t base b).cost = mainCarriedActionCost kernels I S C b := by
  change 0+(((((kernels C.pair.dimension C.pair.dimension b).cost+
    (mainTruePencilAction kernels I S C t b).cost)+
    (mainFactorActions kernels I S C t base b).forward.cost)+
    (mainFactorActions kernels I S C t base b).transpose.cost)+
    (kernels C.pair.dimension C.pair.dimension b).cost)+C.pair.dimension*b = _
  rw [(mainFactorActionCost_correct kernels I S C t base b).1,
    (mainFactorActionCost_correct kernels I S C t base b).2,mainTruePencilAction_cost]
  dsimp [mainCarriedActionCost]
  omega

theorem mainSupportAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) (b : ℕ) :
    (mainSupportAction kernels I S C b).cost =
      (kernels n m b).cost+(kernels m C.pair.dimension b).cost := rfl

theorem mainPhysicalMapAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainPhysicalMapAction kernels I S C t base b).cost =
      (kernels n m b).cost+(kernels m C.pair.dimension b).cost+
        (kernels C.pair.dimension C.pair.dimension b).cost := rfl

@[simp] theorem mainConditionProgram_work (I : FixedProblem n m p r L) :
    (mainConditionProgram I).work = 7 := by
  simp [mainConditionProgram,ArithmeticProgram.work_bind,ArithmeticProgram.work]

end
end HierarchicalAbsoluteSpectral
