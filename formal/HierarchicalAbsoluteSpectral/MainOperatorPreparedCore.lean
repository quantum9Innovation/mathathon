import HierarchicalAbsoluteSpectral.MainOperatorPrepared
import HierarchicalAbsoluteSpectral.MainStatementsCore

/-! Query and output actions built from the prepared recursive factors. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

def mainPreparedSourceAction (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    MatrixAction (mainSourceFactor I S C t base)ᵀ b :=
  ((mainPreparedFactorActions kernels I P S C t base b).transpose.comp
    ((kernels _ _ b).action base.metricFactor.upperᵀ)).castMatrix (by
      simp only [mainSourceFactor, Matrix.transpose_mul])

theorem mainPreparedSourceAction_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    mainPreparedSourceAction kernels I P S C t base b =
      mainSourceAction kernels I S C t base b := by
  simp only [mainPreparedSourceAction, mainSourceAction, mainPreparedFactorActions_eq]

@[simp] theorem mainPreparedSourceAction_program
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainPreparedSourceAction kernels I P S C t base b).program =
      (mainSourceAction kernels I S C t base b).program := by
  rw [mainPreparedSourceAction_eq]

@[simp] theorem mainPreparedSourceAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainPreparedSourceAction kernels I P S C t base b).cost =
      (mainSourceAction kernels I S C t base b).cost := by
  rw [mainPreparedSourceAction_eq]

def mainPreparedCarriedAction (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    MatrixAction (mainCarriedMatrix I S C t base) b :=
  let p₀ := (kernels _ _ b).action base.inverseFactorᵀ
  let p₁ := p₀.comp (mainPreparedTruePencilAction kernels I P S C t b)
  let p₂ := p₁.comp (mainPreparedFactorActions kernels I P S C t base b).forward
  let p₃ := p₂.comp (mainPreparedFactorActions kernels I P S C t base b).transpose
  (MatrixAction.identity _ b).sub (p₃.comp ((kernels _ _ b).action base.metricFactor.upperᵀ))

theorem mainPreparedCarriedAction_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    mainPreparedCarriedAction kernels I P S C t base b =
      mainCarriedAction kernels I S C t base b := by
  simp only [mainPreparedCarriedAction, mainCarriedAction,
    mainPreparedTruePencilAction_eq, mainPreparedFactorActions_eq]

@[simp] theorem mainPreparedCarriedAction_program
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainPreparedCarriedAction kernels I P S C t base b).program =
      (mainCarriedAction kernels I S C t base b).program := by
  rw [mainPreparedCarriedAction_eq]

@[simp] theorem mainPreparedCarriedAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainPreparedCarriedAction kernels I P S C t base b).cost =
      (mainCarriedAction kernels I S C t base b).cost := by
  rw [mainPreparedCarriedAction_eq]

def mainPreparedPhysicalMapAction (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (_P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    MatrixAction (supportLeftFactor I.A S.initialA C.pair*base.metricFactor.upperᵀ) b :=
  (mainSupportAction kernels I S C b).comp ((kernels _ _ b).action base.metricFactor.upperᵀ)

theorem mainPreparedPhysicalMapAction_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    mainPreparedPhysicalMapAction kernels I P S C t base b =
      mainPhysicalMapAction kernels I S C t base b := rfl

@[simp] theorem mainPreparedPhysicalMapAction_program
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainPreparedPhysicalMapAction kernels I P S C t base b).program =
      (mainPhysicalMapAction kernels I S C t base b).program := rfl

@[simp] theorem mainPreparedPhysicalMapAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainPreparedPhysicalMapAction kernels I P S C t base b).cost =
      (mainPhysicalMapAction kernels I S C t base b).cost := rfl

end
end HierarchicalAbsoluteSpectral
