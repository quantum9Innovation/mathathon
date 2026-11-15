import HierarchicalAbsoluteSpectral.ArithmeticKernel
import HierarchicalAbsoluteSpectral.FineProxy

/-! Instantiate mass and Gram action interfaces with stored factors and
verified multiplication kernels, including the executed Neumann-degree search. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {k b s : ℕ}

def neumannCountProgram (ε : ℝ) (hε : 0<ε) : ArithmeticProgram ℕ := do
  let s ← dyadicSearchProgram (1/2) ε (by norm_num) (by norm_num) hε
  ArithmeticProgram.pure (2^s)

@[simp] theorem neumannCountProgram_eval (ε : ℝ) (hε : 0<ε) :
    (neumannCountProgram ε hε).eval=neumannCount ε hε := by
  simp only [neumannCountProgram, eval_bind, eval_pure,
    (dyadicSearchProgram_specification (1/2) ε (by norm_num) (by norm_num) hε).1]
  rfl

theorem neumannCountProgram_work (ε : ℝ) (hε : 0<ε) :
    (neumannCountProgram ε hε).work=
      2*dyadicStoppingLevel (1/2) ε (by norm_num) (by norm_num) hε+1 := by
  simp only [neumannCountProgram, work_bind, work_pure, add_zero]
  exact (dyadicSearchProgram_specification _ _ _ _ _).2.1

theorem neumannCountProgram_admissible (ε : ℝ) (hε : 0<ε) :
    (neumannCountProgram ε hε).admissible := by
  simp only [neumannCountProgram, admissible_bind, admissible_pure, and_true]
  exact (dyadicSearchProgram_specification _ _ _ _ _).2.2

def MatrixAction.constructedNeumann {G : Core k} (P : MatrixAction G b)
    (ε : ℝ) (hε : 0<ε) : MatrixAction (constructedNeumannMass G ε hε) b where
  program V := do
    let q ← neumannCountProgram ε hε
    (P.neumann q).program V
  correct V := by simp only [eval_bind, neumannCountProgram_eval, MatrixAction.correct]; rfl
  valid V := by simp only [admissible_bind, MatrixAction.valid, and_true]; exact neumannCountProgram_admissible ε hε
  cost := 2*dyadicStoppingLevel (1/2) ε (by norm_num) (by norm_num) hε+1+
    2*neumannCount ε hε*(P.cost+2*k*b)
  work_le V := by
    simp only [work_bind, neumannCountProgram_work]
    rw [neumannCountProgram_eval]
    exact Nat.add_le_add_left ((P.neumann (neumannCount ε hε)).work_le V) _

def storedGramAction (F : Matrix (Fin s) (Fin k) ℝ)
    (K : ArithmeticKernel s k b) (KT : ArithmeticKernel k s b) : MatrixAction (Fᵀ*F) b :=
  (KT.action Fᵀ).comp (K.action F)

def storedNeumannPencilAction {G Q : Core k} (PG : MatrixAction G b) (PQ : MatrixAction Q b)
    (t ε : ℝ) (hε : 0<ε) : MatrixAction (trueNeumannPencil G Q t ε hε) b :=
  ((PG.constructedNeumann ε hε).scale t).sub PQ

end
end HierarchicalAbsoluteSpectral
