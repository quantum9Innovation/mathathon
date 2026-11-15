import HierarchicalAbsoluteSpectral.MainSketchSingle

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

def mainLeftSketchInput (I : FixedProblem n m p r L) (g : MainRandomTape I) (j : Fin (L+1)) :
    SketchGaussianInput (dyadicPaddingLevel n) :=
  ((fun i => g (.sketchLeft j 0 i)),((fun i => g (.sketchLeft j 1 i)),(fun i => g (.sketchLeft j 2 i))))

def mainRightSketchInput (I : FixedProblem n m p r L) (g : MainRandomTape I) (j : Fin (L+1)) :
    SketchGaussianInput (dyadicPaddingLevel p) :=
  ((fun i => g (.sketchRight j 0 i)),((fun i => g (.sketchRight j 1 i)),(fun i => g (.sketchRight j 2 i))))

theorem mainSketchFailure_positive (I : FixedProblem n m p r L) : 0 < I.sketchFailure := by
  unfold FixedProblem.sketchFailure
  exact div_pos I.delta_positive (by positivity)

def mainSketchProgram (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    ArithmeticProgram (StoredSketches n m p L) := do
  let SA ← finiteTabulateProgram (fun j : Fin (L+1) => boundedSketchProgram I.A
    (I.accuracy j.val) I.sketchFailure (I.accuracy_positive j.val (by omega))
      (mainSketchFailure_positive I) (mainLeftSketchInput I g j))
  let SB ← finiteTabulateProgram (fun j : Fin (L+1) => boundedSketchProgram I.Bᵀ
    (I.accuracy j.val) I.sketchFailure (I.accuracy_positive j.val (by omega))
      (mainSketchFailure_positive I) (mainRightSketchInput I g j))
  ArithmeticProgram.pure
    { levelA := fun j => ⟨(SA j).rows,(SA j).value⟩
      levelB := fun j => ⟨(SB j).rows,(SB j).value⟩
      rowsA := fun j => (SA j).rows_le
      rowsB := fun j => (SB j).rows_le }

theorem mainSketchProgram_admissible (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (mainSketchProgram I g).admissible := by
  simp [mainSketchProgram,boundedSketchProgram_admissible]

def storedSketchesFromFactors (SA : Fin (L+1) → StoredSketchFactor n m)
    (SB : Fin (L+1) → StoredSketchFactor p m) : StoredSketches n m p L where
  levelA j := ⟨(SA j).rows,(SA j).value⟩
  levelB j := ⟨(SB j).rows,(SB j).value⟩
  rowsA j := (SA j).rows_le
  rowsB j := (SB j).rows_le

theorem mainSketchProgram_eval (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (mainSketchProgram I g).eval = storedSketchesFromFactors
      (fun j => (boundedSketchProgram I.A (I.accuracy j.val) I.sketchFailure
        (I.accuracy_positive j.val (by omega)) (mainSketchFailure_positive I) (mainLeftSketchInput I g j)).eval)
      (fun j => (boundedSketchProgram I.Bᵀ (I.accuracy j.val) I.sketchFailure
        (I.accuracy_positive j.val (by omega)) (mainSketchFailure_positive I) (mainRightSketchInput I g j)).eval) := by
  unfold mainSketchProgram
  rw [eval_bind,eval_bind,eval_pure]
  change storedSketchesFromFactors _ _ = _
  apply congrArg₂ storedSketchesFromFactors
  · exact finiteTabulateProgram_eval _
  · exact finiteTabulateProgram_eval _

theorem mainSketchProgram_leftGram (I : FixedProblem n m p r L) (g : MainRandomTape I) (j : Fin (L+1)) :
    (mainSketchProgram I g).eval.leftGram j =
      (boundedSketchProgram I.A (I.accuracy j.val) I.sketchFailure
        (I.accuracy_positive j.val (by omega)) (mainSketchFailure_positive I)
        (mainLeftSketchInput I g j)).eval.gram := by
  rw [mainSketchProgram_eval]
  rfl

theorem mainSketchProgram_rightGram (I : FixedProblem n m p r L) (g : MainRandomTape I) (j : Fin (L+1)) :
    (mainSketchProgram I g).eval.rightGram j =
      (boundedSketchProgram I.Bᵀ (I.accuracy j.val) I.sketchFailure
        (I.accuracy_positive j.val (by omega)) (mainSketchFailure_positive I)
        (mainRightSketchInput I g j)).eval.gram := by
  rw [mainSketchProgram_eval]
  rfl

end
end HierarchicalAbsoluteSpectral
