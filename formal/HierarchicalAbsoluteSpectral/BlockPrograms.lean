import HierarchicalAbsoluteSpectral.ArithmeticProgram

/-! Entrywise block operations with explicit arithmetic counts. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open ArithmeticProgram hiding pure
variable {k b : ℕ}

def blockScaleProgram (c : ℝ) (V : Matrix (Fin k) (Fin b) ℝ) :
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ) := do
  let rows ← tabulate k (fun i => tabulate b (fun j => mul c (Matrix.of.symm V i j)))
  ArithmeticProgram.pure (Matrix.of rows)

def blockAddProgram (U V : Matrix (Fin k) (Fin b) ℝ) :
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ) := do
  let rows ← tabulate k (fun i => tabulate b (fun j => add (Matrix.of.symm U i j) (Matrix.of.symm V i j)))
  ArithmeticProgram.pure (Matrix.of rows)

def blockSubProgram (U V : Matrix (Fin k) (Fin b) ℝ) :
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ) := do
  let rows ← tabulate k (fun i => tabulate b (fun j => sub (Matrix.of.symm U i j) (Matrix.of.symm V i j)))
  ArithmeticProgram.pure (Matrix.of rows)

@[simp] theorem blockScaleProgram_eval (c : ℝ) (V : Matrix (Fin k) (Fin b) ℝ) :
    (blockScaleProgram c V).eval = c • V := by
  funext i j
  simp [blockScaleProgram]

@[simp] theorem blockAddProgram_eval (U V : Matrix (Fin k) (Fin b) ℝ) :
    (blockAddProgram U V).eval = U+V := by
  funext i j
  simp [blockAddProgram]

@[simp] theorem blockSubProgram_eval (U V : Matrix (Fin k) (Fin b) ℝ) :
    (blockSubProgram U V).eval = U-V := by
  funext i j
  simp [blockSubProgram]

@[simp] theorem blockScaleProgram_work (c : ℝ) (V : Matrix (Fin k) (Fin b) ℝ) :
    (blockScaleProgram c V).work = k*b := by simp [blockScaleProgram]
@[simp] theorem blockAddProgram_work (U V : Matrix (Fin k) (Fin b) ℝ) :
    (blockAddProgram U V).work = k*b := by simp [blockAddProgram]
@[simp] theorem blockSubProgram_work (U V : Matrix (Fin k) (Fin b) ℝ) :
    (blockSubProgram U V).work = k*b := by simp [blockSubProgram]

@[simp] theorem blockScaleProgram_admissible (c : ℝ) (V : Matrix (Fin k) (Fin b) ℝ) :
    (blockScaleProgram c V).admissible := by simp [blockScaleProgram]
@[simp] theorem blockAddProgram_admissible (U V : Matrix (Fin k) (Fin b) ℝ) :
    (blockAddProgram U V).admissible := by simp [blockAddProgram]
@[simp] theorem blockSubProgram_admissible (U V : Matrix (Fin k) (Fin b) ℝ) :
    (blockSubProgram U V).admissible := by simp [blockSubProgram]

end
end HierarchicalAbsoluteSpectral
