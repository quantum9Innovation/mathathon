import HierarchicalAbsoluteSpectral.BaseFixedLeafCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators
variable {n m p r L : ℕ}

def fixedSketchRowsA (I : FixedProblem n m p r L) (j : Fin (L+1)) : ℕ :=
  min n (embeddingComputedRowCount (2^dyadicPaddingLevel n) m (I.accuracy j.val) I.sketchFailure)

def fixedSketchRowsB (I : FixedProblem n m p r L) (j : Fin (L+1)) : ℕ :=
  min p (embeddingComputedRowCount (2^dyadicPaddingLevel p) m (I.accuracy j.val) I.sketchFailure)

theorem mainSketchProgram_rowsA_static (I : FixedProblem n m p r L) (g : MainRandomTape I) (j : Fin (L+1)) :
    ((mainSketchProgram I g).eval.levelA j).1=fixedSketchRowsA I j :=
  mainSketchProgram_rowsA I g j

theorem mainSketchProgram_rowsB_static (I : FixedProblem n m p r L) (g : MainRandomTape I) (j : Fin (L+1)) :
    ((mainSketchProgram I g).eval.levelB j).1=fixedSketchRowsB I j :=
  mainSketchProgram_rowsB I g j

def fixedFineProductCost (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (j b : ℕ) : ℕ :=
  matrixProductCost K (fixedSketchRowsA I (safeSketchIndex L (j+1))) m b+
    matrixProductCost K (fixedSketchRowsB I (safeSketchIndex L (j+1))) m b

def fixedCoarseProductCost (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) : ℕ :=
  matrixProductCost K m (fixedSketchRowsA I 0) m+matrixProductCost K m (fixedSketchRowsB I 0) m

theorem mainActualFineProductCost_static
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) (j b : ℕ) :
    mainFineProductCost K (mainSketchProgram I g).eval j b=fixedFineProductCost K I j b := by
  simp only [mainFineProductCost,fixedFineProductCost,mainSketchProgram_rowsA_static,mainSketchProgram_rowsB_static]

theorem mainFineProductCost_mono_width
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (S : StoredSketches n m p L) (j b B : ℕ) (hb : b ≤ B) :
    mainFineProductCost K S j b ≤ mainFineProductCost K S j B :=
  Nat.add_le_add (matrixProductCost_mono K le_rfl le_rfl hb)
    (matrixProductCost_mono K le_rfl le_rfl hb)

theorem mainInputProductCost_mono_width
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n m p b B : ℕ) (hb : b ≤ B) :
    mainInputProductCost K n m p b ≤ mainInputProductCost K n m p B :=
  Nat.add_le_add (matrixProductCost_mono K le_rfl le_rfl hb)
    (matrixProductCost_mono K le_rfl le_rfl hb)

end
end HierarchicalAbsoluteSpectral
