import HierarchicalAbsoluteSpectral.MainProblem

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix

structure StoredSketches (n m p L : ℕ) where
  levelA : Fin (L+1) → Σ s : ℕ, Matrix (Fin s) (Fin m) ℝ
  levelB : Fin (L+1) → Σ s : ℕ, Matrix (Fin s) (Fin m) ℝ
  rowsA : ∀ j, (levelA j).1 ≤ n
  rowsB : ∀ j, (levelB j).1 ≤ p

def StoredSketches.leftGram {n m p L : ℕ} (S : StoredSketches n m p L) (j : Fin (L+1)) : Core m :=
  (S.levelA j).2ᵀ*(S.levelA j).2

def StoredSketches.rightGram {n m p L : ℕ} (S : StoredSketches n m p L) (j : Fin (L+1)) : Core m :=
  (S.levelB j).2ᵀ*(S.levelB j).2

end
end HierarchicalAbsoluteSpectral
