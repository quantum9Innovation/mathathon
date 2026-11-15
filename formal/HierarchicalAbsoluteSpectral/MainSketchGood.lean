import HierarchicalAbsoluteSpectral.MainSketchData

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder

def SketchGramApprox {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ) (G : Core m) : Prop :=
  (1-ε) • (Aᵀ*A) ≤ G ∧ G ≤ (1+ε) • (Aᵀ*A)

def MainSketchGood {n m p r L : ℕ} (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) : Prop :=
  ∀ j : Fin (L+1), SketchGramApprox I.A (I.accuracy j.val) (S.leftGram j) ∧
    SketchGramApprox I.Bᵀ (I.accuracy j.val) (S.rightGram j)

end
end HierarchicalAbsoluteSpectral
