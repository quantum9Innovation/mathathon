import HierarchicalAbsoluteSpectral.FiniteHierarchy

/-! Both directions of the recursively represented finite factor. Every
coefficient table, scalar root, scalar degree search and matrix action is charged. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open ArithmeticProgram hiding pure
variable {k b : ℕ}

def constructedRefinementTransposeAction {R Kj : Core k}
    (P : MatrixAction R b) (PT : MatrixAction Rᵀ b) (Q : MatrixAction Kj b)
    (hKj : Kjᵀ=Kj) (ε h B : ℝ) (hε : 0<ε) (hh : 0<h) (hB : 0≤B) :
    MatrixAction (finiteRefinementFactor R Kj ε h B)ᵀ b where
  program V := do
    let table ← refinementTableProgram ε h B hε hh hB
    (finiteFactorTransposeAction P PT Q hKj table.1 table.2.1 table.2.2).program V
  correct V := by
    simp only [eval_bind]
    rw [refinementTableProgram_eval]
    simp only [MatrixAction.correct]
    rw [preparedFactorMatrix_eq_refinement R Kj ε h B hε hh hB]
  valid V := by
    simp only [admissible_bind, MatrixAction.valid, and_true]
    exact refinementTableProgram_admissible ε h B hε hh hB
  cost :=
    let s := inverseRootLevel (8*ε) (refinementTolerance h B)
      (by positivity) (by unfold refinementTolerance; positivity)
    7+80*(s+3)*2^s+PT.cost+k*b+2^s*(P.cost+PT.cost+Q.cost+6*k*b)
  work_le V := by
    simp only [work_bind]
    have hT := refinementTableProgram_work ε h B hε hh hB
    have hA := (finiteFactorTransposeAction P PT Q hKj
      (refinementTableProgram ε h B hε hh hB).eval.1
      (refinementTableProgram ε h B hε hh hB).eval.2.1
      (refinementTableProgram ε h B hε hh hB).eval.2.2).work_le V
    convert Nat.add_le_add hT hA using 1
    simp only [finiteFactorTransposeAction_cost, refinementTableProgram_eval,
      automaticInverseRootProgram_eval]
    omega

structure FactorActions (R : Core k) (b : ℕ) where
  forward : MatrixAction R b
  transpose : MatrixAction Rᵀ b

def FactorActions.refine {R Kj : Core k} (P : FactorActions R b)
    (Q : MatrixAction Kj b) (hKj : Kjᵀ=Kj)
    (ε h B : ℝ) (hε : 0<ε) (hh : 0<h) (hB : 0≤B) :
    FactorActions (finiteRefinementFactor R Kj ε h B) b where
  forward := constructedRefinementAction P.forward P.transpose Q ε h B hε hh hB
  transpose := constructedRefinementTransposeAction P.forward P.transpose Q hKj ε h B hε hh hB

def hierarchicalFactorActions (R₀ : Core k) (Kfine : ℕ → Core k) (h : ℕ → ℝ)
    (L : ℕ) (hpos : ∀ j≤L, 0<h j)
    (hsym : ∀ j<L, (Kfine j)ᵀ=Kfine j)
    (base : FactorActions R₀ b) (fine : ∀ j, MatrixAction (Kfine j) b) :
    (j : ℕ) → j≤L → FactorActions (hierarchicalInverseFactor R₀ Kfine h j) b
  | 0,_ => base
  | j+1,hj =>
      (hierarchicalFactorActions R₀ Kfine h L hpos hsym base fine j (by omega)).refine
        (fine j) (hsym j (by omega)) (h (j+1)/h j) (h (j+1)) (hierarchyUpper j)
        (div_pos (hpos _ hj) (hpos _ (by omega))) (hpos _ hj) (hierarchyUpper_nonneg j)

def refinementActionEnvelope (P T J : ℕ) (ε h B : ℝ)
    (hε : 0<ε) (hh : 0<h) (hB : 0≤B) (k b : ℕ) : ℕ :=
  let s := inverseRootLevel (8*ε) (refinementTolerance h B)
    (by positivity) (by unfold refinementTolerance; positivity)
  7+80*(s+3)*2^s+max P T+k*b+2^s*(P+T+J+6*k*b)

theorem FactorActions.refine_cost {R Kj : Core k} (P : FactorActions R b)
    (Q : MatrixAction Kj b) (hKj : Kjᵀ=Kj)
    (ε h B : ℝ) (hε : 0<ε) (hh : 0<h) (hB : 0≤B) :
    max (P.refine Q hKj ε h B hε hh hB).forward.cost
      (P.refine Q hKj ε h B hε hh hB).transpose.cost≤
      refinementActionEnvelope P.forward.cost P.transpose.cost Q.cost ε h B hε hh hB k b := by
  dsimp only [FactorActions.refine, constructedRefinementAction, constructedRefinementTransposeAction,
    refinementActionEnvelope]
  exact max_le
    (by have := le_max_left P.forward.cost P.transpose.cost; omega)
    (by have := le_max_right P.forward.cost P.transpose.cost; omega)

end
end HierarchicalAbsoluteSpectral
