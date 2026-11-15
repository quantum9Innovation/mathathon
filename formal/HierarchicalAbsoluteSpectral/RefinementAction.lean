import HierarchicalAbsoluteSpectral.MatrixAction
import HierarchicalAbsoluteSpectral.ConstructedRefinement
import HierarchicalAbsoluteSpectral.AutomaticPolynomial

/-! Operational components for the recursive refinement action. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure
open Matrix Polynomial
variable {k b : ℕ}

def refinementParameterProgram (ε h B : ℝ) : ArithmeticProgram (ℝ × ℝ × ℝ) := do
  let e ← add 1 ε
  let r ← sqrt e
  let c ← div 1 r
  let η ← mul 8 ε
  let u ← add 1 B
  let d ← mul 1000000 u
  let τ ← div h d
  ArithmeticProgram.pure (c,η,τ)

@[simp] theorem refinementParameterProgram_eval (ε h B : ℝ) :
    (refinementParameterProgram ε h B).eval =
      ((Real.sqrt (1+ε))⁻¹, 8*ε, refinementTolerance h B) := by
  norm_num [refinementParameterProgram, refinementTolerance]

@[simp] theorem refinementParameterProgram_work (ε h B : ℝ) :
    (refinementParameterProgram ε h B).work = 7 := by simp [refinementParameterProgram]

theorem refinementParameterProgram_admissible (ε h B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    (refinementParameterProgram ε h B).admissible := by
  have he : 0 < 1+ε := by positivity
  have hd : (1000000:ℝ)*(1+B) ≠ 0 := by positivity
  simp [refinementParameterProgram, he.le, (Real.sqrt_pos.mpr he).ne', hd]

def normalizedMatrixAction {R Kj : Core k} (P : MatrixAction R b)
    (PT : MatrixAction Rᵀ b) (Q : MatrixAction Kj b) : MatrixAction (Rᵀ*Kj*R) b :=
  (PT.comp (Q.comp P)).castMatrix (Matrix.mul_assoc _ _ _).symm

def scaledTransposeAction {R : Core k} (PT : MatrixAction Rᵀ b) (c : ℝ) :
    MatrixAction (c • R)ᵀ b :=
  (PT.scale c).castMatrix (by rw [Matrix.transpose_smul])

def finiteFactorMatrix (R Kj : Core k) (c : ℝ) (p : ℝ[X]) : Core k :=
  (c • R)*aeval ((c • R)ᵀ*Kj*(c • R)) p

def finiteFactorAction {R Kj : Core k} (P : MatrixAction R b) (PT : MatrixAction Rᵀ b)
    (Q : MatrixAction Kj b) (c : ℝ) (s : ℕ) (a : Fin (2^s) → ℝ) :
    MatrixAction (finiteFactorMatrix R Kj c (polynomialFromChebyshevCoefficients s a)) b :=
  (P.scale c).comp
    ((normalizedMatrixAction (P.scale c) (scaledTransposeAction PT c) Q).chebyshev s a)

theorem finiteFactorAction_cost {R Kj : Core k} (P : MatrixAction R b) (PT : MatrixAction Rᵀ b)
    (Q : MatrixAction Kj b) (c : ℝ) (s : ℕ) (a : Fin (2^s) → ℝ) :
    (finiteFactorAction P PT Q c s a).cost =
      P.cost+k*b+(2^s)*(P.cost+PT.cost+Q.cost+6*k*b) := by
  dsimp [finiteFactorAction, normalizedMatrixAction, scaledTransposeAction,
    MatrixAction.comp, MatrixAction.scale, MatrixAction.chebyshev, MatrixAction.castMatrix]
  ring

theorem polynomial_aeval_transpose (A : Core k) (hA : A.IsHermitian) (p : ℝ[X]) :
    (aeval A p)ᵀ = aeval A p := by
  have hs : IsSelfAdjoint (aeval A p) := by
    rw [← cfc_polynomial p A hA]
    exact cfc_predicate (p := IsSelfAdjoint) p.eval A
  change star (aeval A p) = aeval A p at hs
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hs

def finiteFactorTransposeAction {R Kj : Core k} (P : MatrixAction R b) (PT : MatrixAction Rᵀ b)
    (Q : MatrixAction Kj b) (hKj : Kjᵀ = Kj) (c : ℝ) (s : ℕ) (a : Fin (2^s) → ℝ) :
    MatrixAction (finiteFactorMatrix R Kj c (polynomialFromChebyshevCoefficients s a))ᵀ b :=
  (((normalizedMatrixAction (P.scale c) (scaledTransposeAction PT c) Q).chebyshev s a).comp
    (scaledTransposeAction PT c)).castMatrix (by
      rw [finiteFactorMatrix, Matrix.transpose_mul,
        polynomial_aeval_transpose _ (normalized_isHermitian (c • R) Kj hKj)])

theorem finiteFactorTransposeAction_cost {R Kj : Core k} (P : MatrixAction R b) (PT : MatrixAction Rᵀ b)
    (Q : MatrixAction Kj b) (hKj : Kjᵀ = Kj) (c : ℝ) (s : ℕ) (a : Fin (2^s) → ℝ) :
    (finiteFactorTransposeAction P PT Q hKj c s a).cost =
      PT.cost+k*b+(2^s)*(P.cost+PT.cost+Q.cost+6*k*b) := by
  dsimp [finiteFactorTransposeAction, normalizedMatrixAction, scaledTransposeAction,
    MatrixAction.comp, MatrixAction.scale, MatrixAction.chebyshev, MatrixAction.castMatrix]
  ring

theorem preparedFactorMatrix_eq_refinement (R Kj : Core k) (ε h B : ℝ)
    (hε : 0 < ε) (hh : 0 < h) (hB : 0 ≤ B) :
    let O := (automaticInverseRootProgram (8*ε) (refinementTolerance h B)
      (by positivity) (by unfold refinementTolerance; positivity)).eval
    finiteFactorMatrix R Kj (Real.sqrt (1+ε))⁻¹ (polynomialFromChebyshevCoefficients O.1 O.2) =
      finiteRefinementFactor R Kj ε h B := by
  dsimp only
  rw [automaticInverseRootProgram_polynomial]
  rfl

/-- Compute all scalar parameters and the coefficient table before applying
the factor. Positivity certificates are obtained from computed values. -/
def refinementTableProgram (ε h B : ℝ) (hε : 0 < ε) (hh : 0 < h) (hB : 0 ≤ B) :
    ArithmeticProgram (ℝ × (Σ s : ℕ, Fin (2^s) → ℝ)) := do
  let z ← (refinementParameterProgram ε h B).certify
  have hη : 0 < z.val.2.1 := by
    rw [z.property, refinementParameterProgram_eval]
    positivity
  have hτ : 0 < z.val.2.2 := by
    rw [z.property, refinementParameterProgram_eval]
    unfold refinementTolerance
    positivity
  let table ← automaticInverseRootProgram z.val.2.1 z.val.2.2 hη hτ
  ArithmeticProgram.pure (z.val.1,table)

theorem refinementTableProgram_eval (ε h B : ℝ) (hε : 0 < ε) (hh : 0 < h) (hB : 0 ≤ B) :
    (refinementTableProgram ε h B hε hh hB).eval =
      ((Real.sqrt (1+ε))⁻¹,
        (automaticInverseRootProgram (8*ε) (refinementTolerance h B)
          (by positivity) (by unfold refinementTolerance; positivity)).eval) := by
  simp only [refinementTableProgram, eval_bind, eval_pure, certify_eval,
    refinementParameterProgram_eval]

theorem refinementTableProgram_work (ε h B : ℝ) (hε : 0 < ε) (hh : 0 < h) (hB : 0 ≤ B) :
    (refinementTableProgram ε h B hε hh hB).work ≤
      let s := inverseRootLevel (8*ε) (refinementTolerance h B)
        (by positivity) (by unfold refinementTolerance; positivity)
      7+80*(s+3)*2^s := by
  dsimp only
  simp only [refinementTableProgram, work_bind, work_pure, add_zero, certify_work,
    refinementParameterProgram_work, certify_eval, refinementParameterProgram_eval]
  exact Nat.add_le_add_left (automaticInverseRootProgram_work_bound _ _ _ _) _

theorem refinementTableProgram_admissible (ε h B : ℝ) (hε : 0 < ε) (hh : 0 < h) (hB : 0 ≤ B) :
    (refinementTableProgram ε h B hε hh hB).admissible := by
  simp only [refinementTableProgram, admissible_bind, admissible_pure, and_true,
    certify_admissible, automaticInverseRootProgram_admissible, and_true]
  exact refinementParameterProgram_admissible ε h B hε hB

def constructedRefinementAction {R Kj : Core k} (P : MatrixAction R b) (PT : MatrixAction Rᵀ b)
    (Q : MatrixAction Kj b) (ε h B : ℝ) (hε : 0 < ε) (hh : 0 < h) (hB : 0 ≤ B) :
    MatrixAction (finiteRefinementFactor R Kj ε h B) b where
  program V := do
    let table ← refinementTableProgram ε h B hε hh hB
    (finiteFactorAction P PT Q table.1 table.2.1 table.2.2).program V
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
    7+80*(s+3)*2^s+P.cost+k*b+2^s*(P.cost+PT.cost+Q.cost+6*k*b)
  work_le V := by
    simp only [work_bind]
    have hT := refinementTableProgram_work ε h B hε hh hB
    have hA := (finiteFactorAction P PT Q
      (refinementTableProgram ε h B hε hh hB).eval.1
      (refinementTableProgram ε h B hε hh hB).eval.2.1
      (refinementTableProgram ε h B hε hh hB).eval.2.2).work_le V
    convert Nat.add_le_add hT hA using 1
    simp only [finiteFactorAction_cost, refinementTableProgram_eval,
      automaticInverseRootProgram_eval]
    omega

end
end HierarchicalAbsoluteSpectral
