import HierarchicalAbsoluteSpectral.ChebyshevAction
import HierarchicalAbsoluteSpectral.NeumannAction

/-!
Compositional interfaces for actual matrix-action programs. A witness
contains executable arithmetic syntax, its equality to the stated matrix
product, its admissibility and its proved operation bound. These interfaces
are intermediate compiler lemmas, not assumptions of the main result.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

structure MatrixAction {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : ℕ) where
  program : Matrix (Fin m) (Fin b) ℝ → ArithmeticProgram (Matrix (Fin n) (Fin b) ℝ)
  correct : ∀ V, (program V).eval = A*V
  valid : ∀ V, (program V).admissible
  cost : ℕ
  work_le : ∀ V, (program V).work ≤ cost

namespace MatrixAction

variable {n m l b : ℕ}

def identity (n b : ℕ) : MatrixAction (1 : Core n) b where
  program V := .pure V
  correct V := by simp
  valid V := trivial
  cost := 0
  work_le V := le_refl _

def comp {A : Matrix (Fin n) (Fin m) ℝ} {B : Matrix (Fin m) (Fin l) ℝ}
    (P : MatrixAction A b) (Q : MatrixAction B b) : MatrixAction (A*B) b where
  program V := do
    let U ← Q.program V
    P.program U
  correct V := by simp only [eval_bind, P.correct, Q.correct, Matrix.mul_assoc]
  valid V := by simp only [admissible_bind, P.valid, Q.valid, and_self]
  cost := P.cost+Q.cost
  work_le V := by
    simp only [work_bind]
    have hP := P.work_le (Q.program V).eval
    have hQ := Q.work_le V
    omega

def scale {A : Matrix (Fin n) (Fin m) ℝ} (P : MatrixAction A b) (c : ℝ) : MatrixAction (c • A) b where
  program V := do
    let U ← P.program V
    blockScaleProgram c U
  correct V := by simp only [eval_bind, P.correct, blockScaleProgram_eval, Matrix.smul_mul]
  valid V := by simp only [admissible_bind, P.valid, blockScaleProgram_admissible, and_self]
  cost := P.cost+n*b
  work_le V := by
    simp only [work_bind, blockScaleProgram_work]
    exact Nat.add_le_add_right (P.work_le V) _

def add {A B : Matrix (Fin n) (Fin m) ℝ} (P : MatrixAction A b) (Q : MatrixAction B b) :
    MatrixAction (A+B) b where
  program V := do
    let U ← P.program V
    let W ← Q.program V
    blockAddProgram U W
  correct V := by simp only [eval_bind, P.correct, Q.correct, blockAddProgram_eval, Matrix.add_mul]
  valid V := by simp only [admissible_bind, P.valid, Q.valid, blockAddProgram_admissible, and_self]
  cost := P.cost+Q.cost+n*b
  work_le V := by
    simp only [work_bind, blockAddProgram_work]
    have hP := P.work_le V
    have hQ := Q.work_le V
    omega

def sub {A B : Matrix (Fin n) (Fin m) ℝ} (P : MatrixAction A b) (Q : MatrixAction B b) :
    MatrixAction (A-B) b where
  program V := do
    let U ← P.program V
    let W ← Q.program V
    blockSubProgram U W
  correct V := by simp only [eval_bind, P.correct, Q.correct, blockSubProgram_eval, Matrix.sub_mul]
  valid V := by simp only [admissible_bind, P.valid, Q.valid, blockSubProgram_admissible, and_self]
  cost := P.cost+Q.cost+n*b
  work_le V := by
    simp only [work_bind, blockSubProgram_work]
    have hP := P.work_le V
    have hQ := Q.work_le V
    omega

def neumann {G : Core n} (P : MatrixAction G b) (q : ℕ) : MatrixAction (evenNeumannMass G q) b where
  program V := neumannActionProgram P.program (2*q) V
  correct V := (evenNeumannAction_specification P.program G P.cost q P.correct P.work_le P.valid V).2.1
  valid V := neumannActionProgram_admissible P.program P.valid _ V
  cost := (2*q)*(P.cost+2*n*b)
  work_le V := neumannActionProgram_work P.program P.cost P.work_le _ V

def chebyshev {A : Core n} (P : MatrixAction A b) (s : ℕ) (a : Fin (2^s) → ℝ) :
    MatrixAction (Polynomial.aeval A (polynomialFromChebyshevCoefficients s a)) b where
  program V := chebyshevActionProgram P.program (integerCoefficient (2^s) a) (2^s) V
  correct V := (chebyshevTableAction_specification P.program A P.cost s P.correct P.work_le P.valid a V).2.1
  valid V := chebyshevActionProgram_admissible P.program P.valid _ _ V
  cost := (2^s)*(P.cost+4*n*b)
  work_le V := chebyshevActionProgram_work P.program P.cost P.work_le _ _ V

/-- Relabel a proved program by an equality of its represented matrix. -/
def castMatrix {A B : Matrix (Fin n) (Fin m) ℝ} (P : MatrixAction A b) (h : A = B) : MatrixAction B b where
  program := P.program
  correct V := by rw [← h]; exact P.correct V
  valid := P.valid
  cost := P.cost
  work_le := P.work_le

end MatrixAction
end
end HierarchicalAbsoluteSpectral
