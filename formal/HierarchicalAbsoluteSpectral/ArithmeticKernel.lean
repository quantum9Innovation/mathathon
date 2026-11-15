import HierarchicalAbsoluteSpectral.CircuitProgram
import HierarchicalAbsoluteSpectral.MatrixAction

/-!
Matrix multiplication kernels expressed as actual finite arithmetic circuits.
The correctness and cost of their exact-real execution are proved together.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matmul.UniversalProgram
open ArithmeticProgram hiding pure

abbrev MatrixCircuit (n m p : ℕ) :=
  Circuit ((Fin n × Fin m) ⊕ (Fin m × Fin p)) (Fin n × Fin p)

def matrixCircuitInput {n m p : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    ((Fin n × Fin m) ⊕ (Fin m × Fin p)) → ℝ :=
  Sum.elim (fun x => A x.1 x.2) (fun x => B x.1 x.2)

def matrixCircuitProgram {n m p : ℕ} (c : MatrixCircuit n m p)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    ArithmeticProgram (Matrix (Fin n) (Fin p) ℝ) := do
  let output ← circuitProgram c (matrixCircuitInput A B)
  ArithmeticProgram.pure (Matrix.of (fun i j => output (i,j)))

@[simp] theorem matrixCircuitProgram_eval {n m p : ℕ} (c : MatrixCircuit n m p)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (matrixCircuitProgram c A B).eval =
      Matrix.of (fun i j => c.eval (matrixCircuitInput A B) (i,j)) := by
  simp only [matrixCircuitProgram, eval_bind, eval_pure, circuitProgram_eval]

@[simp] theorem matrixCircuitProgram_work {n m p : ℕ} (c : MatrixCircuit n m p)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (matrixCircuitProgram c A B).work = c.cost := by
  simp only [matrixCircuitProgram, work_bind, work_pure, add_zero, circuitProgram_work]

@[simp] theorem matrixCircuitProgram_admissible {n m p : ℕ} (c : MatrixCircuit n m p)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (matrixCircuitProgram c A B).admissible := by
  simp only [matrixCircuitProgram, admissible_bind, admissible_pure, and_true]
  exact circuitProgram_admissible c _

structure ArithmeticKernel (n m p : ℕ) where
  circuit : MatrixCircuit n m p
  correct : ∀ (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (i : Fin n) (j : Fin p), circuit.eval (matrixCircuitInput A B) (i,j) = (A*B) i j

namespace ArithmeticKernel

variable {n m p : ℕ}

def cost (K : ArithmeticKernel n m p) : ℕ := K.circuit.cost

def program (K : ArithmeticKernel n m p) (A : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin p) ℝ) : ArithmeticProgram (Matrix (Fin n) (Fin p) ℝ) :=
  matrixCircuitProgram K.circuit A B

@[simp] theorem program_eval (K : ArithmeticKernel n m p)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (K.program A B).eval = A*B := by
  rw [program, matrixCircuitProgram_eval]
  ext i j
  exact K.correct A B i j

@[simp] theorem program_work (K : ArithmeticKernel n m p)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (K.program A B).work = K.cost := matrixCircuitProgram_work _ _ _

@[simp] theorem program_admissible (K : ArithmeticKernel n m p)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (K.program A B).admissible := matrixCircuitProgram_admissible _ _ _

def action (K : ArithmeticKernel n m p) (A : Matrix (Fin n) (Fin m) ℝ) :
    MatrixAction A p where
  program := K.program A
  correct := K.program_eval A
  valid := K.program_admissible A
  cost := K.cost
  work_le B := le_of_eq (K.program_work A B)

@[simp] theorem action_cost (K : ArithmeticKernel n m p)
    (A : Matrix (Fin n) (Fin m) ℝ) : (K.action A).cost = K.cost := rfl

end ArithmeticKernel
end
end HierarchicalAbsoluteSpectral
