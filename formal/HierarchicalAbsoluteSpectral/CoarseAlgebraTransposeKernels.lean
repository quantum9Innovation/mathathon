import HierarchicalAbsoluteSpectral.CoarseAlgebraGrowingKernels

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matmul.UniversalProgram Matrix

def transposeKernelInputCircuit (n m p : ℕ) :
    Circuit ((Fin n × Fin m) ⊕ (Fin m × Fin p))
      ((Fin p × Fin m) ⊕ (Fin m × Fin n)) :=
  .pair (.wire (fun q => Sum.inr (q.2,q.1)))
    (.wire (fun q => Sum.inl (q.2,q.1)))

theorem transposeKernelInputCircuit_eval {n m p : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (transposeKernelInputCircuit n m p).eval (matrixCircuitInput A B) =
      matrixCircuitInput Bᵀ Aᵀ := by
  funext q
  cases q <;> rfl

def ArithmeticKernel.transpose {n m p : ℕ} (K : ArithmeticKernel p m n) :
    ArithmeticKernel n m p where
  circuit := .comp (transposeKernelInputCircuit n m p)
    (.comp K.circuit (.wire (fun q : Fin n × Fin p => (q.2,q.1))))
  correct A B i j := by
    simp only [Circuit.eval_comp,Circuit.eval_wire,transposeKernelInputCircuit_eval,K.correct]
    rw [← Matrix.transpose_mul]
    rfl

@[simp] theorem ArithmeticKernel.transpose_cost {n m p : ℕ} (K : ArithmeticKernel p m n) :
    K.transpose.cost = K.cost := by
  simp [ArithmeticKernel.cost,ArithmeticKernel.transpose,transposeKernelInputCircuit]

end
end HierarchicalAbsoluteSpectral
