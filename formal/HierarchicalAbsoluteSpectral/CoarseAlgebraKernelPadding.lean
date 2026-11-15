import HierarchicalAbsoluteSpectral.CoarseAlgebraOuterKernels

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matmul.UniversalProgram Matmul.UniversalPaddedProgram Matmul.UniversalPaddedAlgorithm

def rectangularKernelPaddingCircuit {n m p N M P : ℕ}
    (en : Fin n ↪ Fin N) (em : Fin m ↪ Fin M) (ep : Fin p ↪ Fin P) :
    Circuit ((Fin n × Fin m) ⊕ (Fin m × Fin p))
      ((Fin N × Fin M) ⊕ (Fin M × Fin P)) :=
  .pair
    (partialWire (fun q => (sourceIndex en em q).map Sum.inl))
    (partialWire (fun q => (sourceIndex em ep q).map Sum.inr))

theorem rectangularKernelPaddingCircuit_eval {n m p N M P : ℕ}
    (en : Fin n ↪ Fin N) (em : Fin m ↪ Fin M) (ep : Fin p ↪ Fin P)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (rectangularKernelPaddingCircuit en em ep).eval (matrixCircuitInput A B) =
      matrixCircuitInput (pad en em A) (pad em ep B) := by
  funext s
  cases s with
  | inl q =>
      simp only [rectangularKernelPaddingCircuit, Circuit.eval_pair_inl, partialWire_eval]
      have hs := sourceIndex_pad en em A q
      cases h : sourceIndex en em q <;> simpa [h, matrixCircuitInput] using hs
  | inr q =>
      simp only [rectangularKernelPaddingCircuit, Circuit.eval_pair_inr, partialWire_eval]
      have hs := sourceIndex_pad em ep B q
      cases h : sourceIndex em ep q <;> simpa [h, matrixCircuitInput] using hs

def ArithmeticKernel.padShape {n m p N M P : ℕ} (K : ArithmeticKernel N M P)
    (en : Fin n ↪ Fin N) (em : Fin m ↪ Fin M) (ep : Fin p ↪ Fin P) :
    ArithmeticKernel n m p where
  circuit := .comp (rectangularKernelPaddingCircuit en em ep)
    (.comp K.circuit (.wire (fun q : Fin n × Fin p => (en q.1,ep q.2))))
  correct A B i j := by
    simp only [Circuit.eval_comp, Circuit.eval_wire, rectangularKernelPaddingCircuit_eval]
    rw [K.correct]
    exact congrArg (fun M : Matrix (Fin n) (Fin p) ℝ => M i j)
      (pad_product en em ep A B)

@[simp] theorem ArithmeticKernel.padShape_cost {n m p N M P : ℕ}
    (K : ArithmeticKernel N M P) (en : Fin n ↪ Fin N)
    (em : Fin m ↪ Fin M) (ep : Fin p ↪ Fin P) :
    (K.padShape en em ep).cost = K.cost := by
  simp [ArithmeticKernel.cost, ArithmeticKernel.padShape, rectangularKernelPaddingCircuit]

def ArithmeticKernel.restrictWidth {n m p P : ℕ} (K : ArithmeticKernel n m P)
    (hp : p ≤ P) : ArithmeticKernel n m p :=
  K.padShape (Function.Embedding.refl _) (Function.Embedding.refl _) (Fin.castLEEmb hp)

@[simp] theorem ArithmeticKernel.restrictWidth_cost {n m p P : ℕ}
    (K : ArithmeticKernel n m P) (hp : p ≤ P) :
    (K.restrictWidth hp).cost = K.cost := by
  simp [ArithmeticKernel.restrictWidth]

end
end HierarchicalAbsoluteSpectral
