import HierarchicalAbsoluteSpectral.FastKernels

/-! Zero padding provides counted kernels for arbitrary rectangular sizes. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matmul.UniversalProgram Matmul.UniversalPaddedProgram Matmul.UniversalPaddedAlgorithm

def kernelPaddingCircuit {n m p N : ℕ}
    (en : Fin n ↪ Fin N) (em : Fin m ↪ Fin N) (ep : Fin p ↪ Fin N) :
    Circuit ((Fin n × Fin m) ⊕ (Fin m × Fin p))
      ((Fin N × Fin N) ⊕ (Fin N × Fin N)) :=
  .pair
    (partialWire (fun q => (sourceIndex en em q).map Sum.inl))
    (partialWire (fun q => (sourceIndex em ep q).map Sum.inr))

theorem kernelPaddingCircuit_eval {n m p N : ℕ}
    (en : Fin n ↪ Fin N) (em : Fin m ↪ Fin N) (ep : Fin p ↪ Fin N)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (kernelPaddingCircuit en em ep).eval (matrixCircuitInput A B) =
      matrixCircuitInput (pad en em A) (pad em ep B) := by
  funext s
  cases s with
  | inl q =>
      simp only [kernelPaddingCircuit, Circuit.eval_pair_inl, partialWire_eval]
      have hs := sourceIndex_pad en em A q
      cases h : sourceIndex en em q <;> simpa [h, matrixCircuitInput] using hs
  | inr q =>
      simp only [kernelPaddingCircuit, Circuit.eval_pair_inr, partialWire_eval]
      have hs := sourceIndex_pad em ep B q
      cases h : sourceIndex em ep q <;> simpa [h, matrixCircuitInput] using hs

def ArithmeticKernel.pad {n m p N : ℕ} (K : ArithmeticKernel N N N)
    (en : Fin n ↪ Fin N) (em : Fin m ↪ Fin N) (ep : Fin p ↪ Fin N) :
    ArithmeticKernel n m p where
  circuit := .comp (kernelPaddingCircuit en em ep)
    (.comp K.circuit (.wire (fun q : Fin n × Fin p => (en q.1,ep q.2))))
  correct A B i j := by
    simp only [Circuit.eval_comp, Circuit.eval_wire, kernelPaddingCircuit_eval]
    rw [K.correct]
    exact congrArg (fun M : Matrix (Fin n) (Fin p) ℝ => M i j)
      (pad_product en em ep A B)

@[simp] theorem ArithmeticKernel.pad_cost {n m p N : ℕ} (K : ArithmeticKernel N N N)
    (en : Fin n ↪ Fin N) (em : Fin m ↪ Fin N) (ep : Fin p ↪ Fin N) :
    (K.pad en em ep).cost = K.cost := by
  simp [ArithmeticKernel.cost, ArithmeticKernel.pad, kernelPaddingCircuit]

theorem exists_padded_arithmetic_kernels (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ n m p : ℕ, ArithmeticKernel n m p) (C : ℝ), 0 < C ∧
      ∀ n m p : ℕ, 1 ≤ max n (max m p) →
        ((K n m p).cost : ℝ) ≤ C*(max n (max m p):ℝ)^(9/4+ζ) := by
  obtain ⟨S,C,hC,hS⟩ := exists_square_arithmetic_kernels ζ hζ
  let K := fun n m p => (S (max n (max m p))).pad
    (Fin.castLEEmb (le_max_left _ _))
    (Fin.castLEEmb ((le_max_left _ _).trans (le_max_right _ _)))
    (Fin.castLEEmb ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨K,C,hC,?_⟩
  intro n m p h
  simpa only [K, ArithmeticKernel.pad_cost, Nat.cast_max] using hS (max n (max m p)) h

end
end HierarchicalAbsoluteSpectral
