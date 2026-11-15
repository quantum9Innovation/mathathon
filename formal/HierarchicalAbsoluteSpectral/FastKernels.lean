import HierarchicalAbsoluteSpectral.ArithmeticKernel
import Matmul.RectangularPrograms

/-!
Unconditional fast matrix multiplication kernels in the hierarchy's arithmetic
model. Upstream integer circuits are compiled without changing any gate count.
These statements provide actual programs with every positive exponent slack.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matmul.RectangularPrograms

theorem matrixCircuitInput_eq_encode {n m p : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    matrixCircuitInput A B = Matmul.UniversalPaddedProgram.encode A B := by
  funext s
  cases s <;> rfl

/-- Actual square multiplication programs with the feasible exponent `9/4`.
The constant is uniform in the input size and every arithmetic gate is counted. -/
theorem exists_square_arithmetic_kernels (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ n : ℕ, ArithmeticKernel n n n) (C : ℝ), 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ((K n).cost : ℝ) ≤ C*(n:ℝ)^(9/4+ζ) := by
  obtain ⟨P,C,hC,hP,hcost⟩ := square_multiplication_programs (ε := ζ) hζ
  let K : ∀ n : ℕ, ArithmeticKernel n n n := fun n =>
    { circuit := P n
      correct := by
        intro A B i j
        rw [matrixCircuitInput_eq_encode]
        exact hP ℝ n A B i j }
  exact ⟨K,C,hC,hcost⟩

/-- Actual rectangular programs realizing the complete certified curve.
In particular the half-width endpoint gives exponent `2+ζ`. -/
theorem exists_rectangular_arithmetic_kernels (a ζ : ℝ) (ha : 0 ≤ a) (hζ : 0 < ζ) :
    ∃ (K : ∀ n : ℕ, ArithmeticKernel n (width a n) n) (C : ℝ), 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ((K n).cost : ℝ) ≤
        C*(n:ℝ)^(Matmul.RectangularOptimization.rectangularBound a+ζ) := by
  obtain ⟨P,C,hC,hP,hcost⟩ := rectangular_multiplication_programs (k := a) ha hζ
  let K : ∀ n : ℕ, ArithmeticKernel n (width a n) n := fun n =>
    { circuit := P n
      correct := by
        intro A B i j
        rw [matrixCircuitInput_eq_encode]
        exact hP ℝ n A B i j }
  exact ⟨K,C,hC,hcost⟩

theorem exists_half_rectangular_arithmetic_kernels (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ n : ℕ, ArithmeticKernel n (width (1/2) n) n) (C : ℝ), 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ((K n).cost : ℝ) ≤ C*(n:ℝ)^(2+ζ) := by
  simpa only [Matmul.RectangularOptimization.rectangularBound_half] using
    exists_rectangular_arithmetic_kernels (1/2) ζ (by norm_num) hζ

end
end HierarchicalAbsoluteSpectral
