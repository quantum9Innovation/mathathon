import HierarchicalAbsoluteSpectral.CoarseAlgebraScaleneKernels
import HierarchicalAbsoluteSpectral.CoarseAlgebraScaleneScheme
import HierarchicalAbsoluteSpectral.CoarseAlgebraScaleneCharacter
import HierarchicalAbsoluteSpectral.CoarseAlgebraScaleneOptimization
import HierarchicalAbsoluteSpectral.CoarseAlgebraKernelPadding

/-!
Unconditional strict arithmetic kernels for three independent dimensions.
The weighted integral-character bound is converted by spectral duality to
an exact integer tensor decomposition, then compiled at a common padded
recursion depth. The resulting programs share all intermediate results and
execute their integer coefficients using counted additions and negations.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matmul.RectangularPrograms Matmul.UniversalPaddedProgram

theorem actual_scalene_character_objective_le (φ : Matmul.IntegralCharacter)
    {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    u*φ.pY+v*φ.pZ+w*φ.pX ≤ scaleneBound u v w :=
  scalene_objective_le (ScaleneCharacter.actual_weighted_quadratic_cap φ)
    φ.pX_nonneg φ.pY_nonneg φ.pZ_nonneg hu hv hw

theorem exists_scalene_scheme_certificate {u v w ζ : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hζ : 0 < ζ) :
    Nonempty (ScaleneSchemeCertificate u v w (scaleneBound u v w+ζ)) :=
  exists_scalene_scheme_certificate_of_objective hu hv hw (scaleneBound_nonneg hu hv hw)
    (fun φ => actual_scalene_character_objective_le φ hu hv hw) hζ

universe r

/-- The same finite integer circuit family computes ordered multiplication in
every associative ring, with a single size-independent gate constant. -/
theorem exists_scalene_multiplication_programs (u v w ζ : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hζ : 0 < ζ) :
    ∃ (P : ∀ n : ℕ, MatrixCircuit (width u n) (width v n) (width w n))
      (C : ℝ), 0 < C ∧
      (∀ (R : Type r) [NonUnitalRing R] (n : ℕ)
        (A : Matrix (Fin (width u n)) (Fin (width v n)) R)
        (B : Matrix (Fin (width v n)) (Fin (width w n)) R)
        (i : Fin (width u n)) (j : Fin (width w n)),
        (P n).eval (encode A B) (i,j) = (A*B) i j) ∧
      (∀ n : ℕ, 1 ≤ n → ((P n).cost:ℝ) ≤ C*(n:ℝ)^(scaleneBound u v w+ζ)) := by
  obtain ⟨cert⟩ := exists_scalene_scheme_certificate hu hv hw (show 0 < ζ/2 by positivity)
  have hq : 1 < cert.q := by have := cert.q_ge_two; omega
  have hρ : 1 ≤ cert.ρ := by
    have hvol := Matmul.RecursiveCost.blockVolume_bounds cert.a cert.b cert.c
    have hpos := (Nat.mul_pos cert.a_pos cert.b_pos).trans_le (hvol.1.trans cert.volume)
    omega
  obtain ⟨C,hC,hcost⟩ := scaleneProgram_cost_bound cert.alg u v w
    (scaleneBound u v w+ζ) hq hu hv hw cert.rowShape cert.innerShape cert.columnShape
    hρ cert.volume (by have := cert.rankExponent_lt; linarith)
  refine ⟨scaleneProgram cert.alg u v w hq hu hv hw cert.rowShape cert.innerShape cert.columnShape,
    C,hC,?_,hcost⟩
  intro R inst n A B i j
  exact scaleneProgram_correct cert.alg cert.correct u v w hq hu hv hw cert.rowShape
    cert.innerShape cert.columnShape n A B i j

/-- Actual exact-real arithmetic kernels realize the complete three-dimension
curve with every positive exponent slack. Correctness, admissibility, and
execution work follow from `ArithmeticKernel.program_eval`,
`ArithmeticKernel.program_admissible`, and `ArithmeticKernel.program_work`. -/
theorem exists_scalene_arithmetic_kernels (u v w ζ : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hζ : 0 < ζ) :
    ∃ (K : ∀ n : ℕ, ArithmeticKernel (width u n) (width v n) (width w n))
      (C : ℝ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((K n).cost:ℝ) ≤ C*(n:ℝ)^(scaleneBound u v w+ζ) := by
  obtain ⟨P,C,hC,hP,hcost⟩ := exists_scalene_multiplication_programs.{0} u v w ζ hu hv hw hζ
  let K : ∀ n : ℕ, ArithmeticKernel (width u n) (width v n) (width w n) := fun n =>
    { circuit := P n
      correct := by
        intro A B i j
        rw [matrixCircuitInput_eq_encode]
        exact hP ℝ n A B i j }
  exact ⟨K,C,hC,hcost⟩

theorem exists_sorted_scalene_arithmetic_kernels (a b c ζ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hba : b ≤ a) (hcb : c ≤ b)
    (hζ : 0 < ζ) :
    ∃ (K : ∀ n : ℕ, ArithmeticKernel (width a n) (width b n) (width c n))
      (C : ℝ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((K n).cost:ℝ) ≤ C*(n:ℝ)^((if c*(a+b) ≤ a*b then a+b else
        scaleneRationalBound a b c)+ζ) := by
  simpa only [scaleneBound_of_sorted ha hb hc hba hcb] using
    exists_scalene_arithmetic_kernels a b c ζ ha hb hc hζ

/-- An arbitrarily small exponent allowance also supplies strictly larger
dimensions. The resulting kernel can absorb logarithmic factors by padding. -/
theorem exists_inflated_scalene_arithmetic_kernels (u v w ζ : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ (K : ∀ n : ℕ, ArithmeticKernel (width (u+δ) n) (width (v+δ) n) (width (w+δ) n))
        (C : ℝ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        ((K n).cost:ℝ) ≤ C*(n:ℝ)^(scaleneBound u v w+ζ) := by
  obtain ⟨δ,hδ,hbound⟩ := exists_scalene_shape_slack hu hv hw (show 0 < ζ/2 by positivity)
  obtain ⟨K,C,hC,hK⟩ := exists_scalene_arithmetic_kernels (u+δ) (v+δ) (w+δ) (ζ/2)
    (by positivity) (by positivity) (by positivity) (by positivity)
  refine ⟨δ,hδ,K,C,hC,?_⟩
  intro n hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  exact (hK n hn).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hnR (by linarith)) hC.le)

theorem exists_twolevel_fine_arithmetic_kernels (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ n : ℕ, ArithmeticKernel (width (7/6) n) n (width (14/25) n))
      (C : ℝ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((K n).cost:ℝ) ≤ C*(n:ℝ)^(867/400+ζ) := by
  obtain ⟨K,C,hC,hK⟩ :=
    exists_scalene_arithmetic_kernels (7/6) 1 (14/25) ζ (by norm_num) (by norm_num)
      (by norm_num) hζ
  let Q : ∀ n : ℕ, ArithmeticKernel (width (7/6) n) n (width (14/25) n) :=
    fun n => (K n).padShape (Function.Embedding.refl _)
      (Fin.castLEEmb (le_of_eq (width_one n).symm)) (Function.Embedding.refl _)
  refine ⟨Q,C,hC,?_⟩
  intro n hn
  simpa only [Q,ArithmeticKernel.padShape_cost,scaleneBound_fine] using hK n hn

theorem exists_twolevel_true_arithmetic_kernels (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ n : ℕ, ArithmeticKernel (width (59/50) n) n (width (14/25) n))
      (C : ℝ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((K n).cost:ℝ) ≤ C*(n:ℝ)^(9006001/4130000+ζ) := by
  obtain ⟨K,C,hC,hK⟩ :=
    exists_scalene_arithmetic_kernels (59/50) 1 (14/25) ζ (by norm_num) (by norm_num)
      (by norm_num) hζ
  let Q : ∀ n : ℕ, ArithmeticKernel (width (59/50) n) n (width (14/25) n) :=
    fun n => (K n).padShape (Function.Embedding.refl _)
      (Fin.castLEEmb (le_of_eq (width_one n).symm)) (Function.Embedding.refl _)
  refine ⟨Q,C,hC,?_⟩
  intro n hn
  simpa only [Q,ArithmeticKernel.padShape_cost,scaleneBound_true] using hK n hn

theorem exists_twolevel_coarse_arithmetic_kernels (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ n : ℕ, ArithmeticKernel (width (57/50) n) n n)
      (C : ℝ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((K n).cost:ℝ) ≤ C*(n:ℝ)^(3362/1425+ζ) := by
  obtain ⟨K,C,hC,hK⟩ :=
    exists_scalene_arithmetic_kernels (57/50) 1 1 ζ (by norm_num) (by norm_num)
      (by norm_num) hζ
  let Q : ∀ n : ℕ, ArithmeticKernel (width (57/50) n) n n :=
    fun n => (K n).padShape (Function.Embedding.refl _)
      (Fin.castLEEmb (le_of_eq (width_one n).symm))
      (Fin.castLEEmb (le_of_eq (width_one n).symm))
  refine ⟨Q,C,hC,?_⟩
  intro n hn
  simpa only [Q,ArithmeticKernel.padShape_cost,scaleneBound_coarse] using hK n hn

#print axioms exists_scalene_arithmetic_kernels
#print axioms exists_twolevel_fine_arithmetic_kernels

end
end HierarchicalAbsoluteSpectral
