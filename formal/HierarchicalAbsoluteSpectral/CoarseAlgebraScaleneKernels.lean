import HierarchicalAbsoluteSpectral.FastKernels

/-!
Three independent rectangular shape exponents at a common recursion depth.
The circuit is the existing strict integer recursion, zero padding, and output
wires. Every addition, negation, and ordered multiplication is counted.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matmul.UniversalRecursiveAlgorithm Matmul.UniversalPaddedProgram
open Matmul.IntegerBilinear Matmul.RectangularPrograms
open Filter

def scaleneProgram {q a b c ρ : ℕ} (alg : Scheme a b c ρ)
    (u v w : ℝ) (hq : 1 < q) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hqa : (q:ℝ)^u ≤ a) (hqb : (q:ℝ)^v ≤ b) (hqc : (q:ℝ)^w ≤ c)
    (n : ℕ) : MatrixCircuit (width u n) (width v n) (width w n) :=
  paddedProgram alg (depth q n)
    (inner_fits q a n u hq hu hqa)
    (inner_fits q b n v hq hv hqb)
    (inner_fits q c n w hq hw hqc)

theorem scaleneProgram_correct {q a b c ρ : ℕ} {R : Type*} [NonUnitalRing R]
    (alg : Scheme a b c ρ) (hcorr : alg.tensor = matrixTensor a b c)
    (u v w : ℝ) (hq : 1 < q) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hqa : (q:ℝ)^u ≤ a) (hqb : (q:ℝ)^v ≤ b) (hqc : (q:ℝ)^w ≤ c)
    (n : ℕ) (A : Matrix (Fin (width u n)) (Fin (width v n)) R)
    (B : Matrix (Fin (width v n)) (Fin (width w n)) R)
    (i : Fin (width u n)) (j : Fin (width w n)) :
    (scaleneProgram alg u v w hq hu hv hw hqa hqb hqc n).eval (encode A B) (i,j) =
      (A*B) i j :=
  paddedProgram_correct alg hcorr (depth q n)
    (inner_fits q a n u hq hu hqa) (inner_fits q b n v hq hv hqb)
    (inner_fits q c n w hq hw hqc) A B i j

theorem scaleneProgram_cost_le_work {q a b c ρ : ℕ} (alg : Scheme a b c ρ)
    (u v w : ℝ) (hq : 1 < q) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hqa : (q:ℝ)^u ≤ a) (hqb : (q:ℝ)^v ≤ b) (hqc : (q:ℝ)^w ≤ c) (n : ℕ) :
    (scaleneProgram alg u v w hq hu hv hw hqa hqb hqc n).cost ≤
      Matmul.RecursiveCost.paddedWork 1 (linearWeight alg) ρ
        (Matmul.RecursiveCost.blockVolume a b c) q n :=
  paddedProgram_cost_le_work alg (depth q n)
    (inner_fits q a n u hq hu hqa) (inner_fits q b n v hq hv hqb)
    (inner_fits q c n w hq hw hqc)

theorem scaleneProgram_cost_bound {q a b c ρ : ℕ} (alg : Scheme a b c ρ)
    (u v w E : ℝ) (hq : 1 < q) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hqa : (q:ℝ)^u ≤ a) (hqb : (q:ℝ)^v ≤ b) (hqc : (q:ℝ)^w ≤ c)
    (hρ : 1 ≤ ρ) (hvolume : Matmul.RecursiveCost.blockVolume a b c ≤ ρ)
    (hE : Real.log (ρ:ℝ)/Real.log (q:ℝ) < E) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((scaleneProgram alg u v w hq hu hv hw hqa hqb hqc n).cost:ℝ) ≤ C*(n:ℝ)^E := by
  let θ := Real.log (ρ:ℝ)/Real.log (q:ℝ)
  let δ := (E-θ)/2
  have hδ : 0 < δ := by dsimp [δ,θ]; linarith
  have hqR : 1 < (q:ℝ) := by exact_mod_cast hq
  have hρR : 1 ≤ (ρ:ℝ) := by exact_mod_cast hρ
  have hθ : 0 ≤ θ := div_nonneg (Real.log_nonneg hρR) (Real.log_pos hqR).le
  have hE0 : 0 ≤ E := hθ.trans hE.le
  have hθδ : θ+δ ≤ E := by dsimp [δ]; linarith
  have hwork := Matmul.RecursiveCost.paddedWork_eventually_rpow
    1 (linearWeight alg) ρ (Matmul.RecursiveCost.blockVolume a b c) q
    hρ hvolume hq δ hδ
  let A := (q:ℝ)^(θ+δ)
  have hA : 0 ≤ A := Real.rpow_nonneg (Nat.cast_nonneg _) _
  apply all_sizes_of_eventual_bound
    (fun n => (scaleneProgram alg u v w hq hu hv hw hqa hqb hqc n).cost) E A hE0 hA
  filter_upwards [hwork,eventually_ge_atTop 1] with n hn hnpos
  have hc : ((scaleneProgram alg u v w hq hu hv hw hqa hqb hqc n).cost:ℝ) ≤
      (Matmul.RecursiveCost.paddedWork 1 (linearWeight alg) ρ
        (Matmul.RecursiveCost.blockVolume a b c) q n:ℝ) := by
    exact_mod_cast scaleneProgram_cost_le_work alg u v w hq hu hv hw hqa hqb hqc n
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  exact (hc.trans hn).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hnR hθδ) hA)

def scaleneKernel {q a b c ρ : ℕ} (alg : Scheme a b c ρ)
    (hcorr : alg.tensor = matrixTensor a b c)
    (u v w : ℝ) (hq : 1 < q) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hqa : (q:ℝ)^u ≤ a) (hqb : (q:ℝ)^v ≤ b) (hqc : (q:ℝ)^w ≤ c)
    (n : ℕ) : ArithmeticKernel (width u n) (width v n) (width w n) where
  circuit := scaleneProgram alg u v w hq hu hv hw hqa hqb hqc n
  correct A B i j := by
    rw [matrixCircuitInput_eq_encode]
    exact scaleneProgram_correct alg hcorr u v w hq hu hv hw hqa hqb hqc n A B i j

theorem exists_scalene_arithmetic_kernels_of_scheme {q a b c ρ : ℕ}
    (alg : Scheme a b c ρ) (hcorr : alg.tensor = matrixTensor a b c)
    (u v w E : ℝ) (hq : 1 < q) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hqa : (q:ℝ)^u ≤ a) (hqb : (q:ℝ)^v ≤ b) (hqc : (q:ℝ)^w ≤ c)
    (hρ : 1 ≤ ρ) (hvolume : Matmul.RecursiveCost.blockVolume a b c ≤ ρ)
    (hE : Real.log (ρ:ℝ)/Real.log (q:ℝ) < E) :
    ∃ (K : ∀ n : ℕ, ArithmeticKernel (width u n) (width v n) (width w n))
      (C : ℝ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ((K n).cost:ℝ) ≤ C*(n:ℝ)^E := by
  obtain ⟨C,hC,hcost⟩ := scaleneProgram_cost_bound alg u v w E hq hu hv hw hqa hqb hqc
    hρ hvolume hE
  exact ⟨scaleneKernel alg hcorr u v w hq hu hv hw hqa hqb hqc,C,hC,hcost⟩

end
end HierarchicalAbsoluteSpectral
