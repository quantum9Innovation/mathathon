import HierarchicalAbsoluteSpectral.CoarseAlgebraTensorSymmetry

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matmul.UniversalRecursiveAlgorithm Matmul.UniversalPaddedProgram
open Matmul.IntegerBilinear Matmul.RectangularPrograms
open Filter

def outerRectangularProgram {a b ρ : ℕ} (alg : Scheme a a b ρ) (κ : ℝ)
    (ha : 1 < a) (hκ : 0 ≤ κ) (hab : (a:ℝ)^κ ≤ (b:ℝ)) (n : ℕ) :
    MatrixCircuit n n (width κ n) :=
  paddedProgram alg (depth a n) (outer_fits a n ha) (outer_fits a n ha)
    (inner_fits a b n κ ha hκ hab)

theorem outerRectangularProgram_cost_le_work {a b ρ : ℕ} (alg : Scheme a a b ρ) (κ : ℝ)
    (ha : 1 < a) (hκ : 0 ≤ κ) (hab : (a:ℝ)^κ ≤ (b:ℝ)) (n : ℕ) :
    (outerRectangularProgram alg κ ha hκ hab n).cost ≤
      Matmul.RecursiveCost.paddedWork 1 (linearWeight alg) ρ (Matmul.RecursiveCost.blockVolume a a b) a n := by
  exact paddedProgram_cost_le_work alg (depth a n) (outer_fits a n ha) (outer_fits a n ha)
    (inner_fits a b n κ ha hκ hab)

theorem outerRectangularProgram_cost_bound {a b ρ : ℕ} (alg : Scheme a a b ρ) (κ E : ℝ)
    (ha : 1 < a) (hκ : 0 ≤ κ) (hab : (a:ℝ)^κ ≤ (b:ℝ))
    (hρ : 1 ≤ ρ) (hv : Matmul.RecursiveCost.blockVolume a a b ≤ ρ)
    (hE : Real.log (ρ:ℝ)/Real.log (a:ℝ) < E) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((outerRectangularProgram alg κ ha hκ hab n).cost:ℝ) ≤ C*(n:ℝ)^E := by
  let θ := Real.log (ρ:ℝ)/Real.log (a:ℝ)
  let δ := (E-θ)/2
  have hδ : 0 < δ := by dsimp [δ,θ]; linarith
  have haR : 1 < (a:ℝ) := by exact_mod_cast ha
  have hρR : 1 ≤ (ρ:ℝ) := by exact_mod_cast hρ
  have hθ : 0 ≤ θ := div_nonneg (Real.log_nonneg hρR) (Real.log_pos haR).le
  have hE0 : 0 ≤ E := hθ.trans hE.le
  have hθδ : θ+δ ≤ E := by dsimp [δ]; linarith
  have hw := Matmul.RecursiveCost.paddedWork_eventually_rpow 1 (linearWeight alg) ρ
    (Matmul.RecursiveCost.blockVolume a a b) a hρ hv ha δ hδ
  let A := (a:ℝ)^(θ+δ)
  have hA : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  apply all_sizes_of_eventual_bound (fun n => (outerRectangularProgram alg κ ha hκ hab n).cost) E A hE0 hA
  filter_upwards [hw,eventually_ge_atTop 1] with n hn hnpos
  have hc : ((outerRectangularProgram alg κ ha hκ hab n).cost:ℝ) ≤
      (Matmul.RecursiveCost.paddedWork 1 (linearWeight alg) ρ (Matmul.RecursiveCost.blockVolume a a b) a n:ℝ) := by
    exact_mod_cast outerRectangularProgram_cost_le_work alg κ ha hκ hab n
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  exact (hc.trans hn).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hnR hθδ) hA)

def outerRectangularKernel {a b ρ : ℕ} (alg : Scheme a a b ρ)
    (hcorr : alg.tensor = matrixTensor a a b) (κ : ℝ) (ha : 1 < a)
    (hκ : 0 ≤ κ) (hab : (a:ℝ)^κ ≤ (b:ℝ)) (n : ℕ) : ArithmeticKernel n n (width κ n) where
  circuit := outerRectangularProgram alg κ ha hκ hab n
  correct A B i j := by
    rw [matrixCircuitInput_eq_encode]
    exact paddedProgram_correct alg hcorr (depth a n) (outer_fits a n ha) (outer_fits a n ha)
      (inner_fits a b n κ ha hκ hab) A B i j

theorem exists_outer_rectangular_arithmetic_kernels (κ ζ : ℝ) (hκ : 0 ≤ κ) (hζ : 0 < ζ) :
    ∃ (K : ∀ n : ℕ, ArithmeticKernel n n (width κ n)) (C : ℝ), 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ((K n).cost:ℝ) ≤ C*(n:ℝ)^(Matmul.RectangularOptimization.rectangularBound κ+ζ) := by
  obtain ⟨cert⟩ := exists_outer_scheme_certificate κ (ζ/2) hκ (by positivity)
  have ha : 1 < cert.a := by have := cert.a_ge_two; omega
  have hρ : 1 ≤ cert.ρ := by
    have hv := Matmul.RecursiveCost.blockVolume_bounds cert.a cert.a cert.b
    have hp : 0 < cert.a := by omega
    have hh := (Nat.mul_pos hp hp).trans_le (hv.1.trans cert.volume)
    omega
  obtain ⟨C,hC,hcost⟩ := outerRectangularProgram_cost_bound cert.alg κ
    (Matmul.RectangularOptimization.rectangularBound κ+ζ) ha hκ cert.shape hρ cert.volume
    (by have := cert.rankExponent_lt; linarith)
  exact ⟨outerRectangularKernel cert.alg cert.correct κ ha hκ cert.shape,C,hC,hcost⟩

theorem exists_half_outer_rectangular_arithmetic_kernels (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ n : ℕ, ArithmeticKernel n n (width (1/2) n)) (C : ℝ), 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ((K n).cost:ℝ) ≤ C*(n:ℝ)^(2+ζ) := by
  simpa only [Matmul.RectangularOptimization.rectangularBound_half] using
    exists_outer_rectangular_arithmetic_kernels (1/2) ζ (by norm_num) hζ

end
end HierarchicalAbsoluteSpectral
