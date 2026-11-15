import HierarchicalAbsoluteSpectral.CoarseAlgebraBlockedKernels

/-! Actual blocked matrix circuits for both directions of a tall matrix
action. The large dimension enters the gate count linearly. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matmul.RectangularPrograms

def blockedForwardKernel {κ : ℝ}
    (K : ∀ m : ℕ, ArithmeticKernel m m (width κ m))
    (N m b : ℕ) (hm : 0 < m) (hb : b ≤ width κ m) : ArithmeticKernel N m b :=
  ((K m).restrictWidth hb).tall N hm

def blockedAdjointKernel {κ : ℝ}
    (K : ∀ m : ℕ, ArithmeticKernel m m (width κ m))
    (N m b : ℕ) (hm : 0 < m) (hb : b ≤ width κ m) : ArithmeticKernel m N b :=
  ((K m).restrictWidth hb).longInner N hm

theorem exists_input_optimal_arithmetic_kernels (κ ζ : ℝ) (hκ : 0 ≤ κ) (hζ : 0 < ζ) :
    ∃ (K : ∀ m : ℕ, ArithmeticKernel m m (width κ m)) (C : ℝ), 0 < C ∧
      ∀ (N m b : ℕ) (hm : 0 < m) (hNm : m ≤ N) (hb : b ≤ width κ m),
        ((blockedForwardKernel K N m b hm hb).cost:ℝ) ≤
          2*C*(N:ℝ)*(m:ℝ)^(Matmul.RectangularOptimization.rectangularBound κ+ζ-1) ∧
        ((blockedAdjointKernel K N m b hm hb).cost:ℝ) ≤
          2*C*(N:ℝ)*(m:ℝ)^(Matmul.RectangularOptimization.rectangularBound κ+ζ-1)
            +2*(N:ℝ)*(b:ℝ) := by
  obtain ⟨K,C,hC,hK⟩ := exists_outer_rectangular_arithmetic_kernels κ ζ hκ hζ
  refine ⟨K,C,hC,?_⟩
  intro N m b hm hNm hb
  have hcost : (((K m).restrictWidth hb).cost:ℝ) ≤
      C*(m:ℝ)^(Matmul.RectangularOptimization.rectangularBound κ+ζ) := by
    simpa only [ArithmeticKernel.restrictWidth_cost] using hK m hm
  exact ⟨((K m).restrictWidth hb).tall_cost_bound N hm hNm _ _ hC.le hcost,
    ((K m).restrictWidth hb).longInner_cost_bound N hm hNm _ _ hC.le hcost⟩

theorem half_width_le (m : ℕ) (hm : 1 ≤ m) : width (1/2) m ≤ m := by
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  apply Nat.ceil_le.mpr
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hmR (show (1/2:ℝ) ≤ 1 by norm_num)

theorem exists_half_input_optimal_arithmetic_kernels (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ m : ℕ, ArithmeticKernel m m (width (1/2) m)) (C : ℝ), 0 < C ∧
      ∀ (N m b : ℕ) (hm : 0 < m) (hNm : m ≤ N) (hb : b ≤ width (1/2) m),
        ((blockedForwardKernel K N m b hm hb).cost:ℝ) ≤ C*(N:ℝ)*(m:ℝ)^(1+ζ) ∧
        ((blockedAdjointKernel K N m b hm hb).cost:ℝ) ≤ C*(N:ℝ)*(m:ℝ)^(1+ζ) := by
  obtain ⟨K,C,hC,hK⟩ := exists_input_optimal_arithmetic_kernels (1/2) ζ (by norm_num) hζ
  refine ⟨K,2*(C+1),by positivity,?_⟩
  intro N m b hm hNm hb
  have hs := hK N m b hm hNm hb
  have he : Matmul.RectangularOptimization.rectangularBound (1/2)+ζ-1 = 1+ζ := by
    rw [Matmul.RectangularOptimization.rectangularBound_half]
    ring
  rw [he] at hs
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hbR : (b:ℝ) ≤ (m:ℝ) := by exact_mod_cast hb.trans (half_width_le m hm)
  have hp : (b:ℝ) ≤ (m:ℝ)^(1+ζ) := hbR.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hmR (show (1:ℝ) ≤ 1+ζ by linarith))
  have hnon : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hrnon : 0 ≤ (m:ℝ)^(1+ζ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  constructor
  · exact hs.1.trans (by nlinarith)
  · exact hs.2.trans (by nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 2*(N:ℝ) by positivity)])

end
end HierarchicalAbsoluteSpectral
