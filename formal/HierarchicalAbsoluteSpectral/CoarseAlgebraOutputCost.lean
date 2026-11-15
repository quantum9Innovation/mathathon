import HierarchicalAbsoluteSpectral.CoarseAlgebraHierarchyKernels
import HierarchicalAbsoluteSpectral.MainStatementsFixed

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
variable {n m p r w N : ℕ}

theorem projectionOutputProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (κ η ζ C : ℝ) (hκ : 1/2 ≤ κ)
    (hEnv : HierarchyKernelEnvelopes κ η ζ N m kernels C)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r)
    (hm : 1 ≤ m) (hNm : m ≤ N) (hn : n ≤ N) (hp : p ≤ N)
    (hwr : (w:ℝ) ≤ Real.sqrt (m:ℝ)) :
    ((projectionOutputProgram kernels A B U hw).work:ℝ) ≤
      2*C*(N:ℝ)*(m:ℝ)^(1+η)+C*(N:ℝ)^(2+ζ) := by
  have hwm := sqrt_rank_fits_outer_width κ hκ m m w hm le_rfl hwr
  have hwN := sqrt_rank_fits_outer_width (1/2) le_rfl m N w hm hNm hwr
  have hleft := hEnv.transpose_adjoint w n m hwm hn le_rfl
  have hright := hEnv.transpose_forward w m p hwm le_rfl hp
  have hout := hEnv.dense_output n w p hn hwN hp
  rw [projectionOutputProgram_work,Nat.cast_add,Nat.cast_add]
  linarith

theorem projectionOutputProgram_work_near_quadratic
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (κ η C : ℝ) (hκ : 1/2 ≤ κ) (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hEnv : HierarchyKernelEnvelopes κ η η N m kernels C)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r)
    (hm : 1 ≤ m) (hNm : m ≤ N) (hn : n ≤ N) (hp : p ≤ N)
    (hwr : (w:ℝ) ≤ Real.sqrt (m:ℝ)) :
    ((projectionOutputProgram kernels A B U hw).work:ℝ) ≤ 3*C*(N:ℝ)^(2+η) := by
  have hN : (0:ℝ) < N := by exact_mod_cast hm.trans hNm
  have hpow : (m:ℝ)^(1+η) ≤ (N:ℝ)^(1+η) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hNm) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2*C*(N:ℝ) by positivity)
  have hid : (N:ℝ)*(N:ℝ)^(1+η) = (N:ℝ)^(2+η) := by
    calc
      _ = (N:ℝ)^(1:ℝ)*(N:ℝ)^(1+η) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring
  have hb := projectionOutputProgram_work_bound kernels κ η η C hκ hEnv A B U hw hm hNm hn hp hwr
  nlinarith

end
end HierarchicalAbsoluteSpectral
