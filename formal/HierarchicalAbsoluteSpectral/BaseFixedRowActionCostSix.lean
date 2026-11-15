import HierarchicalAbsoluteSpectral.BaseFixedRowActionCost
import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedCyclicRowFamily

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matmul.RectangularPrograms
variable {m k b s : ℕ}

/-- The same row scale controls every permutation used by a symmetric
matrix-product envelope. The literal stored Gram action needs its four
inherited orientations, so its bounds accept `hrow.toFixedRowKernelEnvelopes`. -/
theorem fixedSixRowKernelEnvelopes_six_orientations
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ)
    (hrow : FixedSixRowKernelEnvelopes m kernels χ)
    (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    (((kernels s k b).cost:ℝ) ≤ 8*χ*(s+m:ℕ)*(m:ℝ) ∧
      ((kernels k s b).cost:ℝ) ≤ 8*χ*(s+m:ℕ)*(m:ℝ) ∧
      ((kernels b k s).cost:ℝ) ≤ 8*χ*(s+m:ℕ)*(m:ℝ) ∧
      ((kernels b s k).cost:ℝ) ≤ 8*χ*(s+m:ℕ)*(m:ℝ)) ∧
    ((kernels s b k).cost:ℝ) ≤ 8*χ*(s+m:ℕ)*(m:ℝ) ∧
    ((kernels k b s).cost:ℝ) ≤ 8*χ*(s+m:ℕ)*(m:ℝ) :=
  ⟨fixedRowKernelEnvelopes_four_orientations kernels χ hrow.toFixedRowKernelEnvelopes hk hb,
    hrow.cyclic_forward s b k hb hk,hrow.cyclic_transpose k b s hk hb⟩

end
end HierarchicalAbsoluteSpectral
