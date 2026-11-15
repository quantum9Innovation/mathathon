import HierarchicalAbsoluteSpectral.BaseFixedProductEnvelopes
import HierarchicalAbsoluteSpectral.BaseFixedStaticCost
import HierarchicalAbsoluteSpectral.BaseFixedOutputCost

/-! The same product bounds applied to the named input and fine-leaf
quantities in the fixed-depth paper budget. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matmul.RectangularPrograms
variable {n m p r L : ℕ}

theorem mainInputProductCost_fixed_six_row_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedSixRowKernelEnvelopes m K χ)
    (N b : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hn : n ≤ N) (hp : p ≤ N)
    (hb : b ≤ 2*width (1/2) m) :
    (mainInputProductCost K n m p b:ℝ) ≤ 64*χ*(m:ℝ)*(N:ℝ) :=
  matrixProductCost_fixed_input_pair_bound K χ hχ hrow n p N b hm hmN hn hp hb

theorem fixedOutputInputCost_fixed_six_row_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedSixRowKernelEnvelopes m K χ)
    (N : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hn : n ≤ N) (hp : p ≤ N)
    (hb : r+1 ≤ 2*width (1/2) m) :
    (fixedOutputInputCost K n m p r:ℝ) ≤ 64*χ*(m:ℝ)*(N:ℝ) :=
  matrixProductCost_fixed_input_pair_bound K χ hχ hrow n p N (r+1) hm hmN hn hp hb

theorem mainFineProductCost_fixed_six_row_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedSixRowKernelEnvelopes m K χ)
    (S : StoredSketches n m p L) (j b : ℕ) (hm : 1 ≤ m)
    (hb : b ≤ 2*width (1/2) m) :
    (mainFineProductCost K S j b:ℝ) ≤
      32*χ*(m:ℝ)*((S.levelA (safeSketchIndex L (j+1))).1+
        (S.levelB (safeSketchIndex L (j+1))).1+m:ℕ) :=
  matrixProductCost_fixed_fine_pair_bound K χ hχ hrow
    (S.levelA (safeSketchIndex L (j+1))).1
    (S.levelB (safeSketchIndex L (j+1))).1 b hm hb

theorem fixedFineProductCost_fixed_six_row_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedSixRowKernelEnvelopes m K χ)
    (I : FixedProblem n m p r L) (j b : ℕ)
    (hb : b ≤ 2*width (1/2) m) :
    (fixedFineProductCost K I j b:ℝ) ≤
      32*χ*(m:ℝ)*(fixedSketchRowsA I (safeSketchIndex L (j+1))+
        fixedSketchRowsB I (safeSketchIndex L (j+1))+m:ℕ) :=
  matrixProductCost_fixed_fine_pair_bound K χ hχ hrow
    (fixedSketchRowsA I (safeSketchIndex L (j+1)))
    (fixedSketchRowsB I (safeSketchIndex L (j+1))) b
    (I.rank_positive.trans I.rank_le_core) hb

theorem FixedFamilyKernelEnvelopes.matrixProductCost_core_bound
    {ζ χ χOut C : ℝ} {N : ℕ}
    {K : ∀ a b c : ℕ, ArithmeticKernel a b c}
    (hK : FixedFamilyKernelEnvelopes ζ N m K χ χOut C)
    (hC : 0 < C) (hζ : 0 ≤ ζ)
    (a b c D : ℕ) (hD : 1 ≤ D) (ha : a ≤ D) (hb : b ≤ D) (hc : c ≤ D) :
    (matrixProductCost K a b c:ℝ) ≤ (C+5)*(D:ℝ)^(9/4+ζ) :=
  _root_.HierarchicalAbsoluteSpectral.matrixProductCost_core_bound
    K C (9/4+ζ) hC (by linarith) hK.core a b c D hD ha hb hc

end
end HierarchicalAbsoluteSpectral
