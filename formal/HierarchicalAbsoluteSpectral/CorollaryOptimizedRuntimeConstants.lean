import HierarchicalAbsoluteSpectral.CorollaryOptimizedPrograms
import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeActions
import HierarchicalAbsoluteSpectral.BaseMainOperatorCost

/-! Fixed constants and literal action recurrence for the one-refinement
comparator.  Every large matrix action is charged through its actual
fixed-row circuit family. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Matmul.RectangularPrograms
variable {N m r b : ℕ}

def comparatorFineNeumannCount : ℕ := neumannCount ((1/1048576:ℝ)/100) (by norm_num)

def comparatorRefinementLevel : ℕ :=
  inverseRootLevel (8*((1/1048576:ℝ)/(1/1024)))
    (refinementTolerance (1/1048576) (hierarchyUpper 0)) (by norm_num)
      (by unfold refinementTolerance hierarchyUpper; norm_num)

def comparatorFactorConstant : ℝ :=
  7+80*(comparatorRefinementLevel+3:ℕ)*2^comparatorRefinementLevel+18+
    (2^comparatorRefinementLevel:ℕ)*(44+2048*comparatorFineNeumannCount)

theorem comparatorFactorConstant_ge_one : 1 ≤ comparatorFactorConstant := by
  have h1 : (0:ℝ) ≤ 80*(comparatorRefinementLevel+3:ℕ)*(2^comparatorRefinementLevel:ℕ) := by positivity
  have h2 : (0:ℝ) ≤ (2^comparatorRefinementLevel:ℕ)*(44+2048*comparatorFineNeumannCount) := by positivity
  unfold comparatorFactorConstant
  push_cast at h1 h2 ⊢
  linarith

theorem comparator_small_kernel_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (hNm : m ≤ N) (k : ℕ) (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ((kernels k k b).cost:ℝ) ≤ 16*χ*(N:ℝ)*(m:ℝ) := by
  have hh := hrow.forward k k b hk hb
  have hkN : (k:ℝ) ≤ N := by exact_mod_cast hk.trans hNm
  have hmN : (m:ℝ) ≤ N := by exact_mod_cast hNm
  have hp : 0 ≤ χ*(m:ℝ) := by positivity
  push_cast at hh
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hkN),mul_nonneg hp (sub_nonneg.mpr hmN)]

theorem comparator_fine_action_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (I : FixedProblem N m N r 1) (haccuracy : I.accuracy=comparatorAccuracy)
    (S : StoredSketches N m N 1) (C : MainSupportData S)
    (hm : 1 ≤ m) (hNm : m ≤ N) (hb : b ≤ 2*width (1/2) m) :
    (mainFineActionCost kernels I S C 0 b:ℝ) ≤
      2048*comparatorFineNeumannCount*χ*(N:ℝ)*(m:ℝ) := by
  have hh := comparator_stored_pencil_cost (b:=b) kernels χ hχ hrow
    (S.levelA (safeSketchIndex 1 (0+1))).2 (S.levelB (safeSketchIndex 1 (0+1))).2
    C.pair.factor C.pair.leftInverseᵀ 0 (safeAccuracy I (0+1)/100)
    (by have := safeAccuracy_pos I (0+1); positivity)
    hm hNm (S.rowsA _) (S.rowsB _) (mainSupport_dimension_le S C) hb
  change (mainFineActionCost kernels I S C 0 b:ℝ) ≤ _ at hh
  simpa only [safeAccuracy,haccuracy,show min (0+1) 1=1 by omega,
    comparatorAccuracy_one,comparatorFineNeumannCount] using hh

theorem comparator_factor_action_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (I : FixedProblem N m N r 1) (haccuracy : I.accuracy=comparatorAccuracy)
    (S : StoredSketches N m N 1) (C : MainSupportData S)
    (hm : 1 ≤ m) (hNm : m ≤ N) (hb : b ≤ 2*width (1/2) m) :
    (mainFactorActionCost kernels I S C b 1:ℝ) ≤
      comparatorFactorConstant*χ*(N:ℝ)*(m:ℝ) := by
  let A : ℝ := χ*(N:ℝ)*(m:ℝ)
  have hA1 : 1 ≤ A := by
    have hN : (1:ℝ) ≤ N := by exact_mod_cast hm.trans hNm
    have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hh : (1:ℝ) ≤ χ*(N:ℝ) := by
      simpa only [one_mul] using
        (mul_le_mul hχ hN (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ χ))
    dsimp only [A]
    simpa only [one_mul] using
      (mul_le_mul hh hmR (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ χ*(N:ℝ)))
  have hP := comparator_small_kernel_cost (b:=b) kernels χ hχ hrow hNm _ (mainSupport_dimension_le S C) hb
  have hJ := comparator_fine_action_cost (b:=b) kernels χ hχ hrow I haccuracy S C hm hNm hb
  have hb2 : b ≤ 2*m := hb.trans (Nat.mul_le_mul_left 2 (half_width_le m hm))
  have hkR : (C.pair.dimension:ℝ) ≤ m := by exact_mod_cast mainSupport_dimension_le S C
  have hbR : (b:ℝ) ≤ 2*m := by exact_mod_cast hb2
  have hNmR : (m:ℝ) ≤ N := by exact_mod_cast hNm
  have hkb : (C.pair.dimension:ℝ)*b ≤ 2*A := by
    have hh := mul_le_mul hkR hbR (Nat.cast_nonneg b) (Nat.cast_nonneg m)
    have hh' := mul_le_mul_of_nonneg_right hNmR (Nat.cast_nonneg m)
    have hh'' := mul_le_mul_of_nonneg_right hχ (show 0 ≤ (N:ℝ)*(m:ℝ) by positivity)
    dsimp [A]
    nlinarith
  have he : (mainFactorActionCost kernels I S C b 1:ℝ) =
      7+80*(comparatorRefinementLevel+3:ℕ)*2^comparatorRefinementLevel+
        (kernels C.pair.dimension C.pair.dimension b).cost+(C.pair.dimension:ℝ)*b+
          (2^comparatorRefinementLevel:ℕ)*
            (2*(kernels C.pair.dimension C.pair.dimension b).cost+
              (mainFineActionCost kernels I S C 0 b:ℝ)+6*(C.pair.dimension:ℝ)*b) := by
    simp only [mainFactorActionCost,refinementActionEnvelope,max_self,
      safeAccuracy,haccuracy,Nat.min_zero,Nat.zero_min,Nat.zero_add,Nat.min_self,
      comparatorAccuracy_zero,comparatorAccuracy_one,comparatorRefinementLevel]
    push_cast
    ring
  rw [he]
  have hconstant : (7:ℝ)+80*(comparatorRefinementLevel+3:ℕ)*2^comparatorRefinementLevel ≤
      (7+80*(comparatorRefinementLevel+3:ℕ)*2^comparatorRefinementLevel)*A := by
    have hn : (0:ℝ) ≤ 7+80*(comparatorRefinementLevel+3:ℕ)*2^comparatorRefinementLevel := by positivity
    have hh := mul_le_mul_of_nonneg_left hA1 hn
    simpa only [mul_one] using hh
  have hinside : 2*((kernels C.pair.dimension C.pair.dimension b).cost:ℝ)+
      (mainFineActionCost kernels I S C 0 b:ℝ)+6*(C.pair.dimension:ℝ)*b ≤
        (44+2048*comparatorFineNeumannCount)*A := by
    dsimp [A] at hkb ⊢
    push_cast
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hinside (show (0:ℝ) ≤ (2^comparatorRefinementLevel:ℕ) by positivity)
  dsimp [A,comparatorFactorConstant] at hA1 hkb hconstant hp ⊢
  push_cast at hconstant hp ⊢
  nlinarith

end
end HierarchicalAbsoluteSpectral
