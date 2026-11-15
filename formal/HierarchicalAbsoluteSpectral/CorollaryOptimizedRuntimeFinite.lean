import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeCore
import HierarchicalAbsoluteSpectral.CorollaryOptimizedSupportCost
import HierarchicalAbsoluteSpectral.MainSketchCost
import HierarchicalAbsoluteSpectral.BaseMainTapeCost

/-! One uniform all-outcome operation bound for both actual comparators.
The bound counts actual sketch preprocessing, both Gram products, support,
every scalar cap, Gaussian draws and every explicit dense output entry. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {N m r s t : ℕ}

def comparatorGramRowWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (m N : ℕ) : ℕ :=
  Finset.univ.sup (fun s : Fin (N+1) => (kernels m s.val m).cost)

theorem comparatorGramRowWorkCap_le
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (m N s : ℕ) (hs : s ≤ N) :
    (kernels m s m).cost ≤ comparatorGramRowWorkCap kernels m N :=
  Finset.le_sup (f:=fun i : Fin (N+1) => (kernels m i.val m).cost)
    (Finset.mem_univ (⟨s,by omega⟩:Fin (N+1)))

theorem comparator_support_uniform_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (HA : Matrix (Fin s) (Fin m) ℝ) (HB : Matrix (Fin t) (Fin m) ℝ)
    (hm : 1 ≤ m) (hs : s ≤ N) (ht : t ≤ N) :
    (coarseSupportProgram kernels HA HB).work ≤
      2*comparatorGramRowWorkCap kernels m N+psdGramCost kernels m+2*kernelEnvelope kernels m := by
  have hwork := coarseSupportProgram_comparator_work_bound kernels HA HB hm
  have hGA := comparatorGramRowWorkCap_le kernels m N s hs
  have hGB := comparatorGramRowWorkCap_le kernels m N t ht
  unfold comparatorSupportWorkCap at hwork
  omega

def comparatorUniformWorkCap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem N m N r 1) (ζ χ χOut Ck : ℝ) : ℕ :=
  4*sketchFormationCap N m I.sketchFailure+
    2*comparatorGramRowWorkCap kernels m N+psdGramCost kernels m+2*kernelEnvelope kernels m+
      comparatorPreparedCoreWorkCap I ζ χ χOut Ck

def comparatorUniformTotalWorkCap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem N m N r 1) (ζ χ χOut Ck : ℝ) : ℕ :=
  m*(N+N)+N*N+mainRandomizedWork I (1+comparatorUniformWorkCap kernels I ζ χ χOut Ck)

theorem constantDistortionComparatorProgram_uniform_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (ζ χ χOut Ck : ℝ)
    (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut) (hC : 0 < Ck)
    (hEnv : FixedFamilyKernelEnvelopes ζ N m kernels χ χOut Ck)
    (I : FixedProblem N m N r 1) (haccuracy : I.accuracy=comparatorAccuracy)
    (hm : 2 ≤ m) (hr : r ≤ ⌊Real.sqrt (m:ℝ)⌋₊)
    (hraw : (comparatorOuterDegreeCap I+1)*(r+1) ≤ m) (g : MainRandomTape I) :
    (constantDistortionComparatorProgram kernels I g).work ≤
      comparatorUniformWorkCap kernels I ζ χ χOut Ck := by
  let S := (mainSketchProgram I g).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  have hs := mainSketchProgram_work_le I g
  have hs' : (mainSketchProgram I g).work ≤ 4*sketchFormationCap N m I.sketchFailure := by
    nlinarith
  have hc := comparator_support_uniform_work kernels S.initialA S.initialB (by omega : 1 ≤ m)
    (S.rowsA 0) (S.rowsB 0)
  have hmcore := mainCoreProgram_comparator_work_bound kernels ζ χ χOut Ck hζ hχ hχOut hC hEnv
    I haccuracy S C hm hr hraw g
  have he : (fixedDepthProgram kernels I g).work=
      (mainSketchProgram I g).work+(coarseSupportProgram kernels S.initialA S.initialB).work+
        (mainCoreProgram kernels I S C g).work := by
    simp only [fixedDepthProgram,work_bind,S,C]
    omega
  unfold constantDistortionComparatorProgram
  rw [preparedFixedDepthProgram_work,he]
  unfold comparatorUniformWorkCap comparatorPreparedCoreWorkCap
  omega

theorem exactGramComparatorProgram_uniform_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (ζ χ χOut Ck : ℝ)
    (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut) (hC : 0 < Ck)
    (hEnv : FixedFamilyKernelEnvelopes ζ N m kernels χ χOut Ck)
    (I : FixedProblem N m N r 1) (haccuracy : I.accuracy=comparatorAccuracy)
    (hm : 2 ≤ m) (hr : r ≤ ⌊Real.sqrt (m:ℝ)⌋₊)
    (hraw : (comparatorOuterDegreeCap I+1)*(r+1) ≤ m) (g : MainRandomTape I) :
    (exactGramComparatorProgram kernels I g).work ≤
      comparatorUniformWorkCap kernels I ζ χ χOut Ck := by
  let S := exactComparatorSketches I.A I.B 1
  let C : MainSupportData S := (coarseSupportProgram kernels I.A I.Bᵀ).eval
  have hs := comparator_support_uniform_work kernels I.A I.Bᵀ (by omega : 1 ≤ m) le_rfl le_rfl
  have hc := preparedMainCoreProgram_comparator_work_bound kernels ζ χ χOut Ck hζ hχ hχOut hC hEnv
    I haccuracy S C hm hr hraw g
  rw [exactGramComparatorProgram_work]
  unfold comparatorUniformWorkCap
  dsimp [S,C] at hc
  omega

theorem constantDistortionComparatorProgram_total_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (ζ χ χOut Ck : ℝ)
    (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut) (hC : 0 < Ck)
    (hEnv : FixedFamilyKernelEnvelopes ζ N m kernels χ χOut Ck)
    (I : FixedProblem N m N r 1) (haccuracy : I.accuracy=comparatorAccuracy)
    (hm : 2 ≤ m) (hr : r ≤ ⌊Real.sqrt (m:ℝ)⌋₊)
    (hraw : (comparatorOuterDegreeCap I+1)*(r+1) ≤ m) (g : MainRandomTape I) :
    m*(N+N)+N*N+mainRandomizedWork I (constantDistortionComparatorProgram kernels I g).work ≤
      comparatorUniformTotalWorkCap kernels I ζ χ χOut Ck := by
  have hh := constantDistortionComparatorProgram_uniform_work kernels ζ χ χOut Ck hζ hχ hχOut hC hEnv
    I haccuracy hm hr hraw g
  unfold comparatorUniformTotalWorkCap mainRandomizedWork
  omega

theorem exactGramComparatorProgram_total_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (ζ χ χOut Ck : ℝ)
    (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut) (hC : 0 < Ck)
    (hEnv : FixedFamilyKernelEnvelopes ζ N m kernels χ χOut Ck)
    (I : FixedProblem N m N r 1) (haccuracy : I.accuracy=comparatorAccuracy)
    (hm : 2 ≤ m) (hr : r ≤ ⌊Real.sqrt (m:ℝ)⌋₊)
    (hraw : (comparatorOuterDegreeCap I+1)*(r+1) ≤ m) (g : MainRandomTape I) :
    m*(N+N)+N*N+mainRandomizedWork I (exactGramComparatorProgram kernels I g).work ≤
      comparatorUniformTotalWorkCap kernels I ζ χ χOut Ck := by
  have hh := exactGramComparatorProgram_uniform_work kernels ζ χ χOut Ck hζ hχ hχOut hC hEnv
    I haccuracy hm hr hraw g
  unfold comparatorUniformTotalWorkCap mainRandomizedWork
  omega

end
end HierarchicalAbsoluteSpectral
