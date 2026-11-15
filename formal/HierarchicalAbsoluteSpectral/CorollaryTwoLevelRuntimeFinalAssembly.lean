import HierarchicalAbsoluteSpectral.CorollaryTwoLevelConstructionMainCost
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalTape
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalSketchCost

/-! The literal explicit work counter is bounded by four actual stages:
tape/preparation, sketch formation, coarse support, and the thin core. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open ArithmeticProgram hiding pure
variable {N m r : ℕ}

def twoLevelRuntimeActualCoreWorkCap (Ck : ℝ) (I : TwoLevelProblem N m r)
    (g : MainRandomTape I.fixed) : ℕ :=
  let K := twoLevelRuntimeFinalKernels m
  let S := (mainSketchProgram I.fixed g).eval
  let C := (coarseSupportProgram K S.initialA S.initialB).eval
  twoLevelFactorCoreWorkCap K I.fixed S C
    (fun hr => mainFlexibleQueryWorkCap K (rangeDeflationWorkCap K) I.fixed S C hr
      Ck twoLevelRuntimeGlobalExponent)

def twoLevelRuntimeActualSupportWorkCap (I : TwoLevelProblem N m r)
    (g : MainRandomTape I.fixed) : ℕ :=
  coarseSupportWorkCap (twoLevelRuntimeFinalKernels m) m
    ((mainSketchProgram I.fixed g).eval.levelA 0).1
    ((mainSketchProgram I.fixed g).eval.levelB 0).1

theorem twoLevelRuntimeFinalConstruction_decompose (Ck : ℝ) (hC : 0 < Ck)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((twoLevelRuntimeFinalKernels m a b c).cost:ℝ) ≤ Ck*(D:ℝ)^twoLevelRuntimeGlobalExponent)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    twoLevelConstructionExplicitWork (twoLevelRuntimeFinalKernels m) I g ≤
      twoLevelRuntimeRestWorkCap I+twoLevelInitialSketchWorkCap N m I.fixed.sketchFailure+
        twoLevelRuntimeActualSupportWorkCap I g+twoLevelRuntimeActualCoreWorkCap Ck I g := by
  have h := twoLevelConstructionExplicitWork_bound (twoLevelRuntimeFinalKernels m)
    (twoLevelRuntimeFinalKernels_classical m) Ck twoLevelRuntimeGlobalExponent hC
    (by norm_num [twoLevelRuntimeGlobalExponent]) hK I g
  simp only [twoLevelFactorFixedWorkCap] at h
  unfold twoLevelRuntimeRestWorkCap twoLevelScalarPreparationWorkCap
    twoLevelInitialSketchWorkCap twoLevelRuntimeActualSupportWorkCap twoLevelRuntimeActualCoreWorkCap
  dsimp only at h ⊢
  omega

end
end HierarchicalAbsoluteSpectral
