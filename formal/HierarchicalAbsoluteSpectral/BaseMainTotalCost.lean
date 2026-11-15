import HierarchicalAbsoluteSpectral.BaseMainCoreCost
import HierarchicalAbsoluteSpectral.MainSketchCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L s t : ℕ}
attribute [local irreducible] mainCoreProgram mainSketchProgram

def coarseSupportWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (m s t : ℕ) : ℕ :=
  (kernels m s m).cost+psdGramCost kernels m+(kernels m t m).cost+
    2*kernelEnvelope kernels m

theorem coarseSupportProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (H : Matrix (Fin s) (Fin m) ℝ) (J : Matrix (Fin t) (Fin m) ℝ) (hm : 1 ≤ m) :
    (coarseSupportProgram kernels H J).work ≤ coarseSupportWorkCap kernels m s t := by
  let GA := ((kernels m s m).program Hᵀ H).certify.eval
  have hGA : GA.val=Hᵀ*H := GA.property.trans (ArithmeticKernel.program_eval _ _ _)
  have hGApos : GA.val.PosSemidef := by
    rw [hGA]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self H
  let pair := (psdGramProgram kernels m GA.val hGApos).eval.cast hGA
  have hp := psdGramProgram_work_le kernels m GA.val hGApos
  have h1 := kernelEnvelope_le kernels m pair.dimension m m pair.dimension_le_fin le_rfl le_rfl
    (by omega : 1 ≤ max pair.dimension (max m m))
  have h2 := kernelEnvelope_le kernels m pair.dimension m pair.dimension pair.dimension_le_fin le_rfl
    pair.dimension_le_fin (by omega : 1 ≤ max pair.dimension (max m pair.dimension))
  simp only [coarseSupportProgram,work_bind,certify_work,ArithmeticKernel.program_work,work_pure,add_zero]
  change (kernels m s m).cost+((psdGramProgram kernels m GA.val hGApos).work+
    ((kernels m t m).cost+((kernels pair.dimension m m).cost+
      (kernels pair.dimension m pair.dimension).cost))) ≤ _
  dsimp [coarseSupportWorkCap]
  omega

/-- Exact, outcome-wise operation budget for the complete baseline compiler.
The only output-dependent data in this expression are the computed support
dimension and the stored sketch row counts. The matrix values never appear
in a kernel cost. -/
def fixedDepthRealizedWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) (Ck p0 : ℝ) : ℕ :=
  let S := (mainSketchProgram I g).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  (L+1)*(sketchFormationCap n m I.sketchFailure+sketchFormationCap p m I.sketchFailure)+
    coarseSupportWorkCap kernels m (S.levelA 0).1 (S.levelB 0).1+
    mainCoreWorkCap kernels I S C Ck p0

theorem fixedDepthProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (fixedDepthProgram kernels I g).work ≤ fixedDepthRealizedWorkCap kernels I g Ck p0 := by
  let S := (mainSketchProgram I g).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  have hs := mainSketchProgram_work_le I g
  have hc := coarseSupportProgram_work_bound kernels S.initialA S.initialB
    (by have hh:=I.rank_positive; have hh':=I.rank_le_core; omega)
  have hm := mainCoreProgram_work_bound kernels Ck p0 hC hp hK I S C g
  simp only [fixedDepthProgram,work_bind]
  dsimp only [S,C] at hc hm
  dsimp only [fixedDepthRealizedWorkCap]
  omega

end
end HierarchicalAbsoluteSpectral
