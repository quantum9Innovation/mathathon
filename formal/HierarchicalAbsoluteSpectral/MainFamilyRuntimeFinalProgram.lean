import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalCore
import HierarchicalAbsoluteSpectral.BaseMainTotalCost

/-! Literal operation count for the growing-depth program, with Gaussian
draws, both preparations, input reads, and every output entry included. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
variable {N m r : ℕ}

def familyFinalRestCap (I : FamilyProblem N m r) : ℕ :=
  4*m*N+N*N+(familyPreparationProgram I).work+
    6*(I.prepared.depth+1)*2^dyadicPaddingLevel N+2*r*m+
    I.prepared.fixed.queryCap*I.prepared.fixed.repetitions*((r+1)*m+2*m*m)+
    (4*I.prepared.depth+3*I.prepared.fixed.queryCap+2*I.prepared.fixed.repetitions+29)

def familyFinalPreprocessingCap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) : ℕ :=
  let S := (mainSketchProgram I.prepared.fixed g).eval
  (I.prepared.depth+1)*2*sketchFormationCap N m I.prepared.fixed.sketchFailure+
    coarseSupportWorkCap kernels m (S.levelA 0).1 (S.levelB 0).1

theorem family_final_explicit_work_of_core_envelope
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ Ck*(D:ℝ)^p0)
    (A B O Q : ℕ)
    (henv : let S := (mainSketchProgram I.prepared.fixed g).eval
      let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
      ComparatorCoreEnvelope kernels I.prepared.fixed S C Ck p0 A B O Q) :
    growingDepthExplicitWork kernels I g ≤ familyFinalRestCap I+
      familyFinalPreprocessingCap kernels I g+
      1000*(I.prepared.fixed.queryCap+1)*(I.prepared.fixed.repetitions+1)*((Q+1)*A+B+O) := by
  let S := (mainSketchProgram I.prepared.fixed g).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  have hcore := ComparatorCoreEnvelope.core_work kernels I.prepared.fixed S C Ck p0 A B O Q henv
  have hfixed := fixedDepthProgram_work_bound kernels Ck p0 hC hp hK I.prepared.fixed g
  have hexp := preparedFixedDepthExplicitWork_le kernels I.prepared.fixed g
  rw [growingDepthExplicitWork_eq]
  rw [preparedFixedDepthTotalWork_eq] at hexp
  dsimp only [fixedDepthRealizedWorkCap] at hfixed
  dsimp only [familyFinalRestCap,familyFinalPreprocessingCap]
  change mainCoreWorkCap kernels I.prepared.fixed S C Ck p0 ≤ _ at hcore
  change (fixedDepthProgram kernels I.prepared.fixed g).work ≤
    (I.prepared.depth+1)*(sketchFormationCap N m I.prepared.fixed.sketchFailure+
      sketchFormationCap N m I.prepared.fixed.sketchFailure)+
      coarseSupportWorkCap kernels m (S.levelA 0).1 (S.levelB 0).1+
      mainCoreWorkCap kernels I.prepared.fixed S C Ck p0 at hfixed
  dsimp only [S] at hcore hfixed
  nlinarith only [hexp,hfixed,hcore]

end
end HierarchicalAbsoluteSpectral
