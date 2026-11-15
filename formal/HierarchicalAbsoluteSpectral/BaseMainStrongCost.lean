import HierarchicalAbsoluteSpectral.BaseMainProgramCostOutput

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}
attribute [local irreducible] strongProjectionOutputProgram

def mainStrongDegree (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hk : 1 ≤ C.pair.dimension) : ℕ :=
  strongGaussianDegree C.pair.dimension (mainConditionBound I) I.singleFailure I.alpha hk
    (mainConditionBound_ge_one I) (div_pos I.delta_positive (by norm_num))
    (by have hh := I.delta_lt_one; dsimp [FixedProblem.singleFailure]; linarith)
    I.alpha_positive (by have hh := I.final_budget.alpha_small; change I.alpha ≤ _ at hh; linarith)

def mainStrongOutputCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hk : 1 ≤ C.pair.dimension) : ℕ :=
  let v := mainStrongDegree I S C hk
  4*v+14+(9+3*v+(v+1)*(mainCarriedActionCost kernels I S C r+6*C.pair.dimension*r)+
    C.pair.dimension*r+(kernels n m r).cost+(kernels m C.pair.dimension r).cost+
    (kernels C.pair.dimension C.pair.dimension r).cost+exactRangeWorkCap kernels n r)+
    projectionOutputWorkCap kernels n m p r

def mainStrongWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hk : 1 ≤ C.pair.dimension) : ℕ :=
  baseConstructionCost kernels C.pair.dimension (I.accuracy 0) (I.accuracy_positive 0 (by omega))+
    2*C.pair.dimension*C.pair.dimension+7+mainStrongOutputCap kernels I S C hk

theorem mainStrongThresholdProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) :
    (mainStrongThresholdProgram kernels I S C hk t G).work ≤ mainStrongWorkCap kernels I S C hk := by
  let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
  let bound := (mainConditionProgram I).certify.eval
  have hb : bound.val=mainConditionBound I := by
    simp only [bound,certify_eval,mainConditionProgram_eval]
  have hU : 1 ≤ bound.val := by rw [hb]; exact mainConditionBound_ge_one I
  have hβ : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
  have hβ1 : I.singleFailure ≤ 1 := by
    have hh := I.delta_lt_one
    dsimp [FixedProblem.singleFailure]
    linarith
  have hα1 : I.alpha ≤ 1 := by
    have hh := I.final_budget.alpha_small
    change I.alpha ≤ _ at hh
    linarith
  have hs := strongProjectionOutputProgram_work_bound kernels I.A I.B
    (mainCarriedAction kernels I S C t.val base r) (mainPhysicalMapAction kernels I S C t.val base r)
    bound.val I.singleFailure I.alpha hk hU hβ hβ1 I.alpha_positive hα1 (columnsMatrix G)
  have hv : strongGaussianDegree C.pair.dimension bound.val I.singleFailure I.alpha
      hk hU hβ hβ1 I.alpha_positive hα1=mainStrongDegree I S C hk := by
    dsimp [mainStrongDegree]
    congr 1
  change _ ≤ 4*strongGaussianDegree C.pair.dimension bound.val I.singleFailure I.alpha
      hk hU hβ hβ1 I.alpha_positive hα1+14+
    (9+3*strongGaussianDegree C.pair.dimension bound.val I.singleFailure I.alpha
      hk hU hβ hβ1 I.alpha_positive hα1+
      (strongGaussianDegree C.pair.dimension bound.val I.singleFailure I.alpha
        hk hU hβ hβ1 I.alpha_positive hα1+1)*
        ((mainCarriedAction kernels I S C t.val base r).cost+6*C.pair.dimension*r)+
      C.pair.dimension*r+(mainPhysicalMapAction kernels I S C t.val base r).cost+
      exactRangeWorkCap kernels n r)+projectionOutputWorkCap kernels n m p r at hs
  rw [hv,mainCarriedAction_cost,mainPhysicalMapAction_cost] at hs
  have hs' : (strongProjectionOutputProgram kernels I.A I.B
      (mainCarriedAction kernels I S C t.val base r) (mainPhysicalMapAction kernels I S C t.val base r)
      bound.val I.singleFailure I.alpha hk hU hβ hβ1 I.alpha_positive hα1 (columnsMatrix G)).work ≤
      mainStrongOutputCap kernels I S C hk := by
    dsimp [mainStrongOutputCap]
    omega
  simp only [mainStrongThresholdProgram,work_bind,coarseBaseProgram_work,certify_work,
    mainConditionProgram_work]
  dsimp only [base,bound] at hs'
  dsimp [mainStrongWorkCap]
  omega

def mainExactOutputWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) : ℕ :=
  Finset.univ.sup (fun w : Fin (r+1) =>
    (kernels n m w.val).cost+(kernels m C.pair.dimension w.val).cost+
      exactRangeWorkCap kernels n w.val+projectionOutputWorkCap kernels n m p r)

theorem mainExactOutputProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    {w : ℕ} (U : Matrix (Fin C.pair.dimension) (Fin w) ℝ) (hw : w ≤ r) :
    (exactPhysicalOutputProgram kernels I.A I.B (mainSupportAction kernels I S C w) U hw).work ≤
      mainExactOutputWorkCap kernels I S C := by
  have hh := exactPhysicalOutputProgram_work_bound kernels I.A I.B (mainSupportAction kernels I S C w) U hw
  rw [mainSupportAction_cost] at hh
  exact hh.trans (Finset.le_sup
    (f := fun w : Fin (r+1) => (kernels n m w.val).cost+(kernels m C.pair.dimension w.val).cost+
      exactRangeWorkCap kernels n w.val+projectionOutputWorkCap kernels n m p r)
      (Finset.mem_univ (⟨w,by omega⟩ : Fin (r+1))))

theorem mainSupportExactOutputProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : C.pair.dimension ≤ r) :
    (supportExactOutputProgram kernels I.A I.B (mainSupportAction kernels I S C _) hr).work ≤
      mainExactOutputWorkCap kernels I S C :=
  mainExactOutputProgram_work_bound kernels I S C 1 hr

end
end HierarchicalAbsoluteSpectral
