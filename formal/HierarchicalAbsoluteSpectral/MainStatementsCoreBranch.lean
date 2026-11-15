import HierarchicalAbsoluteSpectral.MainStatementsAlgorithm
import HierarchicalAbsoluteSpectral.MainStatementsSearchCorrectness
import HierarchicalAbsoluteSpectral.MainInitializerCorrectness
import HierarchicalAbsoluteSpectral.MainAdaptiveInitialEndpoints
import HierarchicalAbsoluteSpectral.MainStrongProbabilityProgram

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

theorem thresholdSearchCapped_cast_eq (x y ε : ℝ) (hε : 0 < ε) (hxy : x=y)
    (query : Fin (leastHalvings y ε hε) → ℝ → ArithmeticProgram ThresholdDecision)
    (hcap : leastHalvings x ε hε=leastHalvings y ε hε) (l u : ℝ) :
    thresholdSearchCapped x ε hε (fun i => query (Fin.cast hcap i)) l u=
      thresholdSearchCapped y ε hε query l u := by
  subst y
  rfl

def mainCoreIdealSelected (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (initial : Fin r → Fin C.pair.dimension → ℝ)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ) : ℝ :=
  (thresholdSearchIndexedValue (mainIdealQuery kernels I S C hr samples)
    I.nearTolerance I.queryCap 0 (by omega)
    (mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix initial) I.singleFailure)
    (mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix initial))).selected

theorem mainCoreIdealSelected_positive (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (initial : Fin r → Fin C.pair.dimension → ℝ)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ) :
    0 < mainCoreIdealSelected kernels I S C hr initial samples :=
  thresholdSearchIndexedValue_selected_positive _ _ _ _ _ _ _
    (mainInitializerLowerEndpoint_pos kernels _ _ _ (by omega) I.singleFailure_positive)
    (mainInitializerEndpoints_ordered kernels _ _ _ (by omega) I.singleFailure_positive)

def mainFinishProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (G : Fin r → Fin C.pair.dimension → ℝ)
    (t : ℝ) : ArithmeticProgram (FixedRankOutput n p r) :=
  .branch t 0 (fun _ => .pure (zeroFixedRankOutput n p r))
    (fun ht => mainStrongThresholdProgram kernels I S C hk ⟨t,lt_of_not_ge ht⟩ G)

theorem mainFinishProgram_eval_pos (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (G : Fin r → Fin C.pair.dimension → ℝ)
    (t : ℝ) (ht : 0 < t) :
    (mainFinishProgram kernels I S C hk G t).eval=
      (mainStrongThresholdProgram kernels I S C hk ⟨t,ht⟩ G).eval := by
  simp only [mainFinishProgram,ArithmeticProgram.eval,dif_neg (not_le_of_gt ht)]

theorem mainCoreProgram_bracket_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (g : MainRandomTape I) (lower upper : ℝ)
    (hresult : (gaussianInitializerProgram kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure).eval.result=.bracket lower upper) :
    (mainCoreProgram kernels I S C g).eval=
      (do
        let result ← mainSearchProgram kernels I S C hr (mainQueryArray I S C g)
          (mainInertiaArray I S C g) (lower/4) (4*upper)
        mainFinishProgram kernels I S C (by omega) (mainStrongArray I S C g) result.selected).eval := by
  unfold mainCoreProgram
  rw [dif_neg (not_le_of_gt hr),eval_bind,hresult]
  simp only [eval_bind,eval_div,eval_mul]
  let ratio := (initializerRatioProgram m I.singleFailure).certify.eval
  let budget := (mul 16 ratio.val).certify.eval
  have hb : budget.val=16*initializerRatio m I.singleFailure := by
    change (mul 16 (initializerRatioProgram m I.singleFailure).certify.eval.val).certify.eval.val=_
    rw [certify_eval,eval_mul,certify_eval,initializerRatioProgram_eval]
  have hc : leastHalvings budget.val I.nearTolerance I.nearTolerance_positive=I.queryCap := by
    rw [hb]
    rfl
  change (mainFinishProgram kernels I S C (by omega) (mainStrongArray I S C g)
    (thresholdSearchCapped budget.val I.nearTolerance I.nearTolerance_positive
      (fun i => mainActualQuery kernels I S C hr (mainQueryArray I S C g)
        (mainInertiaArray I S C g) (Fin.cast hc i)) (lower/4) (4*upper)).eval.selected).eval=_
  rw [thresholdSearchCapped_cast_eq budget.val (16*initializerRatio m I.singleFailure)
    I.nearTolerance I.nearTolerance_positive hb
    (mainActualQuery kernels I S C hr (mainQueryArray I S C g) (mainInertiaArray I S C g)) hc]
  rfl

end
end HierarchicalAbsoluteSpectral
