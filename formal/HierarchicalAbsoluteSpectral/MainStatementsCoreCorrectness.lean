import HierarchicalAbsoluteSpectral.MainStatementsCoreBranch
import HierarchicalAbsoluteSpectral.MainStatementsSearchTransfer

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
open scoped Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

def MainCoreSearchGood (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (initial : Fin r → Fin C.pair.dimension → ℝ)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) : Prop :=
  let l := mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix initial) I.singleFailure
  let u := mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix initial)
  let hl := mainInitializerLowerEndpoint_pos kernels C.rightGram (columnsMatrix initial)
    I.singleFailure (by omega) I.singleFailure_positive
  let hlu := mainInitializerEndpoints_ordered kernels C.rightGram (columnsMatrix initial)
    I.singleFailure (by omega) I.singleFailure_positive
  samples ∈ mainAdaptiveRitzGood kernels I S C hr l u hl hlu ∧
    MainAllInertiaGood kernels I S C hr l u hl hlu samples inertias

theorem mainCore_bracket_selected_facts
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension)
    (initial : Fin r → Fin C.pair.dimension → ℝ)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (lower upper : ℝ)
    (hresult : (gaussianInitializerProgram kernels C.rightGram (columnsMatrix initial) I.singleFailure).eval.result =
      .bracket lower upper)
    (hInit : initial ∈ mainInitializerScalarGood kernels I S C hr)
    (hSearch : MainCoreSearchGood kernels I S C hr initial samples inertias) :
    let t := mainCoreIdealSelected kernels I S C hr initial samples
    ∀ ht : 0 < t,
      orderedEigenvalue (mainThresholdView kernels I S C ⟨t,ht⟩).val
        (mainThresholdView kernels I S C ⟨t,ht⟩).property ⟨r,hr⟩ ≤ 1+I.alpha ∧
      t ≤ ((1+I.nearTolerance)/(1-I.nearTolerance))*(1/(1-I.massAccuracy))*
        (tailSingularValue (I.A*I.B) r)^2 := by
  let l := mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix initial) I.singleFailure
  let u := mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix initial)
  have he := mainInitializerEndpoints_eq_of_bracket kernels C.rightGram
    (columnsMatrix initial) I.singleFailure lower upper hresult
  have hb := hg.initializer_positive_bracket kernels I S C hr (columnsMatrix initial)
    lower upper hresult hInit
  have hl : 0 < l := by change 0 < mainInitializerLowerEndpoint _ _ _ _; rw [he.1]; exact hb.1
  have hlo : l ≤ mainInitializerMassTarget I S C hr := by change mainInitializerLowerEndpoint _ _ _ _ ≤ _; rw [he.1]; exact hb.2.1
  have hhi : mainInitializerMassTarget I S C hr ≤ u := by change _ ≤ mainInitializerUpperEndpoint _ _ _; rw [he.2]; exact hb.2.2.1
  have hwidth : u-l ≤ (16*initializerRatio m I.singleFailure)*l := by
    have hw := (div_le_iff₀ hb.1).mp hb.2.2.2.2
    change mainInitializerUpperEndpoint _ _ _-mainInitializerLowerEndpoint _ _ _ _ ≤
      (16*initializerRatio m I.singleFailure)*mainInitializerLowerEndpoint _ _ _ _
    rw [he.1,he.2]
    linarith
  have hc := mainSearchProgram_correct kernels I S hg C hr l u hl hlo hhi hwidth samples inertias
    hSearch.2 hSearch.1
  have hf := mainSearchProgram_selected_facts kernels I S hg C hr l u samples inertias hc
  have heval := mainSearchProgram_eval_ideal kernels I S C hr l u hl (hlo.trans hhi) samples inertias hSearch.2
  have hselected : (mainSearchProgram kernels I S C hr samples inertias l u).eval.selected =
      mainCoreIdealSelected kernels I S C hr initial samples := congrArg ThresholdSearchResult.selected heval
  rw [hselected] at hf
  exact fun ht => ⟨hf.2.1 ht,hf.2.2⟩

theorem mainCoreSelected_facts
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension)
    (initial : Fin r → Fin C.pair.dimension → ℝ)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (hInit : initial ∈ mainInitializerScalarGood kernels I S C hr)
    (hSearch : MainCoreSearchGood kernels I S C hr initial samples inertias)
    (hpositive : 0 < (gaussianInitializerProgram kernels C.rightGram (columnsMatrix initial) I.singleFailure).eval.value) :
    let t := mainCoreIdealSelected kernels I S C hr initial samples
    ∀ ht : 0 < t,
      orderedEigenvalue (mainThresholdView kernels I S C ⟨t,ht⟩).val
        (mainThresholdView kernels I S C ⟨t,ht⟩).property ⟨r,hr⟩ ≤ 1+I.alpha ∧
      t ≤ ((1+I.nearTolerance)/(1-I.nearTolerance))*(1/(1-I.massAccuracy))*
        (tailSingularValue (I.A*I.B) r)^2 := by
  let out := (gaussianInitializerProgram kernels C.rightGram (columnsMatrix initial) I.singleFailure).eval
  have hb : out.result = .bracket (out.value/initializerRatio C.pair.dimension I.singleFailure) out.value := by
    rw [out.result_eq,if_neg (not_le_of_gt hpositive)]
  exact mainCore_bracket_selected_facts kernels I S hg C hr initial samples inertias _ _ hb hInit hSearch

theorem mainCoreProgram_bracket_error
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (g : MainRandomTape I) (lower upper : ℝ)
    (hresult : (gaussianInitializerProgram kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure).eval.result = .bracket lower upper)
    (hSearch : MainCoreSearchGood kernels I S C hr (mainInitializerArray I S C g)
      (mainQueryArray I S C g) (mainInertiaArray I S C g))
    (hStrong : let t := mainCoreIdealSelected kernels I S C hr (mainInitializerArray I S C g) (mainQueryArray I S C g)
      ‖I.A*I.B-(mainStrongThresholdProgram kernels I S C (by omega)
        ⟨t,mainCoreIdealSelected_positive kernels I S C hr _ _⟩ (mainStrongArray I S C g)).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r) :
    ‖I.A*I.B-(mainCoreProgram kernels I S C g).eval.product‖ ≤
      (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  have he := mainInitializerEndpoints_eq_of_bracket kernels C.rightGram
    (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure lower upper hresult
  rw [mainCoreProgram_bracket_eval kernels I S C hr g lower upper hresult,eval_bind]
  have heval := mainSearchProgram_eval_ideal kernels I S C hr
    (mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure)
    (mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix (mainInitializerArray I S C g)))
    (mainInitializerLowerEndpoint_pos kernels _ _ _ (by omega) I.singleFailure_positive)
    (mainInitializerEndpoints_ordered kernels _ _ _ (by omega) I.singleFailure_positive)
    (mainQueryArray I S C g) (mainInertiaArray I S C g) hSearch.2
  have hselected : (mainSearchProgram kernels I S C hr (mainQueryArray I S C g)
      (mainInertiaArray I S C g) (lower/4) (4*upper)).eval.selected =
      mainCoreIdealSelected kernels I S C hr (mainInitializerArray I S C g) (mainQueryArray I S C g) := by
    rw [← he.1,← he.2]
    exact congrArg ThresholdSearchResult.selected heval
  rw [hselected,mainFinishProgram_eval_pos _ _ _ _ _ _ _
    (mainCoreIdealSelected_positive kernels I S C hr _ _)]
  exact hStrong

theorem mainCoreProgram_error_of_events
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (g : MainRandomTape I)
    (hInit : mainInitializerArray I S C g ∈ mainInitializerScalarGood kernels I S C hr)
    (hSearch : MainCoreSearchGood kernels I S C hr (mainInitializerArray I S C g)
      (mainQueryArray I S C g) (mainInertiaArray I S C g))
    (hStrong : 0 < (gaussianInitializerProgram kernels C.rightGram
        (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure).eval.value →
      let t := mainCoreIdealSelected kernels I S C hr (mainInitializerArray I S C g) (mainQueryArray I S C g)
      ‖I.A*I.B-(mainStrongThresholdProgram kernels I S C (by omega)
        ⟨t,mainCoreIdealSelected_positive kernels I S C hr _ _⟩ (mainStrongArray I S C g)).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r) :
    ‖I.A*I.B-(mainCoreProgram kernels I S C g).eval.product‖ ≤
      (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  cases hresult : (gaussianInitializerProgram kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure).eval.result with
  | exact =>
    rw [hg.mainCoreProgram_exact_of_initializer_exact kernels I S C g hresult,sub_self,norm_zero]
    exact mul_nonneg (by linarith [I.theta_positive]) (tailSingularValue_nonneg _ _)
  | bracket lower upper =>
    have hp := ((gaussianInitializerProgram kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure).eval.bracket_values hresult).1
    exact mainCoreProgram_bracket_error kernels I S C hr g lower upper hresult hSearch (hStrong hp)

end
end HierarchicalAbsoluteSpectral
