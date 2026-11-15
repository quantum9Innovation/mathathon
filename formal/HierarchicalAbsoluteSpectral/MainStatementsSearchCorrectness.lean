import HierarchicalAbsoluteSpectral.MainStatementsQueryCorrectness

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

def mainActualQuery (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) :
    Fin I.queryCap → ℝ → ArithmeticProgram ThresholdDecision :=
  positiveThresholdQuery (fun i t => mainPositiveQueryProgram kernels I S C hr t (samples i) (inertias i))

def mainIdealTime (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (i : Fin I.queryCap) : {t : ℝ // 0 < t} :=
  idealRitzThresholdParameter kernels (mainThresholdView kernels I S C) (mainSourceView kernels I S C)
    (mainKrylovDegree I S C hr) ⟨r,hr⟩ (mainRitzAccuracy I) I.nearTolerance l u hl hlu samples i

def MainAllInertiaGood (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) : Prop :=
  ∀ i, MainQueryInertiaGood kernels I S C hr (mainIdealTime kernels I S C hr l u hl hlu samples i)
    (samples i) (inertias i)

theorem mainActualQuery_agrees_at_ideal_time
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (hgood : MainAllInertiaGood kernels I S C hr l u hl hlu samples inertias) (i : Fin I.queryCap) :
    (mainActualQuery kernels I S C hr samples inertias i
      (mainIdealTime kernels I S C hr l u hl hlu samples i).val).eval =
    mainIdealQuery kernels I S C hr samples i (mainIdealTime kernels I S C hr l u hl hlu samples i).val := by
  rw [show (mainActualQuery kernels I S C hr samples inertias i
      (mainIdealTime kernels I S C hr l u hl hlu samples i).val).eval =
      (mainPositiveQueryProgram kernels I S C hr (mainIdealTime kernels I S C hr l u hl hlu samples i)
        (samples i) (inertias i)).eval from positiveThresholdQuery_eval_pos _ _ _
          (mainIdealTime kernels I S C hr l u hl hlu samples i).property]
  exact mainPositiveQueryProgram_eq_ideal kernels I S C hr _ _ _ (hgood i)

theorem mainActualQuery_history_agreement
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (hgood : MainAllInertiaGood kernels I S C hr l u hl hlu samples inertias) :
    thresholdQueryHistoryAgree (fun i t => (mainActualQuery kernels I S C hr samples inertias i t).eval)
      (mainIdealQuery kernels I S C hr samples) I.nearTolerance l u := by
  intro i
  dsimp only
  intro _ _
  exact mainActualQuery_agrees_at_ideal_time kernels I S C hr l u hl hlu samples inertias hgood i

def mainSearchProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (l u : ℝ) : ArithmeticProgram ThresholdSearchResult :=
  thresholdSearchCapped (16*initializerRatio m I.singleFailure) I.nearTolerance I.nearTolerance_positive
    (mainActualQuery kernels I S C hr samples inertias) l u

theorem mainSearchProgram_eval_ideal
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (hgood : MainAllInertiaGood kernels I S C hr l u hl hlu samples inertias) :
    (mainSearchProgram kernels I S C hr samples inertias l u).eval =
      thresholdSearchIndexedValue (mainIdealQuery kernels I S C hr samples)
        I.nearTolerance I.queryCap 0 (by omega) l u := by
  rw [mainSearchProgram,thresholdSearchCapped_eval,thresholdSearchIndexed_eval]
  exact thresholdSearchIndexedValue_eq_of_history _ _ I.nearTolerance l u
    (mainActualQuery_history_agreement kernels I S C hr l u hl hlu samples inertias hgood)

theorem mainIdealQuery_safe_at_history
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hsketch : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (hInertia : MainAllInertiaGood kernels I S C hr l u hl hlu samples inertias)
    (hRitz : samples ∈ mainAdaptiveRitzGood kernels I S C hr l u hl hlu) (i : Fin I.queryCap) :
    let t := mainIdealTime kernels I S C hr l u hl hlu samples i
    ThresholdDecisionSafe (orderedEigenvalue (mainThresholdView kernels I S C t).val
      (mainThresholdView kernels I S C t).property ⟨r,hr⟩) (mainRitzAccuracy I)
      (mainIdealQuery kernels I S C hr samples i t.val) := by
  let t := mainIdealTime kernels I S C hr l u hl hlu samples i
  have hritz : (t,samples i) ∉ mainRepeatedRitzBad kernels I S C hr := Set.mem_iInter.mp hRitz i
  have hs := mainPositiveQueryProgram_safe kernels I S hsketch C hr t (samples i) (inertias i) (hInertia i) hritz
  rw [mainPositiveQueryProgram_eq_ideal kernels I S C hr t (samples i) (inertias i) (hInertia i)] at hs
  exact hs

end
end HierarchicalAbsoluteSpectral
