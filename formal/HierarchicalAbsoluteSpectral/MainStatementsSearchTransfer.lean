import HierarchicalAbsoluteSpectral.MainStatementsSearchCorrectness
import HierarchicalAbsoluteSpectral.MainThresholdFacts
import HierarchicalAbsoluteSpectral.ThresholdSelection

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

def MainNearThreshold (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (t : ℝ) : Prop :=
  ∀ ht : 0 < t, |1-orderedEigenvalue (mainThresholdView kernels I S C ⟨t,ht⟩).val
    (mainThresholdView kernels I S C ⟨t,ht⟩).property ⟨r,hr⟩| ≤ I.alpha

theorem mainIdealQuery_mass_history_good
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hsketch : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (hInertia : MainAllInertiaGood kernels I S C hr l u hl hlu samples inertias)
    (hRitz : samples ∈ mainAdaptiveRitzGood kernels I S C hr l u hl hlu) :
    thresholdQueryHistoryGood (mainIdealQuery kernels I S C hr samples)
      (mainInitializerMassTarget I S C hr) I.nearTolerance
      (MainNearThreshold kernels I S C hr) l u := by
  intro i
  dsimp only
  intro _ _
  let t := mainIdealTime kernels I S C hr l u hl hlu samples i
  have hs := mainIdealQuery_safe_at_history kernels I S hsketch C hr l u hl hlu samples inertias hInertia hRitz i
  change ThresholdDecisionSafe (orderedEigenvalue (mainThresholdView kernels I S C t).val
    (mainThresholdView kernels I S C t).property ⟨r,hr⟩) (mainRitzAccuracy I)
    (mainIdealQuery kernels I S C hr samples i t.val) at hs
  change (match mainIdealQuery kernels I S C hr samples i t.val with
    | .below => t.val ≤ mainInitializerMassTarget I S C hr
    | .above => mainInitializerMassTarget I S C hr ≤ t.val
    | .near => MainNearThreshold kernels I S C hr t.val)
  cases hd : mainIdealQuery kernels I S C hr samples i t.val with
  | below =>
    rw [hd] at hs
    exact hsketch.actual_threshold_safe_decision kernels I S C hr t.val t.property
      (mainRitzAccuracy I) .below hs
  | above =>
    rw [hd] at hs
    exact hsketch.actual_threshold_safe_decision kernels I S C hr t.val t.property
      (mainRitzAccuracy I) .above hs
  | near =>
    rw [hd] at hs
    have ht := hsketch.actual_threshold_safe_decision kernels I S C hr t.val t.property
      (mainRitzAccuracy I) .near hs
    intro ht'
    exact ht.trans (by unfold mainRitzAccuracy; nlinarith [I.alpha_positive])

theorem mainSearchProgram_correct
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hsketch : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (l u : ℝ) (hl : 0 < l)
    (hlo : l ≤ mainInitializerMassTarget I S C hr) (hhi : mainInitializerMassTarget I S C hr ≤ u)
    (hwidth : u-l ≤ (16*initializerRatio m I.singleFailure)*l)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (hInertia : MainAllInertiaGood kernels I S C hr l u hl (hlo.trans hhi) samples inertias)
    (hRitz : samples ∈ mainAdaptiveRitzGood kernels I S C hr l u hl (hlo.trans hhi)) :
    ThresholdSearchConclusion (mainInitializerMassTarget I S C hr) I.nearTolerance
      (MainNearThreshold kernels I S C hr) (mainSearchProgram kernels I S C hr samples inertias l u).eval := by
  rw [mainSearchProgram_eval_ideal kernels I S C hr l u hl (hlo.trans hhi) samples inertias hInertia]
  apply thresholdSearchIndexedValue_correct_of_trace _ _ _ _ I.nearTolerance_positive.le
    I.queryCap 0 (by omega) l u hl hlo hhi
  · have hs := (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) I.queryCap)).mp
      (leastHalvings_spec (16*initializerRatio m I.singleFailure) I.nearTolerance I.nearTolerance_positive)
    exact hwidth.trans (by nlinarith [mul_le_mul_of_nonneg_right hs hl.le])
  · exact thresholdSearchTraceGood_of_history _ _ _ _ l u
      (mainIdealQuery_mass_history_good kernels I S hsketch C hr l u hl (hlo.trans hhi)
        samples inertias hInertia hRitz) I.queryCap 0 (by omega) l u rfl

theorem mainSearchProgram_selected_facts
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hsketch : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (l u : ℝ)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (hgood : ThresholdSearchConclusion (mainInitializerMassTarget I S C hr) I.nearTolerance
      (MainNearThreshold kernels I S C hr) (mainSearchProgram kernels I S C hr samples inertias l u).eval) :
    let t := (mainSearchProgram kernels I S C hr samples inertias l u).eval.selected
    0 < t ∧ (∀ ht : 0 < t, orderedEigenvalue (mainThresholdView kernels I S C ⟨t,ht⟩).val
      (mainThresholdView kernels I S C ⟨t,ht⟩).property ⟨r,hr⟩ ≤ 1+I.alpha) ∧
      t ≤ ((1+I.nearTolerance)/(1-I.nearTolerance))*(1/(1-I.massAccuracy))*
        (tailSingularValue (I.A*I.B) r)^2 := by
  have hθ1 : I.theta ≤ 1 := I.theta_le_last.trans ((I.accuracy_bounded L le_rfl).trans (by norm_num))
  have hX0 := I.nearTolerance_positive.le
  have hX1 : I.nearTolerance < 1 := by have := I.final_budget.near_error; change I.nearTolerance ≤ _ at this; linarith
  have hratio0 : 0 ≤ (1+I.nearTolerance)/(1-I.nearTolerance) := by positivity
  have hratio : 1+I.nearTolerance ≤ (1+I.nearTolerance)/(1-I.nearTolerance) := by
    apply (le_div_iff₀ (by linarith : 0 < 1-I.nearTolerance)).mpr
    nlinarith
  cases he : (mainSearchProgram kernels I S C hr samples inertias l u).eval with
  | near t =>
    simp only [ThresholdSearchResult.selected]
    rw [he] at hgood
    refine ⟨hgood.1,?_,?_⟩
    · intro ht
      have hn := hgood.2 ht
      have hh := (abs_le.mp hn).1
      linarith
    · exact hsketch.actual_threshold_near_tail kernels I S C hr t hgood.1 (hgood.2 hgood.1)
  | bracket a b =>
    simp only [ThresholdSearchResult.selected]
    rw [he] at hgood
    have hb : 0 < b := hgood.1.trans_le (hgood.2.1.trans hgood.2.2.1)
    refine ⟨hb,?_,?_⟩
    · intro ht
      exact ((hsketch.actual_threshold_le_one_iff kernels I S C hr b ht).mpr hgood.2.2.1).trans
        (by linarith [I.alpha_positive])
    · have hu := hgood.2.2.2.2
      have hm := hsketch.initializer_mass_tail_comparison I S C hr
      have htarget0 := hsketch.initializer_target_nonneg I S C hr
      calc
        b ≤ (1+I.nearTolerance)*mainInitializerMassTarget I S C hr := hu
        _ ≤ ((1+I.nearTolerance)/(1-I.nearTolerance))*mainInitializerMassTarget I S C hr :=
          mul_le_mul_of_nonneg_right hratio htarget0
        _ ≤ ((1+I.nearTolerance)/(1-I.nearTolerance))*
            ((tailSingularValue (I.A*I.B) r)^2/(1-I.massAccuracy)) := mul_le_mul_of_nonneg_left hm.2 hratio0
        _ = _ := by ring

end
end HierarchicalAbsoluteSpectral
