import HierarchicalAbsoluteSpectral.MainStatementsRitzProbability
import HierarchicalAbsoluteSpectral.ProbabilityJointInertiaProgram
import HierarchicalAbsoluteSpectral.ThresholdMassDecision

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

theorem mainPositiveQueryProgram_eval_repeated
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) :
    (mainPositiveQueryProgram kernels I S C hr t G g).eval =
      (repeatedKrylovQueryProgram kernels (mainThresholdView kernels I S C t).val
        (mainThresholdView kernels I S C t).property
        (fun b => (mainThresholdAction kernels I S C t.val (mainBaseAt kernels I S C t) (r+1)).columnBlocks (by omega) b)
        (mainKrylovDegree I S C hr) (mainSourceView kernels I S C t)
        (mainSourceAction kernels I S C t.val (mainBaseAt kernels I S C t) (r+1))
        ⟨r,hr⟩ (mainRitzAccuracy I) I.repetitions G g).eval := by
  simp only [mainPositiveQueryProgram,eval_bind]
  simp only [certify_eval,mainConditionProgram_eval,eval_div]
  exact automaticKrylovQueryProgram_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

def mainTrialRitzMatrix (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin (r+1) → Fin C.pair.dimension → ℝ) : Core C.pair.dimension :=
  krylovRitzFixedMatrix kernels (mainThresholdView kernels I S C t).val
    (mainKrylovDegree I S C hr) ((mainSourceView kernels I S C t)ᵀ*columnsMatrix G)

def MainQueryInertiaGood (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) : Prop :=
  ∀ trial, jointInertiaGood (mainTrialRitzMatrix kernels I S C hr t (G trial)-(1:ℝ) • (1 : Core C.pair.dimension)) (g trial 0) ∧
    jointInertiaGood (mainTrialRitzMatrix kernels I S C hr t (G trial)-
      (1-2*mainRitzAccuracy I) • (1 : Core C.pair.dimension)) (g trial 1)

theorem mainPositiveQueryProgram_eq_ideal
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (hg : MainQueryInertiaGood kernels I S C hr t G g) :
    (mainPositiveQueryProgram kernels I S C hr t G g).eval =
      positiveRitzDecision kernels (mainThresholdView kernels I S C) (mainSourceView kernels I S C)
        (mainKrylovDegree I S C hr) ⟨r,hr⟩ (mainRitzAccuracy I) G t.val := by
  rw [mainPositiveQueryProgram_eval_repeated]
  dsimp only [mainThresholdView,mainSourceView]
  rw [repeatedKrylovQueryProgram_eq_of_success kernels
    (mainThresholdOperator I S C t.val (mainBaseAt kernels I S C t))
    (mainThresholdOperator_isHermitian I S C t.val _)
    (fun b => (mainThresholdAction kernels I S C t.val (mainBaseAt kernels I S C t) (r+1)).columnBlocks (by omega) b)
    (mainKrylovDegree I S C hr) (mainSourceFactor I S C t.val (mainBaseAt kernels I S C t))
    (mainSourceAction kernels I S C t.val (mainBaseAt kernels I S C t) (r+1))
    ⟨r,hr⟩ (mainRitzAccuracy I) I.repetitions G g (by
    intro trial
    apply gaussianKrylovRitzTestsProgram_success_of_polynomial_events
    · exact jointInertiaGood_polynomial_event _ _ (hg trial).1
    · exact jointInertiaGood_polynomial_event _ _ (hg trial).2)]
  simp only [positiveRitzDecision,dif_pos t.property]
  congr 1
  funext trial
  exact (gaussianRitzObservable_eq_computed kernels _ _ _ _ _ _ _).symm

theorem mainPositiveQueryProgram_safe
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hsketch : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (hg : MainQueryInertiaGood kernels I S C hr t G g)
    (hritz : (t,G) ∉ mainRepeatedRitzBad kernels I S C hr) :
    ThresholdDecisionSafe (orderedEigenvalue (mainThresholdView kernels I S C t).val
      (mainThresholdView kernels I S C t).property ⟨r,hr⟩) (mainRitzAccuracy I)
      (mainPositiveQueryProgram kernels I S C hr t G g).eval := by
  rw [mainPositiveQueryProgram_eq_ideal kernels I S C hr t G g hg]
  simp only [positiveRitzDecision,dif_pos t.property]
  have hT := (hsketch.actual_threshold_bounds kernels I S C t.val t.property).1
  apply thresholdDecision_safe _ _ _ (orderedEigenvalue_nonneg _ hT ⟨r,hr⟩)
    (mainRitzAccuracy_positive I) (by
      have hh := I.final_budget.alpha_small
      change I.alpha ≤ _ at hh
      unfold mainRitzAccuracy
      linarith)
  · intro trial
    dsimp only [mainThresholdView,mainSourceView]
    rw [gaussianRitzObservable_eq_computed kernels _ _
      (fun b => mainThresholdAction kernels I S C t.val (mainBaseAt kernels I S C t) b)]
    exact computedKrylovRitzValue_always_safe kernels _ hT _ _ _ _ _
  · change ¬ ∀ trial, gaussianRitzObservable kernels (mainKrylovDegree I S C hr) ⟨r,hr⟩
      ((mainThresholdView kernels I S C t,mainSourceView kernels I S C t),G trial) < _ at hritz
    push_neg at hritz
    exact hritz

end
end HierarchicalAbsoluteSpectral
