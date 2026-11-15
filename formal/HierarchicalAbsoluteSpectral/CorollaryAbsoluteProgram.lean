import HierarchicalAbsoluteSpectral.CorollaryAbsoluteRank
import HierarchicalAbsoluteSpectral.MainStatementsArrays
import HierarchicalAbsoluteSpectral.MainSketchProgram
import HierarchicalAbsoluteSpectral.MainOperatorSpectral

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

/-- Original fixed-depth data and absolute tolerance, with no supplied rank. -/
structure AbsoluteProblem (n m p L : ℕ) where
  A : Matrix (Fin n) (Fin m) ℝ
  B : Matrix (Fin m) (Fin p) ℝ
  theta : ℝ
  delta : ℝ
  tolerance : ℝ
  accuracy : ℕ → ℝ
  core_positive : 1 ≤ m
  core_le_rows : m ≤ n
  core_le_cols : m ≤ p
  depth_positive : 1 ≤ L
  theta_positive : 0 < theta
  delta_positive : 0 < delta
  delta_lt_one : delta < 1
  tolerance_positive : 0 < tolerance
  accuracy_positive : ∀ j ≤ L, 0 < accuracy j
  initial_accuracy_le : accuracy 0 ≤ 1/64
  theta_le_last : theta ≤ accuracy L
  refinement_ratio : ∀ j < L, accuracy (j+1)/accuracy j ≤ 1/1024

/-- Rank one only seeds rank-independent hierarchy parameters. Each of the
at most m+1 possible attempts receives its own finite failure allocation. -/
def AbsoluteProblem.seed (I : AbsoluteProblem n m p L) : FixedProblem n m p 1 L where
  A := I.A
  B := I.B
  theta := I.theta
  delta := I.delta/((m:ℝ)+1)
  accuracy := I.accuracy
  core_le_rows := I.core_le_rows
  core_le_cols := I.core_le_cols
  rank_positive := le_rfl
  rank_le_core := I.core_positive
  depth_positive := I.depth_positive
  theta_positive := I.theta_positive
  delta_positive := div_pos I.delta_positive (by positivity)
  delta_lt_one := by
    apply (div_lt_iff₀ (by positivity : 0 < (m:ℝ)+1)).mpr
    have hm : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
    linarith [I.delta_lt_one]
  accuracy_positive := I.accuracy_positive
  initial_accuracy_le := I.initial_accuracy_le
  theta_le_last := I.theta_le_last
  refinement_ratio := I.refinement_ratio

def AbsoluteProblem.slackRank (I : AbsoluteProblem n m p L) : ℕ :=
  absoluteSlackRank I.A I.B I.tolerance I.theta I.tolerance_positive I.theta_positive.le

def absoluteThreshold (I : AbsoluteProblem n m p L) : ℝ :=
  I.tolerance^2/(1+I.theta/4)

theorem absoluteThreshold_positive (I : AbsoluteProblem n m p L) : 0 < absoluteThreshold I := by
  unfold absoluteThreshold
  exact div_pos (sq_pos_of_pos I.tolerance_positive) (by linarith [I.theta_positive])

def absoluteThresholdProgram (I : AbsoluteProblem n m p L) : ArithmeticProgram ℝ := do
  let a ← mul I.tolerance I.tolerance
  let b ← div I.theta 4
  let c ← add 1 b
  div a c

@[simp] theorem absoluteThresholdProgram_eval (I : AbsoluteProblem n m p L) :
    (absoluteThresholdProgram I).eval = absoluteThreshold I := by
  simp only [absoluteThresholdProgram,eval_bind,eval_mul,eval_div,eval_add,absoluteThreshold,pow_two]

theorem absoluteThresholdProgram_admissible (I : AbsoluteProblem n m p L) :
    (absoluteThresholdProgram I).admissible := by
  have h : 0 < 1+I.theta/4 := by linarith [I.theta_positive]
  simp [absoluteThresholdProgram,h.ne']

@[simp] theorem absoluteThresholdProgram_work (I : AbsoluteProblem n m p L) :
    (absoluteThresholdProgram I).work = 4 := by simp [absoluteThresholdProgram]

/-- Actual arbitrary-rank threshold query, including s=0. Native eigenvalues
occur only in the specifications of the existing query compiler. -/
def absolutePositiveQueryProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hs : s < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (s+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) :
    ArithmeticProgram ThresholdDecision := do
  let base ← coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))
  let bound ← (mainConditionProgram I).certify
  let ε ← (div I.alpha 100).certify
  have hε : ε.val=I.alpha/100 := ε.property
  let actions := fun b => (mainThresholdAction kernels I S C t.val base (s+1)).columnBlocks (by omega) b
  automaticKrylovQueryProgram kernels (mainThresholdOperator I S C t.val base)
    (mainThresholdOperator_isHermitian I S C t.val base) actions
    (mainSourceFactor I S C t.val base) (mainSourceAction kernels I S C t.val base (s+1))
    ⟨s,hs⟩ bound.val ε.val (by omega)
    (by rw [bound.property,mainConditionProgram_eval]; exact mainConditionBound_ge_one I)
    (by rw [hε]; exact div_pos I.alpha_positive (by norm_num))
    (by rw [hε]; have := I.final_budget.alpha_small; change I.alpha ≤ _ at this; linarith)
    I.repetitions G g

theorem absolutePositiveQueryProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hs : s < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (s+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) :
    (absolutePositiveQueryProgram kernels I S C s hs t G g).admissible := by
  simp only [absolutePositiveQueryProgram,admissible_bind,coarseBaseProgram_admissible,
    certify_admissible,mainConditionProgram_admissible,admissible_div,
    automaticKrylovQueryProgram_admissible,true_and]
  norm_num

/-- The same carried polynomial/range/output compiler at an attempted rank
s independent of the seed rank, including the empty output case. -/
def absoluteStrongThresholdProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin s → Fin C.pair.dimension → ℝ) : ArithmeticProgram (FixedRankOutput n p s) := do
  let base ← coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))
  let bound ← (mainConditionProgram I).certify
  strongProjectionOutputProgram kernels I.A I.B
    (mainCarriedAction kernels I S C t.val base s) (mainPhysicalMapAction kernels I S C t.val base s)
    bound.val I.singleFailure I.alpha hk
    (by rw [bound.property,mainConditionProgram_eval]; exact mainConditionBound_ge_one I)
    (div_pos I.delta_positive (by norm_num)) (by have := I.delta_lt_one; dsimp [FixedProblem.singleFailure]; linarith)
    I.alpha_positive (by have := I.final_budget.alpha_small; change I.alpha ≤ _ at this; linarith)
    (columnsMatrix G)

theorem absoluteStrongThresholdProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin s → Fin C.pair.dimension → ℝ) :
    (absoluteStrongThresholdProgram kernels I S C s hk t G).admissible := by
  simp only [absoluteStrongThresholdProgram,admissible_bind,coarseBaseProgram_admissible,
    certify_admissible,mainConditionProgram_admissible,strongProjectionOutputProgram_admissible,and_self]

end
end HierarchicalAbsoluteSpectral
