import HierarchicalAbsoluteSpectral.FiniteHierarchy
import HierarchicalAbsoluteSpectral.StrongFilterFinalBudget
import HierarchicalAbsoluteSpectral.ProbabilityInitializer
import HierarchicalAbsoluteSpectral.ProbabilityEmbeddingPadding

/-! Original fixed-depth inputs and one finite independent Gaussian tape.
Only manuscript input conditions occur in `FixedProblem`; derived tolerances,
query caps and repetition counts are definitions, rather than extra hypotheses. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
variable {n m p r L : ℕ}

structure FixedProblem (n m p r L : ℕ) where
  A : Matrix (Fin n) (Fin m) ℝ
  B : Matrix (Fin m) (Fin p) ℝ
  theta : ℝ
  delta : ℝ
  accuracy : ℕ → ℝ
  core_le_rows : m ≤ n
  core_le_cols : m ≤ p
  rank_positive : 1 ≤ r
  rank_le_core : r ≤ m
  depth_positive : 1 ≤ L
  theta_positive : 0 < theta
  delta_positive : 0 < delta
  delta_lt_one : delta < 1
  accuracy_positive : ∀ j ≤ L, 0 < accuracy j
  initial_accuracy_le : accuracy 0 ≤ 1/64
  theta_le_last : theta ≤ accuracy L
  refinement_ratio : ∀ j < L, accuracy (j+1)/accuracy j ≤ 1/1024

namespace FixedProblem

def alpha (I : FixedProblem n m p r L) : ℝ := literalFinalAlpha (hierarchyConstant L) (I.accuracy L) I.theta
def massAccuracy (I : FixedProblem n m p r L) : ℝ := literalFinalMass (hierarchyConstant L) I.theta
def nearTolerance (I : FixedProblem n m p r L) : ℝ := literalFinalX (hierarchyConstant L) (I.accuracy L) I.theta
def singleFailure (I : FixedProblem n m p r L) : ℝ := I.delta/20
def sketchFailure (I : FixedProblem n m p r L) : ℝ := I.delta/(20*((L:ℝ)+1))

theorem final_budget (I : FixedProblem n m p r L) :
    LiteralFinalBudget (hierarchyConstant L) (I.accuracy L) I.theta :=
  literal_final_tolerance_budget _ _ _ (hierarchyConstant_ge_one L)
    (I.accuracy_positive L le_rfl) I.theta_positive I.theta_le_last

theorem alpha_positive (I : FixedProblem n m p r L) : 0<I.alpha := I.final_budget.alpha_positive
theorem nearTolerance_positive (I : FixedProblem n m p r L) : 0<I.nearTolerance := by
  have hC := hierarchyConstant_ge_one L
  have hh := I.accuracy_positive L le_rfl
  have ha := I.alpha_positive
  unfold nearTolerance literalFinalX
  change 0<4*hierarchyConstant L*I.alpha*I.accuracy L
  positivity

def queryCap (I : FixedProblem n m p r L) : ℕ :=
  leastHalvings (16*initializerRatio m I.singleFailure) I.nearTolerance I.nearTolerance_positive

def queryFailure (I : FixedProblem n m p r L) : ℝ := I.delta/(20*((I.queryCap:ℝ)+1))
theorem queryFailure_positive (I : FixedProblem n m p r L) : 0<I.queryFailure := by
  unfold queryFailure
  exact div_pos I.delta_positive (by positivity)

def repetitions (I : FixedProblem n m p r L) : ℕ :=
  leastHalvings 1 I.queryFailure I.queryFailure_positive

end FixedProblem

/-- Every coordinate is sampled independently once. Counters index fresh
arrays even when the next threshold is chosen from previous query results. -/
inductive MainGaussianIndex (n m p r L cap repetitions : ℕ) where
  | sketchLeft (level : Fin (L+1)) (part : Fin 3) (coordinate : Fin (2^dyadicPaddingLevel n))
  | sketchRight (level : Fin (L+1)) (part : Fin 3) (coordinate : Fin (2^dyadicPaddingLevel p))
  | initializer (column : Fin r) (row : Fin m)
  | query (number : Fin cap) (trial : Fin repetitions) (column : Fin (r+1)) (row : Fin m)
  | inertia (number : Fin cap) (trial : Fin repetitions) (test : Fin 2) (coordinate : Fin (m*m))
  | strong (column : Fin r) (row : Fin m)
  deriving Fintype, DecidableEq

abbrev MainRandomTape (I : FixedProblem n m p r L) :=
  MainGaussianIndex n m p r L I.queryCap I.repetitions → ℝ

def mainRandomLaw (I : FixedProblem n m p r L) : Measure (MainRandomTape I) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance mainRandomLaw_isProbability (I : FixedProblem n m p r L) :
    IsProbabilityMeasure (mainRandomLaw I) := by unfold mainRandomLaw; infer_instance

end
end HierarchicalAbsoluteSpectral
