import HierarchicalAbsoluteSpectral.MainStatementsAlgorithm
import HierarchicalAbsoluteSpectral.MainPreparedProgram
import HierarchicalAbsoluteSpectral.MainSketchProbability
import HierarchicalAbsoluteSpectral.RuntimeFamilyOptimization

/-!
Executable comparators for the optimized example.  The constant-distortion
comparator is the finite fixed-depth algorithm at two fixed accuracies.  The
Gram comparator forms the true two Grams, extracts their exact support, and
then calls the same finite core algorithm on exact stored factors.  In
particular, neither comparator has a singular-value or Ritz oracle.
-/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

/-- All three optimized constants are computed with a single positive
scalar square root and field instructions. -/
def optimizedConstantsProgram : ArithmeticProgram (ℝ × ℝ × ℝ) := do
  let root ← sqrt 5
  let triple ← mul 3 root
  let numerator ← sub triple 5
  let d ← div numerator 10
  let alpha ← div numerator 2
  let savingNumerator ← sub 7 triple
  let saving ← div savingNumerator 8
  .pure (d,alpha,saving)

@[simp] theorem optimizedConstantsProgram_eval :
    optimizedConstantsProgram.eval = (dStar,alphaStar,savingStar) := by
  simp [optimizedConstantsProgram,dStar,alphaStar,savingStar]

@[simp] theorem optimizedConstantsProgram_work : optimizedConstantsProgram.work = 7 := by
  simp [optimizedConstantsProgram]

theorem optimizedConstantsProgram_admissible : optimizedConstantsProgram.admissible := by
  norm_num [optimizedConstantsProgram]

def comparatorAccuracy (j : ℕ) : ℝ :=
  if j=0 then 1/1024 else 1/1048576

@[simp] theorem comparatorAccuracy_zero : comparatorAccuracy 0 = 1/1024 := by
  norm_num [comparatorAccuracy]

@[simp] theorem comparatorAccuracy_one : comparatorAccuracy 1 = 1/1048576 := by
  norm_num [comparatorAccuracy]

theorem comparatorAccuracy_pos (j : ℕ) : 0 < comparatorAccuracy j := by
  unfold comparatorAccuracy
  split_ifs <;> norm_num

/-- A scalar comparison caps the requested accuracy by the fixed final
distortion.  Thus both comparators are finite for every positive accuracy. -/
def comparatorThetaProgram (theta : ℝ) : ArithmeticProgram ℝ :=
  .branch theta (1/1048576) (fun _ => .pure theta) (fun _ => .pure (1/1048576))

@[simp] theorem comparatorThetaProgram_eval (theta : ℝ) :
    (comparatorThetaProgram theta).eval = min theta (1/1048576) := by
  simp only [comparatorThetaProgram,ArithmeticProgram.eval]
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

@[simp] theorem comparatorThetaProgram_work (theta : ℝ) :
    (comparatorThetaProgram theta).work = 1 := by
  simp [comparatorThetaProgram,ArithmeticProgram.work]

theorem comparatorThetaProgram_admissible (theta : ℝ) :
    (comparatorThetaProgram theta).admissible := by
  simp [comparatorThetaProgram,ArithmeticProgram.admissible]

def comparatorProblem
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (theta delta : ℝ) (hmn : m ≤ n) (hmp : m ≤ p)
    (hr : 1 ≤ r) (hrm : r ≤ m) (htheta : 0 < theta)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) : FixedProblem n m p r 1 where
  A := A
  B := B
  theta := min theta (1/1048576)
  delta := delta
  accuracy := comparatorAccuracy
  core_le_rows := hmn
  core_le_cols := hmp
  rank_positive := hr
  rank_le_core := hrm
  depth_positive := le_refl _
  theta_positive := lt_min htheta (by norm_num)
  delta_positive := hdelta
  delta_lt_one := hdelta1
  accuracy_positive j _ := comparatorAccuracy_pos j
  initial_accuracy_le := by norm_num
  theta_le_last := by simpa using min_le_right theta (1/1048576 : ℝ)
  refinement_ratio j hj := by
    have hj0 : j=0 := by omega
    subst j
    norm_num

def constantDistortionComparatorProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r 1) (g : MainRandomTape I) :
    ArithmeticProgram (FixedRankOutput n p r) :=
  preparedFixedDepthProgram kernels I g

theorem constantDistortionComparatorProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r 1) (g : MainRandomTape I) :
    (constantDistortionComparatorProgram kernels I g).eval=(fixedDepthProgram kernels I g).eval :=
  preparedFixedDepthProgram_eval kernels I g

theorem constantDistortionComparatorProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r 1) (g : MainRandomTape I) :
    (constantDistortionComparatorProgram kernels I g).admissible :=
  preparedFixedDepthProgram_admissible kernels I g

theorem constantDistortionComparatorProgram_rank_cap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r 1) (g : MainRandomTape I) :
    (constantDistortionComparatorProgram kernels I g).eval.width ≤ r ∧
      (constantDistortionComparatorProgram kernels I g).eval.product.rank ≤ r :=
  preparedFixedDepthProgram_rank_cap kernels I g

/-- Exact factors at every stored level.  Reusing the factors performs no
field operation; every Gram actually used by support preprocessing is formed
by `coarseSupportProgram` below. -/
def exactComparatorSketches (A : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin p) ℝ) (L : ℕ) : StoredSketches n m p L where
  levelA _ := ⟨n,A⟩
  levelB _ := ⟨p,Bᵀ⟩
  rowsA _ := le_rfl
  rowsB _ := le_rfl

@[simp] theorem exactComparatorSketches_initialA (A : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin p) ℝ) (L : ℕ) :
    (exactComparatorSketches A B L).initialA = A := rfl

@[simp] theorem exactComparatorSketches_initialB (A : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin p) ℝ) (L : ℕ) :
    (exactComparatorSketches A B L).initialB = Bᵀ := rfl

theorem exactComparatorSketches_good (I : FixedProblem n m p r L) :
    MainSketchGood I (exactComparatorSketches I.A I.B L) := by
  intro j
  exact ⟨sketchGramApprox_identity I.A (I.accuracy j.val)
      (I.accuracy_positive j.val (by omega)).le,
    sketchGramApprox_identity I.Bᵀ (I.accuracy j.val)
      (I.accuracy_positive j.val (by omega)).le⟩

/-- A true-Gram arithmetic comparator.  The support branch handles deficient
and zero factors through the same exact rank-revealing program as the main
algorithm.  All remaining branches are the capped finite core algorithm. -/
def exactGramComparatorProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    ArithmeticProgram (FixedRankOutput n p r) := do
  let support ← coarseSupportProgram kernels I.A I.Bᵀ
  preparedMainCoreProgram kernels I (exactComparatorSketches I.A I.B L) support g

theorem exactGramComparatorProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (exactGramComparatorProgram kernels I g).admissible := by
  simp only [exactGramComparatorProgram,admissible_bind,
    coarseSupportProgram_admissible,preparedMainCoreProgram_admissible,and_self]

theorem exactGramComparatorProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (exactGramComparatorProgram kernels I g).eval =
      (mainCoreProgram kernels I (exactComparatorSketches I.A I.B L)
        (coarseSupportProgram kernels I.A I.Bᵀ).eval g).eval := by
  simp only [exactGramComparatorProgram,eval_bind,preparedMainCoreProgram_eval]

theorem exactGramComparatorProgram_rank_cap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (exactGramComparatorProgram kernels I g).eval.width ≤ r ∧
      (exactGramComparatorProgram kernels I g).eval.product.rank ≤ r :=
  ⟨(exactGramComparatorProgram kernels I g).eval.width_le,
    (exactGramComparatorProgram kernels I g).eval.rank_le⟩

/-- The work identity exposes the actual two-Gram support preprocessing.
It is the starting point for the comparator's total, explicit-output bound. -/
theorem exactGramComparatorProgram_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (exactGramComparatorProgram kernels I g).work =
      (coarseSupportProgram kernels I.A I.Bᵀ).work+
        (preparedMainCoreProgram kernels I (exactComparatorSketches I.A I.B L)
          (coarseSupportProgram kernels I.A I.Bᵀ).eval g).work := by
  exact work_bind _ _

end
end HierarchicalAbsoluteSpectral
