import HierarchicalAbsoluteSpectral.CorollaryOptimizedPrograms

/-! Original-input comparator preparation.  The internal accuracy is chosen
by an executed scalar comparison, and its result is used in the dependent
fixed problem and Gaussian tape passed to the actual comparator. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r : ℕ}

def replaceComparatorTheta (I : FixedProblem n m p r 1) (theta : ℝ) (he : theta=I.theta) :
    {J : FixedProblem n m p r 1 // J=I} :=
  ⟨{I with theta := theta
           theta_positive := he.symm ▸ I.theta_positive
           theta_le_last := he.symm ▸ I.theta_le_last},by cases he; rfl⟩

def comparatorPreparationProgram
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (theta delta : ℝ) (hmn : m ≤ n) (hmp : m ≤ p)
    (hr : 1 ≤ r) (hrm : r ≤ m) (htheta : 0 < theta)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ArithmeticProgram {J : FixedProblem n m p r 1 //
      J=comparatorProblem A B theta delta hmn hmp hr hrm htheta hdelta hdelta1} :=
  .branch theta (1/1048576)
    (fun h => .pure (replaceComparatorTheta _ theta (min_eq_left h).symm))
    (fun h => .pure (replaceComparatorTheta _ (1/1048576) (min_eq_right (le_of_not_ge h)).symm))

theorem comparatorPreparationProgram_eval
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (theta delta : ℝ) (hmn : m ≤ n) (hmp : m ≤ p)
    (hr : 1 ≤ r) (hrm : r ≤ m) (htheta : 0 < theta)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (comparatorPreparationProgram A B theta delta hmn hmp hr hrm htheta hdelta hdelta1).eval =
      ⟨comparatorProblem A B theta delta hmn hmp hr hrm htheta hdelta hdelta1,rfl⟩ := by
  apply Subtype.ext
  exact (comparatorPreparationProgram A B theta delta hmn hmp hr hrm htheta hdelta hdelta1).eval.property

theorem comparatorPreparationProgram_work
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (theta delta : ℝ) (hmn : m ≤ n) (hmp : m ≤ p)
    (hr : 1 ≤ r) (hrm : r ≤ m) (htheta : 0 < theta)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (comparatorPreparationProgram A B theta delta hmn hmp hr hrm htheta hdelta hdelta1).work=1 := by
  simp [comparatorPreparationProgram,ArithmeticProgram.work]

theorem comparatorPreparationProgram_admissible
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (theta delta : ℝ) (hmn : m ≤ n) (hmp : m ≤ p)
    (hr : 1 ≤ r) (hrm : r ≤ m) (htheta : 0 < theta)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (comparatorPreparationProgram A B theta delta hmn hmp hr hrm htheta hdelta hdelta1).admissible := by
  simp [comparatorPreparationProgram,ArithmeticProgram.admissible]

def constantComparatorContinuation
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r 1) (g : MainRandomTape I)
    (J : {J : FixedProblem n m p r 1 // J=I}) : ArithmeticProgram (FixedRankOutput n p r) :=
  constantDistortionComparatorProgram kernels J.val
    (cast (congrArg (fun I => MainRandomTape I) J.property.symm) g)

theorem constantComparatorContinuation_eq
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r 1) (g : MainRandomTape I)
    (J : {J : FixedProblem n m p r 1 // J=I}) :
    constantComparatorContinuation kernels I g J=constantDistortionComparatorProgram kernels I g := by
  rcases J with ⟨J,hJ⟩
  subst J
  rfl

def gramComparatorContinuation
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r 1) (g : MainRandomTape I)
    (J : {J : FixedProblem n m p r 1 // J=I}) : ArithmeticProgram (FixedRankOutput n p r) :=
  exactGramComparatorProgram kernels J.val
    (cast (congrArg (fun I => MainRandomTape I) J.property.symm) g)

theorem gramComparatorContinuation_eq
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r 1) (g : MainRandomTape I)
    (J : {J : FixedProblem n m p r 1 // J=I}) :
    gramComparatorContinuation kernels I g J=exactGramComparatorProgram kernels I g := by
  rcases J with ⟨J,hJ⟩
  subst J
  rfl

def preparedConstantComparatorProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (theta delta : ℝ) (hmn : m ≤ n) (hmp : m ≤ p)
    (hr : 1 ≤ r) (hrm : r ≤ m) (htheta : 0 < theta)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (g : MainRandomTape (comparatorProblem A B theta delta hmn hmp hr hrm htheta hdelta hdelta1)) :
    ArithmeticProgram (FixedRankOutput n p r) := do
  let J ← comparatorPreparationProgram A B theta delta hmn hmp hr hrm htheta hdelta hdelta1
  constantComparatorContinuation kernels _ g J

def preparedGramComparatorProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (theta delta : ℝ) (hmn : m ≤ n) (hmp : m ≤ p)
    (hr : 1 ≤ r) (hrm : r ≤ m) (htheta : 0 < theta)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (g : MainRandomTape (comparatorProblem A B theta delta hmn hmp hr hrm htheta hdelta hdelta1)) :
    ArithmeticProgram (FixedRankOutput n p r) := do
  let J ← comparatorPreparationProgram A B theta delta hmn hmp hr hrm htheta hdelta hdelta1
  gramComparatorContinuation kernels _ g J

theorem preparedConstantComparatorProgram_specification
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (theta delta : ℝ) (hmn : m ≤ n) (hmp : m ≤ p)
    (hr : 1 ≤ r) (hrm : r ≤ m) (htheta : 0 < theta)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (g : MainRandomTape (comparatorProblem A B theta delta hmn hmp hr hrm htheta hdelta hdelta1)) :
    let I := comparatorProblem A B theta delta hmn hmp hr hrm htheta hdelta hdelta1
    (preparedConstantComparatorProgram kernels A B theta delta hmn hmp hr hrm htheta hdelta hdelta1 g).eval=
      (constantDistortionComparatorProgram kernels I g).eval ∧
    (preparedConstantComparatorProgram kernels A B theta delta hmn hmp hr hrm htheta hdelta hdelta1 g).work=
      1+(constantDistortionComparatorProgram kernels I g).work ∧
    (preparedConstantComparatorProgram kernels A B theta delta hmn hmp hr hrm htheta hdelta hdelta1 g).admissible := by
  simp only [preparedConstantComparatorProgram,eval_bind,work_bind,admissible_bind,
    comparatorPreparationProgram_work,constantComparatorContinuation_eq,
    comparatorPreparationProgram_admissible,constantDistortionComparatorProgram_admissible,
    and_self]

theorem preparedGramComparatorProgram_specification
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (theta delta : ℝ) (hmn : m ≤ n) (hmp : m ≤ p)
    (hr : 1 ≤ r) (hrm : r ≤ m) (htheta : 0 < theta)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (g : MainRandomTape (comparatorProblem A B theta delta hmn hmp hr hrm htheta hdelta hdelta1)) :
    let I := comparatorProblem A B theta delta hmn hmp hr hrm htheta hdelta hdelta1
    (preparedGramComparatorProgram kernels A B theta delta hmn hmp hr hrm htheta hdelta hdelta1 g).eval=
      (exactGramComparatorProgram kernels I g).eval ∧
    (preparedGramComparatorProgram kernels A B theta delta hmn hmp hr hrm htheta hdelta hdelta1 g).work=
      1+(exactGramComparatorProgram kernels I g).work ∧
    (preparedGramComparatorProgram kernels A B theta delta hmn hmp hr hrm htheta hdelta hdelta1 g).admissible := by
  simp only [preparedGramComparatorProgram,eval_bind,work_bind,admissible_bind,
    comparatorPreparationProgram_work,gramComparatorContinuation_eq,
    comparatorPreparationProgram_admissible,exactGramComparatorProgram_admissible,
    and_self]

end
end HierarchicalAbsoluteSpectral
