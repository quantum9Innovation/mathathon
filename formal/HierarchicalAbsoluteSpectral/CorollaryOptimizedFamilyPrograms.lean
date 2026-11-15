import HierarchicalAbsoluteSpectral.CorollaryOptimizedPreparedProbability
import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeDimension
import HierarchicalAbsoluteSpectral.MainFamilyProgramParameters

/-! The two comparator algorithms on exactly the original family inputs.
Theta is computed from the integer dimensions by four counted operations,
capped by an executed comparison, and passed to the same scalar-prepared
finite programs whose full relative-error guarantees have been proved. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
open scoped Matrix.Norms.L2Operator
variable {N m r : ℕ}

def comparatorDimensionThetaProgram (m N : ℕ) : ArithmeticProgram ℝ := do
  let rho ← div (m:ℝ) (N:ℝ)
  let rhoSquared ← mul rho rho
  let rhoRoot ← sqrt rho
  mul rhoSquared rhoRoot

@[simp] theorem comparatorDimensionThetaProgram_eval (m N : ℕ) :
    (comparatorDimensionThetaProgram m N).eval=comparatorDimensionTheta m N := by
  simp [comparatorDimensionThetaProgram,comparatorDimensionTheta,pow_two]

@[simp] theorem comparatorDimensionThetaProgram_work (m N : ℕ) :
    (comparatorDimensionThetaProgram m N).work=4 := by simp [comparatorDimensionThetaProgram]

theorem comparatorDimensionThetaProgram_admissible (m N : ℕ) (hN : 0 < N) :
    (comparatorDimensionThetaProgram m N).admissible := by
  simp only [comparatorDimensionThetaProgram,admissible_bind,admissible_div,eval_div,
    admissible_mul,eval_mul,admissible_sqrt,true_and,and_true]
  exact ⟨by exact_mod_cast hN.ne',div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩

def comparatorProblemForFamily (I : FamilyProblem N m r) : FixedProblem N m N r 1 :=
  comparatorProblem I.A I.B I.theta I.delta I.core_le_side I.core_le_side
    I.rank_positive I.rank_le_core I.theta_positive I.delta_positive I.delta_lt_one

abbrev ComparatorFamilyRandomTape (I : FamilyProblem N m r) := MainRandomTape (comparatorProblemForFamily I)

def comparatorFamilyLaw (I : FamilyProblem N m r) : Measure (ComparatorFamilyRandomTape I) :=
  mainRandomLaw (comparatorProblemForFamily I)

instance comparatorFamilyLaw_isProbability (I : FamilyProblem N m r) :
    IsProbabilityMeasure (comparatorFamilyLaw I) := by unfold comparatorFamilyLaw; infer_instance

def comparatorFamilyCapProgram (I : FamilyProblem N m r) (t : {theta : ℝ // theta=I.theta}) :
    ArithmeticProgram {J : FixedProblem N m N r 1 // J=comparatorProblemForFamily I} := do
  let J ← comparatorPreparationProgram I.A I.B t.val I.delta I.core_le_side I.core_le_side
    I.rank_positive I.rank_le_core (by rw [t.property]; exact I.theta_positive) I.delta_positive I.delta_lt_one
  .pure ⟨J.val,J.property.trans (by rcases t with ⟨t,ht⟩; subst t; rfl)⟩

theorem comparatorFamilyCapProgram_work (I : FamilyProblem N m r) (t : {theta : ℝ // theta=I.theta}) :
    (comparatorFamilyCapProgram I t).work=1 := by
  simp only [comparatorFamilyCapProgram,work_bind,comparatorPreparationProgram_work,work_pure,add_zero]

theorem comparatorFamilyCapProgram_admissible (I : FamilyProblem N m r) (t : {theta : ℝ // theta=I.theta}) :
    (comparatorFamilyCapProgram I t).admissible := by
  simp only [comparatorFamilyCapProgram,admissible_bind,comparatorPreparationProgram_admissible,
    admissible_pure,and_self]

def optimizedKrylovComparator (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : ComparatorFamilyRandomTape I) : ArithmeticProgram (FixedRankOutput N N r) := do
  let t ← certifyAs (comparatorDimensionThetaProgram m N) I.theta
    (by rw [comparatorDimensionThetaProgram_eval]; rfl)
  let J ← comparatorFamilyCapProgram I t
  constantComparatorContinuation kernels (comparatorProblemForFamily I) g J

def optimizedGramComparator (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : ComparatorFamilyRandomTape I) : ArithmeticProgram (FixedRankOutput N N r) := do
  let t ← certifyAs (comparatorDimensionThetaProgram m N) I.theta
    (by rw [comparatorDimensionThetaProgram_eval]; rfl)
  let J ← comparatorFamilyCapProgram I t
  gramComparatorContinuation kernels (comparatorProblemForFamily I) g J

theorem optimizedKrylovComparator_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : ComparatorFamilyRandomTape I) :
    (optimizedKrylovComparator kernels I g).eval=
      (constantDistortionComparatorProgram kernels (comparatorProblemForFamily I) g).eval := by
  simp only [optimizedKrylovComparator,eval_bind,constantComparatorContinuation_eq]

theorem optimizedGramComparator_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : ComparatorFamilyRandomTape I) :
    (optimizedGramComparator kernels I g).eval=
      (exactGramComparatorProgram kernels (comparatorProblemForFamily I) g).eval := by
  simp only [optimizedGramComparator,eval_bind,gramComparatorContinuation_eq]

theorem optimizedKrylovComparator_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : ComparatorFamilyRandomTape I) :
    (optimizedKrylovComparator kernels I g).work=
      5+(constantDistortionComparatorProgram kernels (comparatorProblemForFamily I) g).work := by
  simp only [optimizedKrylovComparator,work_bind,certifyAs_work,comparatorDimensionThetaProgram_work,
    comparatorFamilyCapProgram_work,constantComparatorContinuation_eq]
  omega

theorem optimizedGramComparator_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : ComparatorFamilyRandomTape I) :
    (optimizedGramComparator kernels I g).work=
      5+(exactGramComparatorProgram kernels (comparatorProblemForFamily I) g).work := by
  simp only [optimizedGramComparator,work_bind,certifyAs_work,comparatorDimensionThetaProgram_work,
    comparatorFamilyCapProgram_work,gramComparatorContinuation_eq]
  omega

theorem optimizedKrylovComparator_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : ComparatorFamilyRandomTape I) :
    (optimizedKrylovComparator kernels I g).admissible := by
  simp only [optimizedKrylovComparator,admissible_bind,certifyAs_admissible,
    comparatorDimensionThetaProgram_admissible m N I.side_positive,
    comparatorFamilyCapProgram_admissible,constantComparatorContinuation_eq,
    constantDistortionComparatorProgram_admissible,and_self]

theorem optimizedGramComparator_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : ComparatorFamilyRandomTape I) :
    (optimizedGramComparator kernels I g).admissible := by
  simp only [optimizedGramComparator,admissible_bind,certifyAs_admissible,
    comparatorDimensionThetaProgram_admissible m N I.side_positive,
    comparatorFamilyCapProgram_admissible,gramComparatorContinuation_eq,
    exactGramComparatorProgram_admissible,and_self]

theorem optimizedKrylovComparator_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FamilyProblem N m r) :
    (comparatorFamilyLaw I).real {g : ComparatorFamilyRandomTape I |
      ‖I.A*I.B-(optimizedKrylovComparator kernels I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r} ≥ 1-I.delta := by
  have hp := constantDistortionComparatorProgram_error_probability kernels (comparatorProblemForFamily I)
  refine hp.trans (measureReal_mono ?_)
  intro g hg
  change ‖I.A*I.B-(optimizedKrylovComparator kernels I g).eval.product‖ ≤ _
  rw [optimizedKrylovComparator_eval]
  change ‖I.A*I.B-(constantDistortionComparatorProgram kernels (comparatorProblemForFamily I) g).eval.product‖ ≤
    (1+min I.theta (1/1048576))*tailSingularValue (I.A*I.B) r at hg
  exact hg.trans (mul_le_mul_of_nonneg_right (by linarith [min_le_left I.theta (1/1048576:ℝ)])
    (tailSingularValue_nonneg (I.A*I.B) r))

theorem optimizedGramComparator_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FamilyProblem N m r) :
    (comparatorFamilyLaw I).real {g : ComparatorFamilyRandomTape I |
      ‖I.A*I.B-(optimizedGramComparator kernels I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r} ≥ 1-I.delta := by
  have hp := exactGramComparatorProgram_error_probability kernels (comparatorProblemForFamily I)
  refine hp.trans (measureReal_mono ?_)
  intro g hg
  change ‖I.A*I.B-(optimizedGramComparator kernels I g).eval.product‖ ≤ _
  rw [optimizedGramComparator_eval]
  change ‖I.A*I.B-(exactGramComparatorProgram kernels (comparatorProblemForFamily I) g).eval.product‖ ≤
    (1+min I.theta (1/1048576))*tailSingularValue (I.A*I.B) r at hg
  exact hg.trans (mul_le_mul_of_nonneg_right (by linarith [min_le_left I.theta (1/1048576:ℝ)])
    (tailSingularValue_nonneg (I.A*I.B) r))

end
end HierarchicalAbsoluteSpectral
