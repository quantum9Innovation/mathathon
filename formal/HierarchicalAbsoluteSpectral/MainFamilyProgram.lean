import HierarchicalAbsoluteSpectral.MainFamilyProgramParameters
import HierarchicalAbsoluteSpectral.MainStatementsAlgorithm
import HierarchicalAbsoluteSpectral.MainScalarProgram
import HierarchicalAbsoluteSpectral.MainPreparedProgram

/-! The original-input growing-depth caller runs its scalar preparation
before the same fixed-depth approximation program. The dependent tape is
finite and has exactly the dimensions computed by that preparation. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
open scoped Matrix.Norms.L2Operator
variable {N m r : ℕ}

abbrev FamilyRandomTape (I : FamilyProblem N m r) := MainRandomTape I.prepared.fixed

def familyRandomLaw (I : FamilyProblem N m r) : Measure (FamilyRandomTape I) :=
  mainRandomLaw I.prepared.fixed

instance familyRandomLaw_isProbability (I : FamilyProblem N m r) :
    IsProbabilityMeasure (familyRandomLaw I) := by
  unfold familyRandomLaw
  infer_instance

def familyFixedDepthContinuation (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I)
    (P : {Q : PreparedFamilyProblem I // Q=I.prepared}) : ArithmeticProgram (FixedRankOutput N N r) :=
  preparedFixedDepthProgram kernels P.val.fixed
    (cast (congrArg (fun Q : PreparedFamilyProblem I => MainRandomTape Q.fixed) P.property.symm) g)

theorem familyFixedDepthContinuation_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I)
    (P : {Q : PreparedFamilyProblem I // Q=I.prepared}) :
    familyFixedDepthContinuation kernels I g P = preparedFixedDepthProgram kernels I.prepared.fixed g := by
  rcases P with ⟨P,hP⟩
  subst P
  rfl

def growingDepthProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) :
    ArithmeticProgram (FixedRankOutput N N r) := do
  let P ← certifyAs (familyPreparationProgram I) I.prepared rfl
  familyFixedDepthContinuation kernels I g P

theorem growingDepthProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) :
    (growingDepthProgram kernels I g).eval = (fixedDepthProgram kernels I.prepared.fixed g).eval := by
  simp only [growingDepthProgram,eval_bind,familyFixedDepthContinuation_eq,preparedFixedDepthProgram_eval]

theorem growingDepthProgram_work_prepared (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) :
    (growingDepthProgram kernels I g).work = (familyPreparationProgram I).work+
      (preparedFixedDepthProgram kernels I.prepared.fixed g).work := by
  simp only [growingDepthProgram,work_bind,certifyAs_work,familyFixedDepthContinuation_eq]

theorem growingDepthProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) :
    (growingDepthProgram kernels I g).work = (familyPreparationProgram I).work+
      (4*I.prepared.depth+3*I.prepared.fixed.queryCap+2*I.prepared.fixed.repetitions+29)+
      (fixedDepthProgram kernels I.prepared.fixed g).work := by
  rw [growingDepthProgram_work_prepared,preparedFixedDepthProgram_work]
  omega

theorem growingDepthProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) :
    (growingDepthProgram kernels I g).admissible := by
  simp only [growingDepthProgram,admissible_bind,certifyAs_admissible,familyFixedDepthContinuation_eq,
    familyPreparationProgram_admissible,preparedFixedDepthProgram_admissible,and_self]

theorem growingDepthProgram_rank_cap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) :
    (growingDepthProgram kernels I g).eval.width ≤ r ∧
      (growingDepthProgram kernels I g).eval.product.rank ≤ r :=
  ⟨(growingDepthProgram kernels I g).eval.width_le,(growingDepthProgram kernels I g).eval.rank_le⟩

/-- The event is the manuscript's original accuracy and original factors,
including when the finite fallback uses a smaller internal accuracy. -/
def familySuccessEvent (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) : Set (FamilyRandomTape I) :=
  {g | ‖I.A*I.B-(growingDepthProgram kernels I g).eval.product‖ ≤
    (1+I.theta)*tailSingularValue (I.A*I.B) r}

theorem familySuccessEvent_of_internal (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I)
    (hgood : ‖I.prepared.fixed.A*I.prepared.fixed.B-
      (fixedDepthProgram kernels I.prepared.fixed g).eval.product‖ ≤
      (1+I.prepared.fixed.theta)*tailSingularValue (I.prepared.fixed.A*I.prepared.fixed.B) r) :
    g ∈ familySuccessEvent kernels I := by
  rw [I.prepared.input_left,I.prepared.input_right] at hgood
  change ‖I.A*I.B-(growingDepthProgram kernels I g).eval.product‖ ≤ _
  rw [growingDepthProgram_eval]
  exact hgood.trans (mul_le_mul_of_nonneg_right (by linarith [I.prepared.internal_accuracy_le])
    (tailSingularValue_nonneg (I.A*I.B) r))

end
end HierarchicalAbsoluteSpectral
