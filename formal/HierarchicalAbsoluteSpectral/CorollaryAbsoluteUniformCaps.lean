import HierarchicalAbsoluteSpectral.CorollaryAbsoluteFamilyFinal

/-! The absolute controller has one deterministic finite cap on every
outcome. The maximum ranges over the finite sketch metadata, and its
entries are the explicit kernel/scalar budgets, not measured runtimes. -/
namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
variable {n m p L N : ℕ}

def absoluteAllOutcomeStoredWorkCap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (Ck exponent : ℝ) : ℕ :=
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  4*L+3*I.seed.queryCap+2*I.seed.repetitions+31+absolutePreprocessingWorkCap kernels I S+
    (Nat.log 2 m+2)*absoluteUniformAttemptWorkCap kernels I S C m Ck exponent+(kernels n m p).cost

theorem absoluteAllOutcomeRealizedWorkCap_eq_stored
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) (Ck exponent : ℝ) :
    absoluteAllOutcomeRealizedWorkCap kernels I g Ck exponent=
      absoluteAllOutcomeStoredWorkCap kernels I (mainSketchProgram I.seed g.1).eval Ck exponent := rfl

def absoluteFamilyFiniteSketchWorkCap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (Ck exponent : ℝ)
    (z : MainSketchSampleTape I.fixed.seed) : ℕ :=
  4*m*N+(familyPreparationProgram I.seed).work+
    absoluteAllOutcomeStoredWorkCap kernels I.fixed (mainSketchFromFiniteSample I.fixed.seed z) Ck exponent

theorem absoluteFamilyAllOutcomeWorkCap_factorization
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I) (Ck exponent : ℝ) :
    absoluteFamilyAllOutcomeExplicitWorkCap kernels I g Ck exponent=
      absoluteFamilyFiniteSketchWorkCap kernels I Ck exponent (mainSketchFiniteSample I.fixed.seed g.1) := by
  change (4*m*N+(familyPreparationProgram I.seed).work+
    absoluteAllOutcomeStoredWorkCap kernels I.fixed (mainSketchProgram I.fixed.seed g.1).eval Ck exponent)=_
  exact congrArg (fun S : StoredSketches N m N I.seed.prepared.depth =>
    4*m*N+(familyPreparationProgram I.seed).work+absoluteAllOutcomeStoredWorkCap kernels I.fixed S Ck exponent)
      (mainSketchProgram_factorization I.fixed.seed g.1)

/-- This natural number depends on the original problem and chosen kernel
implementation, and is independent of every Gaussian tape. -/
def absoluteFamilyUniformWorkCap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (Ck exponent : ℝ) : ℕ := by
  classical
  letI := Fintype.ofFinite (MainSketchSampleTape I.fixed.seed)
  exact Finset.univ.sup (absoluteFamilyFiniteSketchWorkCap kernels I Ck exponent)

theorem absoluteFamilyExplicitWork_uniform_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (Ck exponent : ℝ) (hC : 0 < Ck) (he : 2 ≤ exponent)
    (hK : ∀ a b c M : ℕ, 1 ≤ M → a ≤ M → b ≤ M → c ≤ M →
      ((kernels a b c).cost:ℝ) ≤ Ck*(M:ℝ)^exponent)
    (g : AbsoluteFamilyTape I) :
    absoluteFamilyExplicitWork kernels I g ≤ absoluteFamilyUniformWorkCap kernels I Ck exponent := by
  classical
  have hh:=absoluteFamilyExplicitWork_all_outcome_bound kernels I g Ck exponent hC he hK
  rw [absoluteFamilyAllOutcomeWorkCap_factorization] at hh
  apply hh.trans
  letI := Fintype.ofFinite (MainSketchSampleTape I.fixed.seed)
  exact Finset.le_sup (f:=absoluteFamilyFiniteSketchWorkCap kernels I Ck exponent)
    (Finset.mem_univ (mainSketchFiniteSample I.fixed.seed g.1))

theorem absoluteFamilyProgram_uniform_all_outcome_cap (ζ : ℝ) (hζ : 0 < ζ)
    (I : AbsoluteFamilyProblem N m) :
    let K := familyFinalKernelImplementation ζ hζ
    let kernels := K.kernels N m I.core_positive
    ∀ g : AbsoluteFamilyTape I,
      (absoluteFamilyProgram kernels I g).admissible ∧
        (absoluteFamilyProgram kernels I g).eval.result.width ≤ m ∧
        absoluteFamilyExplicitWork kernels I g ≤ absoluteFamilyUniformWorkCap kernels I K.coreConstant (9/4+ζ) := by
  intro K kernels g
  refine ⟨absoluteFamilyProgram_admissible kernels I g,?_,?_⟩
  · exact (absoluteFamilyProgram kernels I g).eval.result.width_le.trans
      (absoluteFamilyProgram kernels I g).eval.attemptRank_le
  · exact absoluteFamilyExplicitWork_uniform_bound kernels I K.coreConstant (9/4+ζ)
      K.core_positive (by linarith) (K.envelopes N m I.core_positive I.core_le_side).core g

/-- The kernel fixed by the public corollary also has the deterministic
finite cap, independently of the common success event and asymptotic slack. -/
theorem absoluteFamilyPaperKernel_uniform_cap
    (d : ℝ) (hd : FamilyExponentAdmissible d) (I : AbsoluteFamilyProblem N m) :
    let K := familyFinalKernelForExponent d hd
    ∀ g : AbsoluteFamilyTape I,
      (absoluteFamilyProgram (K.kernels N m I.core_positive) I g).admissible ∧
        (absoluteFamilyProgram (K.kernels N m I.core_positive) I g).eval.result.width ≤ m ∧
        absoluteFamilyExplicitWork (K.kernels N m I.core_positive) I g ≤
          absoluteFamilyUniformWorkCap (K.kernels N m I.core_positive) I K.coreConstant
            (9/4+(2+2*d-9/4)/2) := by
  have hζ : 0 < (2+2*d-9/4)/2 := by linarith [hd.1]
  exact absoluteFamilyProgram_uniform_all_outcome_cap _ hζ I

end
end HierarchicalAbsoluteSpectral
