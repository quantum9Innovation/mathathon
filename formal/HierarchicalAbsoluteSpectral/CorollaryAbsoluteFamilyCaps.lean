import HierarchicalAbsoluteSpectral.CorollaryAbsoluteExplicitWork
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinal

/-! All random outcomes, including the executed dense-product fallback,
have a finite explicit cap under the same verified kernel implementation. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
variable {N m : ℕ}

def absoluteFamilyAllOutcomeExplicitWorkCap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I) (Ck p0 : ℝ) : ℕ :=
  4*m*N+(familyPreparationProgram I.seed).work+
    absoluteAllOutcomeRealizedWorkCap kernels I.fixed g Ck p0

theorem absoluteFamilyExplicitWork_all_outcome_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c M : ℕ, 1 ≤ M → a ≤ M → b ≤ M → c ≤ M →
      ((kernels a b c).cost:ℝ) ≤ Ck*(M:ℝ)^p0) :
    absoluteFamilyExplicitWork kernels I g ≤ absoluteFamilyAllOutcomeExplicitWorkCap kernels I g Ck p0 := by
  have he := absoluteFamilyExplicitWork_le kernels I g
  rw [absoluteFamilyTotalWork_eq] at he
  have hf := preparedAbsoluteRandomizedWork_all_outcome_bound kernels Ck p0 hC hp hK I.fixed g
  unfold absoluteFamilyAllOutcomeExplicitWorkCap
  omega

theorem absoluteFamilyProgram_all_outcome_cap (ζ : ℝ) (hζ : 0 < ζ)
    (I : AbsoluteFamilyProblem N m) :
    let K := familyFinalKernelImplementation ζ hζ
    let kernels := K.kernels N m I.core_positive
    ∀ g : AbsoluteFamilyTape I,
      (absoluteFamilyProgram kernels I g).admissible ∧
        (absoluteFamilyProgram kernels I g).eval.result.width ≤ m ∧
        absoluteFamilyExplicitWork kernels I g ≤
          absoluteFamilyAllOutcomeExplicitWorkCap kernels I g K.coreConstant (9/4+ζ) := by
  intro K kernels g
  refine ⟨absoluteFamilyProgram_admissible kernels I g,?_,?_⟩
  · exact (absoluteFamilyProgram kernels I g).eval.result.width_le.trans
      (absoluteFamilyProgram kernels I g).eval.attemptRank_le
  · exact absoluteFamilyExplicitWork_all_outcome_bound kernels I g K.coreConstant (9/4+ζ)
      K.core_positive (by linarith) (K.envelopes N m I.core_positive I.core_le_side).core

end
end HierarchicalAbsoluteSpectral
