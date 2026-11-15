import HierarchicalAbsoluteSpectral.CorollaryAbsoluteFamilyCost
import HierarchicalAbsoluteSpectral.MainExplicitOutputCost

/-! Exact entry access for both factors and the dense matrix, in addition
to the Gaussian samples and executed scalar arithmetic already counted. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {n m p L N : ℕ}

def preparedAbsoluteExplicitWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) : ℕ :=
  m*(n+p)+(preparedAbsoluteAlgorithmProgram kernels I g).eval.result.entryCount+
    (preparedAbsoluteAlgorithmProgram kernels I g).work+absoluteAlgorithmGaussianDrawCount kernels I g

theorem preparedAbsoluteExplicitWork_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) :
    preparedAbsoluteExplicitWork kernels I g ≤ 2*m*(n+p)+preparedAbsoluteRandomizedWork kernels I g := by
  have hentries := (preparedAbsoluteAlgorithmProgram kernels I g).eval.result.entryCount_le
    (preparedAbsoluteAlgorithmProgram kernels I g).eval.attemptRank_le
  unfold preparedAbsoluteExplicitWork preparedAbsoluteRandomizedWork
  nlinarith only [hentries]

def absoluteFamilyExplicitWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I) : ℕ :=
  m*(N+N)+(absoluteFamilyProgram kernels I g).eval.result.entryCount+
    (absoluteFamilyProgram kernels I g).work+absoluteAlgorithmGaussianDrawCount kernels I.fixed g

theorem absoluteFamilyExplicitWork_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I) :
    absoluteFamilyExplicitWork kernels I g=(familyPreparationProgram I.seed).work+
      preparedAbsoluteExplicitWork kernels I.fixed g := by
  rw [absoluteFamilyExplicitWork,absoluteFamilyProgram_work,absoluteFamilyProgram_eval]
  unfold preparedAbsoluteExplicitWork
  rw [preparedAbsoluteAlgorithmProgram_eval]
  omega

theorem absoluteFamilyExplicitWork_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I) :
    absoluteFamilyExplicitWork kernels I g ≤ 4*m*N+absoluteFamilyTotalWork kernels I g := by
  rw [absoluteFamilyExplicitWork_eq,absoluteFamilyTotalWork_eq]
  have hh := preparedAbsoluteExplicitWork_le kernels I.fixed g
  nlinarith only [hh]

theorem absolute_family_explicit_error_width_and_runtime_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c M : ℕ, 1 ≤ M → a ≤ M → b ≤ M → c ≤ M →
      ((kernels a b c).cost:ℝ) ≤ Ck*(M:ℝ)^p0)
    (I : AbsoluteFamilyProblem N m) :
    ∃ E : Set (AbsoluteFamilyTape I), MeasurableSet E ∧
      (absoluteFamilyRandomLaw I).real E ≥ 1-I.delta ∧ ∀ g ∈ E,
        let out := (absoluteFamilyProgram kernels I g).eval
        out.result.width ≤ 2*I.slackRank ∧ ‖I.A*I.B-out.result.product‖ ≤ I.tolerance ∧
          (I.slackRank ≤ Nat.sqrt m/2 → absoluteFamilyExplicitWork kernels I g ≤
            4*m*N+absoluteFamilySmallRealizedWorkCap kernels I g Ck p0) := by
  obtain ⟨E,hEm,hEp,hE⟩ := absolute_family_error_width_and_runtime_event kernels Ck p0 hC hp hK I
  refine ⟨E,hEm,hEp,?_⟩
  intro g hg
  obtain ⟨hw,he,ht⟩ := hE g hg
  exact ⟨hw,he,fun hs => (absoluteFamilyExplicitWork_le kernels I g).trans
    (Nat.add_le_add_left (ht hs) _)⟩

end
end HierarchicalAbsoluteSpectral
