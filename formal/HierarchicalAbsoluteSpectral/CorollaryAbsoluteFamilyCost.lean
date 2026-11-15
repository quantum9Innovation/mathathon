import HierarchicalAbsoluteSpectral.CorollaryAbsoluteFamily
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteRuntime
import HierarchicalAbsoluteSpectral.MainFamilyProgramSequences

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {N m : ℕ}

theorem absolute_failure_allocation_inverse_polynomial (m : ℕ) (δ c : ℝ)
    (hm : 2 ≤ m) (hδ : (m:ℝ)^(-c) ≤ δ) :
    (m:ℝ)^(-(c+2)) ≤ δ/((m:ℝ)+1) := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0:ℝ) < m := by linarith
  apply (le_div_iff₀ (by positivity : 0 < (m:ℝ)+1)).mpr
  calc
    (m:ℝ)^(-(c+2))*((m:ℝ)+1) ≤ (m:ℝ)^(-(c+2))*(m:ℝ)^2 :=
      mul_le_mul_of_nonneg_left (by nlinarith : (m:ℝ)+1 ≤ (m:ℝ)^2) (Real.rpow_nonneg hmpos.le _)
    _ = (m:ℝ)^(-c) := by
      rw [← Real.rpow_two,← Real.rpow_add hmpos]
      congr 1
      ring
    _ ≤ δ := hδ

theorem AbsoluteFamilyProblem.seed_confidence_lower (I : AbsoluteFamilyProblem N m)
    (c : ℝ) (hm : 2 ≤ m) (hδ : (m:ℝ)^(-c) ≤ I.delta) :
    (m:ℝ)^(-(c+2)) ≤ I.seed.delta :=
  absolute_failure_allocation_inverse_polynomial m I.delta c hm hδ

def absoluteFamilyTotalWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I) : ℕ :=
  (absoluteFamilyProgram kernels I g).work+absoluteAlgorithmGaussianDrawCount kernels I.fixed g+N*N

theorem absoluteFamilyTotalWork_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I) :
    absoluteFamilyTotalWork kernels I g=(familyPreparationProgram I.seed).work+
      preparedAbsoluteRandomizedWork kernels I.fixed g := by
  rw [absoluteFamilyTotalWork,absoluteFamilyProgram_work]
  unfold preparedAbsoluteRandomizedWork
  omega

def absoluteFamilySmallRealizedWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I) (Ck p0 : ℝ) : ℕ :=
  (familyPreparationProgram I.seed).work+absoluteSmallRealizedWorkCap kernels I.fixed g Ck p0

/-- The actual scalar schedule, lazy Gaussian draws and explicit dense
output are charged on the same event as absolute error and adaptive width. -/
theorem absolute_family_error_width_and_runtime_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c M : ℕ, 1 ≤ M → a ≤ M → b ≤ M → c ≤ M →
      ((kernels a b c).cost:ℝ) ≤ Ck*(M:ℝ)^p0)
    (I : AbsoluteFamilyProblem N m) :
    ∃ E : Set (AbsoluteFamilyTape I), MeasurableSet E ∧
      (absoluteFamilyRandomLaw I).real E ≥ 1-I.delta ∧ ∀ g ∈ E,
        let out := (absoluteFamilyProgram kernels I g).eval
        out.result.width ≤ 2*I.slackRank ∧ ‖I.A*I.B-out.result.product‖ ≤ I.tolerance ∧
          (I.slackRank ≤ Nat.sqrt m/2 → absoluteFamilyTotalWork kernels I g ≤
            absoluteFamilySmallRealizedWorkCap kernels I g Ck p0) := by
  obtain ⟨E,hEm,hEp,hE⟩ := absolute_error_width_and_runtime_event kernels Ck p0 hC hp hK I.fixed
  refine ⟨E,hEm,hEp,?_⟩
  intro g hg
  obtain ⟨hw,he,ht⟩ := hE g hg
  rw [absoluteFamilyProgram_eval]
  rw [preparedAbsoluteAlgorithmProgram_eval] at hw he
  refine ⟨hw.trans (Nat.mul_le_mul_left 2 I.internal_slackRank_le),?_,?_⟩
  · have hA : I.fixed.A=I.A := I.seed.prepared.input_left
    have hB : I.fixed.B=I.B := I.seed.prepared.input_right
    change ‖I.fixed.A*I.fixed.B-(absoluteAlgorithmProgram kernels I.fixed g).eval.result.product‖ ≤ I.tolerance at he
    rw [hA,hB] at he
    exact he
  · intro hs
    rw [absoluteFamilyTotalWork_eq]
    exact Nat.add_le_add_left (ht (I.internal_slackRank_le.trans hs)) _

end
end HierarchicalAbsoluteSpectral
