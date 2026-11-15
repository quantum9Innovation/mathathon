import HierarchicalAbsoluteSpectral.MainFamilyProgram
import HierarchicalAbsoluteSpectral.BaseMainRandomizedCost
import HierarchicalAbsoluteSpectral.MainExplicitOutputCost

/-! The growing-depth caller counts the finite Gaussian tape and every
executed scalar preparation and approximation instruction. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {N m r : ℕ}

def growingDepthTotalWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) : ℕ :=
  mainRandomizedWork I.prepared.fixed (growingDepthProgram kernels I g).work

theorem growingDepthTotalWork_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) :
    growingDepthTotalWork kernels I g = (familyPreparationProgram I).work+
      preparedFixedDepthTotalWork kernels I.prepared.fixed g := by
  rw [growingDepthTotalWork,growingDepthProgram_work_prepared]
  unfold preparedFixedDepthTotalWork mainRandomizedWork
  omega

def growingDepthRealizedWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) (Ck p0 : ℝ) : ℕ :=
  (familyPreparationProgram I).work+preparedFixedDepthRealizedWorkCap kernels
    (rangeDeflationWorkCap kernels) I.prepared.fixed g Ck p0

theorem growingDepthTotalWork_bound_deflation
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (kernels a b c).cost ≤ 2*a*b*c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c M : ℕ, 1 ≤ M → a ≤ M → b ≤ M → c ≤ M →
      ((kernels a b c).cost : ℝ) ≤ Ck*(M : ℝ)^p0)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) :
    growingDepthTotalWork kernels I g ≤ growingDepthRealizedWorkCap kernels I g Ck p0 := by
  rw [growingDepthTotalWork_eq]
  exact Nat.add_le_add_left
    (preparedFixedDepthTotalWork_bound_deflation kernels hClassical Ck p0 hC hp hK I.prepared.fixed g) _

/-- The literal input reads, both returned factors, the full dense output,
Gaussian samples, scalar preparation and approximation arithmetic. -/
def growingDepthExplicitWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) : ℕ :=
  m*(N+N)+(growingDepthProgram kernels I g).eval.entryCount+growingDepthTotalWork kernels I g

theorem growingDepthExplicitWork_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) :
    growingDepthExplicitWork kernels I g = (familyPreparationProgram I).work+
      preparedFixedDepthExplicitWork kernels I.prepared.fixed g := by
  unfold growingDepthExplicitWork preparedFixedDepthExplicitWork
  rw [growingDepthTotalWork_eq,growingDepthProgram_eval,preparedFixedDepthProgram_eval]
  omega

theorem growingDepthExplicitWork_bound_deflation
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (kernels a b c).cost ≤ 2*a*b*c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c M : ℕ, 1 ≤ M → a ≤ M → b ≤ M → c ≤ M →
      ((kernels a b c).cost : ℝ) ≤ Ck*(M : ℝ)^p0)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I) :
    growingDepthExplicitWork kernels I g ≤ 2*m*(N+N)+N*N+
      growingDepthRealizedWorkCap kernels I g Ck p0 := by
  rw [growingDepthExplicitWork_eq]
  have hh := preparedFixedDepthExplicitWork_bound_deflation kernels hClassical Ck p0 hC hp hK I.prepared.fixed g
  unfold growingDepthRealizedWorkCap
  omega

end
end HierarchicalAbsoluteSpectral
