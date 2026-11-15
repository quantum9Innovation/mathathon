import HierarchicalAbsoluteSpectral.CorollaryTwoLevelConstructionOutput

/-! Literal operation bounds for the factor-only final suffix. The caps
contain only thin products and range algebra; dense expansion is absent. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r k w : ℕ}

def twoLevelFactorProjectionWorkCap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (n m p r : ℕ) : ℕ :=
  Finset.univ.sup (fun w : Fin (r+1) =>
    (kernels w.val n m).cost+(kernels w.val m p).cost)

theorem twoLevelFactorProjectionWorkCap_correct
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) :
    (twoLevelFactorProjectionProgram kernels A B U hw).work ≤ twoLevelFactorProjectionWorkCap kernels n m p r := by
  rw [twoLevelFactorProjectionProgram_work]
  exact Finset.le_sup (f := fun i : Fin (r+1) => (kernels i.val n m).cost+(kernels i.val m p).cost)
    (Finset.mem_univ (⟨w,by omega⟩ : Fin (r+1)))

theorem twoLevelFactorExactProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z w)
    (U : Matrix (Fin k) (Fin w) ℝ) (hw : w ≤ r) :
    (twoLevelFactorExactProgram kernels A B PZ U hw).work ≤
      PZ.cost+exactRangeWorkCap kernels n w+twoLevelFactorProjectionWorkCap kernels n m p r := by
  have hp := physicalRangeProgram_work_bound kernels PZ U
  have ho := twoLevelFactorProjectionWorkCap_correct kernels A B
    (physicalRangeProgram kernels PZ U).eval.basis
      ((physicalRangeProgram kernels PZ U).eval.dimension_le_cols.trans hw)
  simp only [twoLevelFactorExactProgram,work_bind]
  omega

theorem twoLevelFactorStrongProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {T : Core k} {Z : Matrix (Fin n) (Fin k) ℝ} (PT : MatrixAction T r) (PZ : MatrixAction Z r)
    (U β α : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    let v := strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1
    (twoLevelFactorStrongProgram kernels A B PT PZ U β α hk hU hβ hβ1 hα hα1 Ξ).work ≤
      4*v+14+(9+3*v+(v+1)*(PT.cost+6*k*r)+k*r+PZ.cost+exactRangeWorkCap kernels n r)+
        twoLevelFactorProjectionWorkCap kernels n m p r := by
  intro v
  have hs := automaticStrongPhysicalRangeProgram_work_bound kernels PT PZ U β α hk hU hβ hβ1 hα hα1 Ξ
  have ho := twoLevelFactorProjectionWorkCap_correct kernels A B
    (automaticStrongPhysicalRangeProgram kernels PT PZ U β α hk hU hβ hβ1 hα hα1 Ξ).eval.2.basis
    (automaticStrongPhysicalRangeProgram kernels PT PZ U β α hk hU hβ hβ1 hα hα1 Ξ).eval.2.dimension_le_cols
  simp only [twoLevelFactorStrongProgram,work_bind]
  dsimp only [v]
  omega

end
end HierarchicalAbsoluteSpectral
