import HierarchicalAbsoluteSpectral.CorollaryTwoLevelPrepared

/-! The construction stage returns the two actual factors.  Dense
expansion is a separate, counted matrix-kernel call. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r k w : ℕ}

structure TwoLevelFactors (n p r : ℕ) where
  width : ℕ
  width_le : width ≤ r
  left : Matrix (Fin n) (Fin width) ℝ
  right : Matrix (Fin width) (Fin p) ℝ

def FixedRankOutput.twoLevelFactors (out : FixedRankOutput n p r) : TwoLevelFactors n p r :=
  ⟨out.width,out.width_le,out.left,out.right⟩

def TwoLevelFactors.product (out : TwoLevelFactors n p r) : Matrix (Fin n) (Fin p) ℝ :=
  out.left*out.right

theorem FixedRankOutput.twoLevelFactors_product (out : FixedRankOutput n p r) :
    out.twoLevelFactors.product = out.product := out.product_eq.symm

def zeroTwoLevelFactors (n p r : ℕ) : TwoLevelFactors n p r := ⟨0,Nat.zero_le _,0,0⟩

def twoLevelExpandProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (out : TwoLevelFactors n p r) : ArithmeticProgram (FixedRankOutput n p r) := do
  let C ← ((kernels n out.width p).program out.left out.right).certify
  .pure
    { width := out.width, width_le := out.width_le, left := out.left, right := out.right
      product := C.val
      product_eq := C.property.trans (ArithmeticKernel.program_eval _ _ _) }

theorem twoLevelExpandProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (out : TwoLevelFactors n p r) :
    (twoLevelExpandProgram kernels out).eval.product = out.product := by
  simp only [twoLevelExpandProgram,eval_bind,certify_eval,ArithmeticKernel.program_eval,eval_pure]
  rfl

theorem twoLevelExpandProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (out : TwoLevelFactors n p r) :
    (twoLevelExpandProgram kernels out).work = (kernels n out.width p).cost := by
  simp [twoLevelExpandProgram]

theorem twoLevelExpandProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (out : TwoLevelFactors n p r) : (twoLevelExpandProgram kernels out).admissible := by
  simp [twoLevelExpandProgram]

/-- Only the two thin matrix products are executed. The dense product
does not occur in the result data or any instruction of this program. -/
def twoLevelFactorProjectionProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) : ArithmeticProgram (TwoLevelFactors n p r) := do
  let leftProduct ← (kernels w n m).program Uᵀ A
  let right ← (kernels w m p).program leftProduct B
  .pure ⟨w,hw,U,right⟩

theorem twoLevelFactorProjectionProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) :
    (twoLevelFactorProjectionProgram kernels A B U hw).eval =
      (projectionOutputProgram kernels A B U hw).eval.twoLevelFactors := by
  rw [projectionOutputProgram_eval]
  simp only [twoLevelFactorProjectionProgram,eval_bind,
    ArithmeticKernel.program_eval,eval_pure,FixedRankOutput.twoLevelFactors]

theorem twoLevelFactorProjectionProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) :
    (twoLevelFactorProjectionProgram kernels A B U hw).work =
      (kernels w n m).cost+(kernels w m p).cost := by
  simp [twoLevelFactorProjectionProgram]

theorem twoLevelFactorProjectionProgram_work_split
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) :
    (twoLevelFactorProjectionProgram kernels A B U hw).work+(kernels n w p).cost =
      (projectionOutputProgram kernels A B U hw).work := by
  rw [twoLevelFactorProjectionProgram_work,projectionOutputProgram_work]

theorem twoLevelFactorProjectionProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) :
    (twoLevelFactorProjectionProgram kernels A B U hw).admissible := by
  simp [twoLevelFactorProjectionProgram]

def twoLevelFactorExactProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z w)
    (U : Matrix (Fin k) (Fin w) ℝ) (hw : w ≤ r) : ArithmeticProgram (TwoLevelFactors n p r) := do
  let out ← physicalRangeProgram kernels PZ U
  twoLevelFactorProjectionProgram kernels A B out.basis (out.dimension_le_cols.trans hw)

theorem twoLevelFactorExactProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z w)
    (U : Matrix (Fin k) (Fin w) ℝ) (hw : w ≤ r) :
    (twoLevelFactorExactProgram kernels A B PZ U hw).eval =
      (exactPhysicalOutputProgram kernels A B PZ U hw).eval.twoLevelFactors := by
  simp only [twoLevelFactorExactProgram,exactPhysicalOutputProgram,eval_bind,
    twoLevelFactorProjectionProgram_eval]

theorem twoLevelFactorExactProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z w)
    (U : Matrix (Fin k) (Fin w) ℝ) (hw : w ≤ r) :
    (twoLevelFactorExactProgram kernels A B PZ U hw).admissible := by
  simp only [twoLevelFactorExactProgram,admissible_bind,physicalRangeProgram_admissible,
    twoLevelFactorProjectionProgram_admissible,and_self]

def twoLevelFactorStrongProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {T : Core k} {Z : Matrix (Fin n) (Fin k) ℝ} (PT : MatrixAction T r) (PZ : MatrixAction Z r)
    (U β α : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    ArithmeticProgram (TwoLevelFactors n p r) := do
  let out ← automaticStrongPhysicalRangeProgram kernels PT PZ U β α hk hU hβ hβ1 hα hα1 Ξ
  twoLevelFactorProjectionProgram kernels A B out.2.basis out.2.dimension_le_cols

theorem twoLevelFactorStrongProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {T : Core k} {Z : Matrix (Fin n) (Fin k) ℝ} (PT : MatrixAction T r) (PZ : MatrixAction Z r)
    (U β α : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    (twoLevelFactorStrongProgram kernels A B PT PZ U β α hk hU hβ hβ1 hα hα1 Ξ).eval =
      (strongProjectionOutputProgram kernels A B PT PZ U β α hk hU hβ hβ1 hα hα1 Ξ).eval.twoLevelFactors := by
  simp only [twoLevelFactorStrongProgram,strongProjectionOutputProgram,eval_bind,
    twoLevelFactorProjectionProgram_eval]

theorem twoLevelFactorStrongProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {T : Core k} {Z : Matrix (Fin n) (Fin k) ℝ} (PT : MatrixAction T r) (PZ : MatrixAction Z r)
    (U β α : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    (twoLevelFactorStrongProgram kernels A B PT PZ U β α hk hU hβ hβ1 hα hα1 Ξ).admissible := by
  simp only [twoLevelFactorStrongProgram,admissible_bind,automaticStrongPhysicalRangeProgram_admissible,
    twoLevelFactorProjectionProgram_admissible,and_self]

end
end HierarchicalAbsoluteSpectral
