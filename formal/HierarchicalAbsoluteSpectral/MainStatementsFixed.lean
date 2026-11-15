import HierarchicalAbsoluteSpectral.ThresholdKrylovProgram
import HierarchicalAbsoluteSpectral.Spectral

/-! The concrete result type and final dense-output program for the fixed
theorem. The main randomized theorem will quantify only over the original
matrices and parameters; the checked result carries width and product facts. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r w : ℕ}

structure FixedRankOutput (n p r : ℕ) where
  width : ℕ
  width_le : width ≤ r
  left : Matrix (Fin n) (Fin width) ℝ
  right : Matrix (Fin width) (Fin p) ℝ
  product : Matrix (Fin n) (Fin p) ℝ
  product_eq : product = left*right

theorem FixedRankOutput.rank_le (out : FixedRankOutput n p r) : out.product.rank ≤ r := by
  rw [out.product_eq]
  calc
    _ ≤ out.right.rank := Matrix.rank_mul_le_right _ _
    _ ≤ out.width := by simpa only [Fintype.card_fin] using Matrix.rank_le_card_height out.right
    _ ≤ r := out.width_le

def zeroFixedRankOutput (n p r : ℕ) : FixedRankOutput n p r where
  width := 0
  width_le := Nat.zero_le _
  left := 0
  right := 0
  product := 0
  product_eq := by simp

def projectionOutputProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) : ArithmeticProgram (FixedRankOutput n p r) := do
  let leftProduct ← ((kernels w n m).program Uᵀ A).certify
  let right ← ((kernels w m p).program leftProduct.val B).certify
  let C ← ((kernels n w p).program U right.val).certify
  .pure { width := w
          width_le := hw
          left := U
          right := right.val
          product := C.val
          product_eq := C.property.trans (ArithmeticKernel.program_eval _ _ _) }

theorem projectionOutputProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) :
    (projectionOutputProgram kernels A B U hw).eval =
      { width := w
        width_le := hw
        left := U
        right := (Uᵀ*A)*B
        product := U*((Uᵀ*A)*B)
        product_eq := rfl } := by
  simp only [projectionOutputProgram,eval_bind,eval_pure,certify_eval,ArithmeticKernel.program_eval]

theorem projectionOutputProgram_product (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) :
    (projectionOutputProgram kernels A B U hw).eval.product = U*(Uᵀ*(A*B)) := by
  simp only [projectionOutputProgram,eval_bind,eval_pure,certify_eval,ArithmeticKernel.program_eval,
    Matrix.mul_assoc]

theorem projectionOutputProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) :
    (projectionOutputProgram kernels A B U hw).admissible := by
  simp only [projectionOutputProgram,admissible_bind,certify_admissible,
    ArithmeticKernel.program_admissible,admissible_pure,and_self]

theorem projectionOutputProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) :
    (projectionOutputProgram kernels A B U hw).work =
      (kernels w n m).cost+(kernels w m p).cost+(kernels n w p).cost := by
  simp only [projectionOutputProgram,work_bind,certify_work,ArithmeticKernel.program_work,work_pure,add_zero]
  omega

theorem projectionOutputProgram_exact (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) (hspan : U*Uᵀ*(A*B) = A*B) :
    (projectionOutputProgram kernels A B U hw).eval.product = A*B := by
  rw [projectionOutputProgram_product,← Matrix.mul_assoc,hspan]

end
end HierarchicalAbsoluteSpectral
