import HierarchicalAbsoluteSpectral.MainStatementsFixed
import HierarchicalAbsoluteSpectral.MassSpectrumExactRange

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped MatrixOrder
variable {n m p k r w : ℕ}

def physicalRangeProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z w)
    (U : Matrix (Fin k) (Fin w) ℝ) : ArithmeticProgram (OrthogonalRange (Z*U)) := do
  let Y ← (PZ.program U).certify
  let out ← orthogonalRangeProgram kernels Y.val
  have hY : Y.val=Z*U := Y.property.trans (PZ.correct U)
  .pure (hY ▸ out)

theorem physicalRangeProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z w)
    (U : Matrix (Fin k) (Fin w) ℝ) : (physicalRangeProgram kernels PZ U).admissible := by
  simp only [physicalRangeProgram,admissible_bind,certify_admissible,PZ.valid,
    orthogonalRangeProgram_admissible,admissible_pure,and_self]

/-- The initializer's exact branch uses the computed width-r range and
the ordinary final factor/dense-output compiler. -/
def exactPhysicalOutputProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z w)
    (U : Matrix (Fin k) (Fin w) ℝ) (hw : w≤r) : ArithmeticProgram (FixedRankOutput n p r) := do
  let out ← physicalRangeProgram kernels PZ U
  projectionOutputProgram kernels A B out.basis (out.dimension_le_cols.trans hw)

theorem exactPhysicalOutputProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z w)
    (U : Matrix (Fin k) (Fin w) ℝ) (hw : w≤r) :
    (exactPhysicalOutputProgram kernels A B PZ U hw).admissible := by
  simp only [exactPhysicalOutputProgram,admissible_bind,physicalRangeProgram_admissible,
    projectionOutputProgram_admissible,and_self]

theorem exactPhysicalOutputProgram_exact (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (Z : Matrix (Fin n) (Fin k) ℝ) (Bbar : Matrix (Fin k) (Fin p) ℝ)
    (hsupport : A*B=Z*Bbar) (Q₀ : Core k) (PZ : MatrixAction Z w)
    (U : Matrix (Fin k) (Fin w) ℝ) (hw : w≤r)
    (c : ℝ) (hc : 0<c) (hgram : c • (Bbar*Bbarᵀ)≤Q₀)
    (hzero : initializerValue Q₀ U=0) :
    (exactPhysicalOutputProgram kernels A B PZ U hw).eval.product=A*B := by
  simp only [exactPhysicalOutputProgram,eval_bind,projectionOutputProgram_product]
  rw [hsupport]
  exact initializer_exact_physical_range Z Bbar Q₀ U c hc hgram hzero
    (physicalRangeProgram kernels PZ U).eval

def supportExactOutputProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z k) (hk : k ≤ r) :
    ArithmeticProgram (FixedRankOutput n p r) :=
  exactPhysicalOutputProgram kernels A B PZ (1 : Core k) hk

theorem supportExactOutputProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z k) (hk : k ≤ r) :
    (supportExactOutputProgram kernels A B PZ hk).admissible :=
  exactPhysicalOutputProgram_admissible kernels A B PZ _ hk

theorem supportExactOutputProgram_exact (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (Z : Matrix (Fin n) (Fin k) ℝ) (Bbar : Matrix (Fin k) (Fin p) ℝ)
    (hsupport : A*B=Z*Bbar) (PZ : MatrixAction Z k) (hk : k ≤ r) :
    (supportExactOutputProgram kernels A B PZ hk).eval.product=A*B := by
  simp only [supportExactOutputProgram,exactPhysicalOutputProgram,ArithmeticProgram.eval_bind,
    projectionOutputProgram_product]
  rw [hsupport]
  let out := (physicalRangeProgram kernels PZ (1 : Core k)).eval
  have hp := congrArg (fun Y : Matrix (Fin n) (Fin k) ℝ => Y*Bbar) out.projection_exact
  simpa only [Matrix.mul_one,Matrix.mul_assoc] using hp

end
end HierarchicalAbsoluteSpectral
