import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftCertificate
import HierarchicalAbsoluteSpectral.MainStatementsFixed

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator

structure ExactGramAppendixLiftData {n m p k r : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) {K : Core k} (out : FiniteCongruenceDiagonal K) where
  selection : ExactGramNegativeSelection out.diagonal
  physical : Matrix (Fin n) (Fin selection.width) ℝ
  physical_eq : physical = A*exactGramDualSmall T out selection
  range : OrthogonalRange physical
  output : FixedRankOutput n p r
  projection : output.product = range.basis*(range.basisᵀ*(A*B))

def exactGramAppendixLiftDataProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) {K : Core k} (out : FiniteCongruenceDiagonal K)
    (hr : out.negativeCount ≤ r) : ArithmeticProgram (ExactGramAppendixLiftData A B T out (r:=r)) := do
  let s ← exactGramNegativeSelectionProgram out.diagonal
  let small ← certify ((kernels m k s.width).program T (out.inverseᵀ.submatrix id s.selected))
  let Y ← certify ((kernels n m s.width).program A small.val)
  have hY : Y.val = A*exactGramDualSmall T out s := by
    rw [Y.property, ArithmeticKernel.program_eval, small.property, ArithmeticKernel.program_eval]
    rfl
  let qr ← orthogonalRangeProgram kernels Y.val
  have hw : qr.dimension ≤ r :=
    qr.dimension_le_cols.trans (by
      calc s.width = out.negativeCount := s.width_eq
           _ ≤ r := hr)
  let result ← certify (projectionOutputProgram kernels A B qr.basis hw)
  ArithmeticProgram.pure {
    selection := s
    physical := Y.val
    physical_eq := hY
    range := qr
    output := result.val
    projection := by rw [result.property, projectionOutputProgram_product] }

def exactGramAppendixLiftProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) {K : Core k} (out : FiniteCongruenceDiagonal K)
    (hr : out.negativeCount ≤ r) : ArithmeticProgram (FixedRankOutput n p r) := do
  let data ← exactGramAppendixLiftDataProgram kernels A B T out hr
  ArithmeticProgram.pure data.output

theorem exactGramAppendixLiftDataProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) {K : Core k} (out : FiniteCongruenceDiagonal K)
    (hr : out.negativeCount ≤ r) : (exactGramAppendixLiftDataProgram kernels A B T out hr).admissible := by
  simp only [exactGramAppendixLiftDataProgram, admissible_bind, certify_admissible,
    exactGramNegativeSelectionProgram_admissible, ArithmeticKernel.program_admissible,
    orthogonalRangeProgram_admissible, projectionOutputProgram_admissible, admissible_pure, and_self]

theorem exactGramAppendixLiftProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) {K : Core k} (out : FiniteCongruenceDiagonal K)
    (hr : out.negativeCount ≤ r) : (exactGramAppendixLiftProgram kernels A B T out hr).admissible := by
  simp only [exactGramAppendixLiftProgram, admissible_bind, exactGramAppendixLiftDataProgram_admissible,
    admissible_pure, and_self]

theorem exactGramAppendixLiftProgram_error
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (t : ℝ) (ht : 0 ≤ t)
    (hZ : (A*T)ᵀ*(A*T) = 1) (hcov : (A*B)*(A*B)ᵀ = (A*T)*Hc*(A*T)ᵀ)
    (out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc)) (hr : out.negativeCount ≤ r) :
    ‖A*B - (exactGramAppendixLiftProgram kernels A B T out hr).eval.product‖ ≤ Real.sqrt t := by
  let data := (exactGramAppendixLiftDataProgram kernels A B T out hr).eval
  change ‖A*B-data.output.product‖ ≤ Real.sqrt t
  rw [data.projection]
  apply projection_error_of_complement_bound (A*B) data.range.basis data.range.orthogonal
    (Real.sqrt t) (Real.sqrt_nonneg _)
  intro x hx
  have hz : ((A*T)*out.inverseᵀ.submatrix id data.selection.selected)ᵀ *ᵥ x = 0 := by
    have hphys : data.physical = (A*T)*out.inverseᵀ.submatrix id data.selection.selected := by
      rw [data.physical_eq]
      simp only [exactGramDualSmall, Matrix.mul_assoc]
    rw [← hphys, data.range.spans, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have hh := exactGramAppendixLift_rayleigh (A*B) (A*T) Hc t ht hZ hcov out data.selection x hz
  simpa only [Real.sq_sqrt ht] using hh

theorem exactGramAppendixLiftProgram_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) {K : Core k} (out : FiniteCongruenceDiagonal K)
    (hr : out.negativeCount ≤ r) :
    (exactGramAppendixLiftProgram kernels A B T out hr).work =
      (exactGramAppendixLiftDataProgram kernels A B T out hr).work := by
  simp only [exactGramAppendixLiftProgram, work_bind, work_pure, add_zero]

end
end HierarchicalAbsoluteSpectral
