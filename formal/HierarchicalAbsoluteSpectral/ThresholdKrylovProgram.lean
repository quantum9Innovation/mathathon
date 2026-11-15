import HierarchicalAbsoluteSpectral.ThresholdKrylovRitz
import HierarchicalAbsoluteSpectral.CoarseAlgebraRangeProgram

set_option backward.isDefEq.respectTransparency false

/-! Actual Krylov range and compressed Gram construction. Every range basis
is produced by the checked finite zero-pivot Gram algorithm. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open ArithmeticProgram hiding pure
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {k r : ℕ}

def flattenKrylovBlocks (q : ℕ) (blocks : Fin (q+1) → Matrix (Fin k) (Fin r) ℝ) :
    Matrix (Fin k) (Fin ((q+1)*r)) ℝ :=
  Matrix.of (fun i s => blocks (finProdFinEquiv.symm s).1 i (finProdFinEquiv.symm s).2)

def flatBlockKrylov (T : Core k) (Ω : Matrix (Fin k) (Fin r) ℝ) (q : ℕ) :
    Matrix (Fin k) (Fin ((q+1)*r)) ℝ :=
  flattenKrylovBlocks q (fun s => T^s.val*Ω)

theorem flatBlockKrylov_unflatten (T : Core k) (Ω : Matrix (Fin k) (Fin r) ℝ) (q : ℕ) :
    (flatBlockKrylov T Ω q).submatrix id finProdFinEquiv = blockKrylov T Ω q := by
  ext i sb
  simp only [flatBlockKrylov, flattenKrylovBlocks, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_apply_apply, id_eq, blockKrylov]

def krylovRangeProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (action : MatrixAction T r) (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    ArithmeticProgram (OrthogonalRange (flatBlockKrylov T Ω q)) := do
  let blocks ← certify (krylovBlocksProgram action.program q Ω)
  let Y := flattenKrylovBlocks q blocks.val
  have hY : Y = flatBlockKrylov T Ω q := by
    dsimp only [Y]
    rw [show blocks.val = (fun s => T^s.val*Ω) from
      blocks.property.trans (krylovBlocksProgram_eval T action.program action.correct q Ω)]
    rfl
  let out ← orthogonalRangeProgram kernels Y
  .pure (hY ▸ out)

theorem krylovRangeProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (action : MatrixAction T r) (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    (krylovRangeProgram kernels T action q Ω).admissible := by
  simp only [krylovRangeProgram, admissible_bind, certify_admissible, admissible_pure, and_true]
  exact ⟨krylovBlocksProgram_admissible action.program action.valid q Ω,
    orthogonalRangeProgram_admissible kernels _⟩

theorem krylovRange_unflatten_spans (T : Core k) (Ω : Matrix (Fin k) (Fin r) ℝ) (q : ℕ)
    (out : OrthogonalRange (flatBlockKrylov T Ω q)) :
    blockKrylov T Ω q = out.basis*(out.coefficients.submatrix id finProdFinEquiv) := by
  have hh := congrArg (fun M : Matrix (Fin k) (Fin ((q+1)*r)) ℝ =>
    M.submatrix id finProdFinEquiv) out.spans
  rw [flatBlockKrylov_unflatten] at hh
  rw [Matrix.submatrix_mul _ _ id id finProdFinEquiv Function.bijective_id] at hh
  simpa only [Matrix.submatrix_id_id] using hh

structure KrylovQueryData (T : Core k) (Ω : Matrix (Fin k) (Fin r) ℝ) (q : ℕ) where
  range : OrthogonalRange (flatBlockKrylov T Ω q)
  compression : Core range.dimension
  compression_eq : compression = range.basisᵀ*(T*T)*range.basis
  compression_posSemidef : compression.PosSemidef

def krylovQueryDataProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) : ArithmeticProgram (KrylovQueryData T Ω q) := do
  let out ← krylovRangeProgram kernels T (actions r) q Ω
  let TU ← certify ((actions out.dimension).program out.basis)
  let C ← certify ((kernels out.dimension k out.dimension).program TU.valᵀ TU.val)
  have hTU : TU.val = T*out.basis := TU.property.trans ((actions out.dimension).correct _)
  have hC : C.val = TU.valᵀ*TU.val := C.property.trans (ArithmeticKernel.program_eval _ _ _)
  have hcomp : C.val = out.basisᵀ*(T*T)*out.basis := by
    rw [hC, hTU]
    have ht : Tᵀ = T := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hT.eq
    simp only [Matrix.transpose_mul, ht, Matrix.mul_assoc]
  have hPSD : C.val.PosSemidef := by
    rw [hC]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self TU.val
  .pure ⟨out,C.val,hcomp,hPSD⟩

theorem krylovQueryDataProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    (krylovQueryDataProgram kernels T hT actions q Ω).admissible := by
  simp only [krylovQueryDataProgram, admissible_bind, certify_admissible,
    krylovRangeProgram_admissible, MatrixAction.valid, ArithmeticKernel.program_admissible,
    admissible_pure, and_self]

theorem computed_thresholdRitzValue_of_capture
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.PosSemidef) (actions : ∀ b, MatrixAction T b) (j : Fin k)
    (htarget : 0 < orderedEigenvalue T hT.isHermitian j)
    (ε R : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1) (hR : 1 ≤ R) (q : ℕ)
    (hstop : 10*R/ε ≤ strongFilterDenominator (ε/100) q)
    (Ω : Matrix (Fin k) (Fin r) ℝ) (H : Matrix (Fin r) (Fin (j.val+1)) ℝ)
    (hhead : (((strongSpectralQ T (Matrix.isSymmetric_toEuclideanLin_iff.mpr hT.isHermitian))ᵀ*Ω).submatrix
      (krylovHeadEmbedding j) id)*H = 1)
    (hΩ : ‖((strongSpectralQ T (Matrix.isSymmetric_toEuclideanLin_iff.mpr hT.isHermitian))ᵀ*Ω)*H‖ ≤ R) :
    let data := (krylovQueryDataProgram kernels T hT.isHermitian actions q Ω).eval
    (1-ε)*(orderedEigenvalue T hT.isHermitian j)^2 ≤ thresholdRitzValue T hT.isHermitian data.range.basis j := by
  let data := (krylovQueryDataProgram kernels T hT.isHermitian actions q Ω).eval
  apply thresholdRitzValue_of_capture T hT j htarget ε R hε hε' hR q hstop Ω H
    data.range.basis (data.range.coefficients.submatrix id finProdFinEquiv)ᵀ data.range.orthogonal
  · simpa only [Matrix.transpose_transpose] using krylovRange_unflatten_spans T Ω q data.range
  · exact hhead
  · exact hΩ

end
end HierarchicalAbsoluteSpectral
