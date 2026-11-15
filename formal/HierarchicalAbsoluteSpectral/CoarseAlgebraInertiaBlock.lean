import HierarchicalAbsoluteSpectral.CoarseAlgebraInertia
import HierarchicalAbsoluteSpectral.CholeskyFinite

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix

structure CongruenceDiagonalData {n : Type} [Fintype n] [DecidableEq n] (D : Matrix n n ℝ) where
  basis : Matrix n n ℝ
  inverse : Matrix n n ℝ
  diagonal : n → ℝ
  left_inverse : inverse*basis = 1
  right_inverse : basis*inverse = 1
  congruence : basisᵀ*D*basis = Matrix.diagonal diagonal

def FiniteCongruenceDiagonal.toData {n : ℕ} {D : Core n} (out : FiniteCongruenceDiagonal D) :
    CongruenceDiagonalData D :=
  ⟨out.basis,out.inverse,out.diagonal,out.left_inverse,out.right_inverse,out.congruence⟩

def CongruenceDiagonalData.toFinite {n : ℕ} {D : Core n} (out : CongruenceDiagonalData D) :
    FiniteCongruenceDiagonal D :=
  ⟨out.basis,out.inverse,out.diagonal,out.left_inverse,out.right_inverse,out.congruence⟩

namespace CongruenceDiagonalData

def cast {n : Type} [Fintype n] [DecidableEq n] {D E : Matrix n n ℝ}
    (out : CongruenceDiagonalData D) (h : D = E) : CongruenceDiagonalData E := h ▸ out

def reindex {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {D : Matrix n n ℝ} (out : CongruenceDiagonalData D) (e : m ≃ n) :
    CongruenceDiagonalData (D.submatrix e e) where
  basis := out.basis.submatrix e e
  inverse := out.inverse.submatrix e e
  diagonal := out.diagonal ∘ e
  left_inverse := by rw [Matrix.submatrix_mul_equiv, out.left_inverse, Matrix.submatrix_one_equiv]
  right_inverse := by rw [Matrix.submatrix_mul_equiv, out.right_inverse, Matrix.submatrix_one_equiv]
  congruence := by
    change out.basisᵀ.submatrix e e*D.submatrix e e*out.basis.submatrix e e = _
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, out.congruence]
    exact Matrix.submatrix_diagonal_equiv _ _

def ofZero {n : Type} [Fintype n] [DecidableEq n] (D : Matrix n n ℝ) (hD : D = 0) :
    CongruenceDiagonalData D where
  basis := 1
  inverse := 1
  diagonal := fun _ => 0
  left_inverse := by simp
  right_inverse := by simp
  congruence := by simp [hD]

def conjugate {n : Type} [Fintype n] [DecidableEq n] (D U V : Matrix n n ℝ)
    (hVU : V*U = 1) (hUV : U*V = 1) (out : CongruenceDiagonalData (Uᵀ*D*U)) :
    CongruenceDiagonalData D where
  basis := U*out.basis
  inverse := out.inverse*V
  diagonal := out.diagonal
  left_inverse := by
    calc
      _ = out.inverse*(V*U)*out.basis := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hVU, Matrix.mul_one, out.left_inverse]
  right_inverse := by
    calc
      _ = U*(out.basis*out.inverse)*V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [out.right_inverse, Matrix.mul_one, hUV]
  congruence := by
    calc
      _ = out.basisᵀ*(Uᵀ*D*U)*out.basis := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := out.congruence

end CongruenceDiagonalData

def scalarSchur {n : Type} [Fintype n] (d : ℝ) (B : Matrix (Fin 1) n ℝ)
    (C : Matrix n n ℝ) : Matrix n n ℝ := C-Bᵀ*(d⁻¹ • B)

def scalarPivotData {n : Type} [Fintype n] [DecidableEq n]
    (d : ℝ) (hd : d ≠ 0) (B : Matrix (Fin 1) n ℝ) (C : Matrix n n ℝ)
    (out : CongruenceDiagonalData (scalarSchur d B C)) :
    CongruenceDiagonalData (Matrix.fromBlocks (d • (1 : Core 1)) B Bᵀ C) := by
  let W := d⁻¹ • B
  let J := Matrix.fromBlocks (1 : Core 1) (-W) 0 (1 : Matrix n n ℝ)
  let Q := Matrix.fromBlocks (1 : Core 1) (0 : Matrix (Fin 1) n ℝ) 0 out.basis
  have hdW : (d • (1 : Core 1))*W = B := by
    simp only [W, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ hd, one_smul]
  have hSchur : Jᵀ*Matrix.fromBlocks (d • (1 : Core 1)) B Bᵀ C*J =
      Matrix.fromBlocks (d • (1 : Core 1)) 0 0 (scalarSchur d B C) := by
    have hWt : Wᵀ*(d • (1 : Core 1)) = Bᵀ := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_one]
        using congrArg Matrix.transpose hdW
    dsimp only [J]
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_neg,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, hWt, neg_add_cancel, hdW]
    simp only [scalarSchur, W, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      sub_eq_add_neg, add_comm, neg_zero, add_zero]
  refine ⟨Matrix.fromBlocks (1 : Core 1) (-(W*out.basis)) 0 out.basis,
    Matrix.fromBlocks (1 : Core 1) W 0 out.inverse,
    Sum.elim (fun _ => d) out.diagonal, ?_, ?_, ?_⟩
  · rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, out.left_inverse, neg_add_cancel]
    simp
  · rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, Matrix.neg_mul, Matrix.mul_assoc, out.right_inverse, add_neg_cancel]
    simp
  · have hP : Matrix.fromBlocks (1 : Core 1) (-(W*out.basis)) 0 out.basis = J*Q := by
      simp only [J, Q, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
        Matrix.zero_mul, Matrix.mul_zero, Matrix.neg_mul, add_zero, zero_add]
    rw [hP]
    calc
      _ = Qᵀ*(Jᵀ*Matrix.fromBlocks (d • (1 : Core 1)) B Bᵀ C*J)*Q := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [hSchur]
        dsimp only [Q]
        rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
        simp only [Matrix.transpose_one, Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero,
          Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, out.congruence]
        rw [← Matrix.fromBlocks_diagonal]
        congr 1
        ext i j
        fin_cases i
        fin_cases j
        simp

end
end HierarchicalAbsoluteSpectral
