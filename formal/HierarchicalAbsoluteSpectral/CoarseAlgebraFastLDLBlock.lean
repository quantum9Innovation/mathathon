import HierarchicalAbsoluteSpectral.CoarseAlgebraInertiaBlock
import HierarchicalAbsoluteSpectral.CoarseAlgebraLeading

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix

structure RegularCongruenceData {n : Type} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℝ) extends CongruenceDiagonalData D where
  nonzero : ∀ i, diagonal i ≠ 0

namespace RegularCongruenceData

variable {n : Type} [Fintype n] [DecidableEq n] {D : Matrix n n ℝ}

abbrev inverseMatrix (out : RegularCongruenceData D) : Matrix n n ℝ :=
  out.basis*Matrix.diagonal (fun i => (out.diagonal i)⁻¹)*out.basisᵀ

theorem undo (out : RegularCongruenceData D) :
    D = out.inverseᵀ*Matrix.diagonal out.diagonal*out.inverse := by
  calc
    _ = (out.basis*out.inverse)ᵀ*D*(out.basis*out.inverse) := by rw [out.right_inverse]; simp
    _ = out.inverseᵀ*(out.basisᵀ*D*out.basis)*out.inverse := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = _ := by rw [out.congruence]

theorem inverseMatrix_left (out : RegularCongruenceData D) : out.inverseMatrix*D = 1 := by
  have hd : Matrix.diagonal (fun i => (out.diagonal i)⁻¹)*Matrix.diagonal out.diagonal = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp [out.nonzero i]
    · simp [hij]
  calc
    _ = out.inverseMatrix*(out.inverseᵀ*Matrix.diagonal out.diagonal*out.inverse) :=
      congrArg (out.inverseMatrix*·) out.undo
    _ = out.basis*Matrix.diagonal (fun i => (out.diagonal i)⁻¹)*
        (out.inverse*out.basis)ᵀ*Matrix.diagonal out.diagonal*out.inverse := by
      simp only [inverseMatrix, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by
      rw [out.left_inverse, Matrix.transpose_one, Matrix.mul_one,
        Matrix.mul_assoc out.basis, hd, Matrix.mul_one, out.right_inverse]

theorem inverseMatrix_eq_inv (out : RegularCongruenceData D) : out.inverseMatrix = D⁻¹ :=
  (Matrix.inv_eq_left_inv out.inverseMatrix_left).symm

theorem inverseMatrix_transpose (out : RegularCongruenceData D) :
    out.inverseMatrixᵀ = out.inverseMatrix := by
  simp only [inverseMatrix, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

def cast {E : Matrix n n ℝ} (out : RegularCongruenceData D) (h : D = E) : RegularCongruenceData E := h ▸ out

def reindex {m : Type} [Fintype m] [DecidableEq m]
    (out : RegularCongruenceData D) (e : m ≃ n) : RegularCongruenceData (D.submatrix e e) where
  toCongruenceDiagonalData := out.toCongruenceDiagonalData.reindex e
  nonzero := fun i => out.nonzero (e i)

end RegularCongruenceData

def regularBlockSchur {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    {A : Matrix m m ℝ} (left : RegularCongruenceData A) (B : Matrix m n ℝ)
    (C : Matrix n n ℝ) : Matrix n n ℝ := C-Bᵀ*(left.inverseMatrix*B)

def regularBlockData {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℝ} (left : RegularCongruenceData A)
    (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    {T : Matrix n n ℝ} (right : RegularCongruenceData T) (hT : T = regularBlockSchur left B C) :
    RegularCongruenceData (Matrix.fromBlocks A B Bᵀ C) := by
  let W := left.inverseMatrix*B
  have hAW : A*W = B := by
    have hu : IsUnit A.det := by
      have he := congrArg Matrix.det left.inverseMatrix_left
      rw [Matrix.det_mul, Matrix.det_one] at he
      apply isUnit_iff_ne_zero.mpr
      intro hz
      rw [hz, mul_zero] at he
      norm_num at he
    dsimp only [W]
    rw [left.inverseMatrix_eq_inv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hu, Matrix.one_mul]
  have hWA : Wᵀ*A = Bᵀ := by
    have hAt : Aᵀ = A := by
      have he := left.undo
      calc
        _ = (left.inverseᵀ*Matrix.diagonal left.diagonal*left.inverse)ᵀ := congrArg Matrix.transpose he
        _ = A := by simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose, Matrix.mul_assoc] using he.symm
    simpa only [Matrix.transpose_mul, hAt] using congrArg Matrix.transpose hAW
  let J := Matrix.fromBlocks (1 : Matrix m m ℝ) (-W) 0 (1 : Matrix n n ℝ)
  let Q := Matrix.fromBlocks left.basis (0 : Matrix m n ℝ) 0 right.basis
  have hSchur : Jᵀ*Matrix.fromBlocks A B Bᵀ C*J = Matrix.fromBlocks A 0 0 T := by
    dsimp only [J]
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_neg, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
      add_zero, zero_add, hWA, neg_add_cancel, hAW, neg_zero]
    rw [hT]
    simp only [regularBlockSchur, W, Matrix.transpose_mul, left.inverseMatrix_transpose,
      Matrix.transpose_transpose,Matrix.diagonal_transpose,Matrix.mul_assoc, sub_eq_add_neg, add_comm]
  refine ⟨⟨Matrix.fromBlocks left.basis (-(W*right.basis)) 0 right.basis,
      Matrix.fromBlocks left.inverse (left.inverse*W) 0 right.inverse,
      Sum.elim left.diagonal right.diagonal, ?_, ?_, ?_⟩, ?_⟩
  · rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, left.left_inverse,
      right.left_inverse, Matrix.mul_neg]
    have hc : left.inverse*(W*right.basis) = left.inverse*W*right.basis := (Matrix.mul_assoc _ _ _).symm
    rw [hc]; simp
  · rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, left.right_inverse,
      right.right_inverse, Matrix.neg_mul]
    simp only [← Matrix.mul_assoc, left.right_inverse, Matrix.one_mul]
    simp only [Matrix.mul_assoc, right.right_inverse, Matrix.mul_one, add_neg_cancel]
    simp
  · have hP : Matrix.fromBlocks left.basis (-(W*right.basis)) 0 right.basis = J*Q := by
      simp [J, Q, Matrix.fromBlocks_multiply, Matrix.neg_mul]
    rw [hP]
    calc
      _ = Qᵀ*(Jᵀ*Matrix.fromBlocks A B Bᵀ C*J)*Q := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [hSchur]
        dsimp only [Q]
        rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
        simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
          left.congruence, right.congruence]
        exact Matrix.fromBlocks_diagonal _ _
  · intro i
    cases i with
    | inl i => exact left.nonzero i
    | inr i => exact right.nonzero i

end
end HierarchicalAbsoluteSpectral
