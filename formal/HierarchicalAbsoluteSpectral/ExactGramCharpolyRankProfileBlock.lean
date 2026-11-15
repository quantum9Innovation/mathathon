import HierarchicalAbsoluteSpectral.ExactGramCharpolyRankProfile

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix

namespace FieldPSDPrincipalData

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {A : Matrix m m ℝ}

theorem gram_symmetric (p : FieldPSDPrincipalData A) (hA : Aᵀ = A) :
    p.gramᵀ = p.gram := by
  change Aᵀ.submatrix p.selected p.selected = A.submatrix p.selected p.selected
  rw [hA]

theorem inverse_symmetric (p : FieldPSDPrincipalData A) (hA : Aᵀ = A) :
    p.inverseᵀ = p.inverse := by
  have hi : p.inverseᵀ * p.gram = 1 := by
    simpa only [Matrix.transpose_mul, p.gram_symmetric hA, Matrix.transpose_one]
      using congrArg Matrix.transpose p.gram_inverse
  calc
    _ = p.inverseᵀ * (p.gram * p.inverse) := by rw [p.gram_inverse, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hi, Matrix.one_mul]

theorem offDiagonal_range (p : FieldPSDPrincipalData A)
    (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef) :
    p.coordinatesᵀ * B.submatrix p.selected id = B := by
  let E := (1 : Matrix m m ℝ).submatrix p.selected id
  let P := 1 - p.coordinatesᵀ * E
  have hEA : E * A = p.gram * p.coordinates := by
    calc
      _ = A.submatrix p.selected id := Matrix.one_submatrix_mul p.selected (Equiv.refl m) A
      _ = _ := p.selected_rows
  have hPA : P * A = 0 := by
    change (1 - p.coordinatesᵀ * E) * A = 0
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hEA,
      ← Matrix.mul_assoc, (show p.coordinatesᵀ * p.gram * p.coordinates = A from p.decomposition), sub_self]
  let Z : Matrix (m ⊕ n) m ℝ := Matrix.fromRows Pᵀ 0
  have hz : Zᵀ * Matrix.fromBlocks A B Bᵀ C * Z = 0 := by
    dsimp only [Z]
    rw [Matrix.transpose_fromRows, Matrix.transpose_transpose, Matrix.transpose_zero,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, hPA]
  have hDZ := psd_congruence_zero_mul_zero _ hD Z hz
  have hB : Bᵀ * Pᵀ = 0 := by
    ext i j
    have he := congrArg (fun M => M (Sum.inr i) j) hDZ
    simpa only [Z, Matrix.fromBlocks_mul_fromRows, Matrix.mul_zero, add_zero,
      Matrix.fromRows_apply_inr, Matrix.zero_apply] using he
  have hPB : P * B = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using congrArg Matrix.transpose hB
  have hEB : E * B = B.submatrix p.selected id := by
    exact Matrix.one_submatrix_mul p.selected (Equiv.refl m) B
  dsimp only [P] at hPB
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hEB] at hPB
  exact (sub_eq_zero.mp hPB).symm

def schur (p : FieldPSDPrincipalData A) (B : Matrix m n ℝ) (C : Matrix n n ℝ) :
    Matrix n n ℝ := C - (B.submatrix p.selected id)ᵀ *
      (p.inverse * B.submatrix p.selected id)

theorem schur_posSemidef (p : FieldPSDPrincipalData A)
    (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef) : (p.schur B C).PosSemidef := by
  let E := (1 : Matrix m m ℝ).submatrix p.selected id
  let H := p.inverse * B.submatrix p.selected id
  let Z : Matrix (m ⊕ n) n ℝ := Matrix.fromRows (-(Eᵀ * H)) 1
  have hEA : E * A = p.gram * p.coordinates := by
    calc
      _ = A.submatrix p.selected id := Matrix.one_submatrix_mul p.selected (Equiv.refl m) A
      _ = _ := p.selected_rows
  have hGH : p.gram * H = B.submatrix p.selected id := by
    simp only [H, ← Matrix.mul_assoc, p.gram_inverse, Matrix.one_mul]
  have hA : Aᵀ = A := by
    have hh := (hD.submatrix Sum.inl).isHermitian.eq
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (show Aᴴ = A from hh)
  have hHB : Hᵀ * p.gram = (B.submatrix p.selected id)ᵀ := by
    simpa only [Matrix.transpose_mul, p.gram_symmetric hA] using congrArg Matrix.transpose hGH
  have hEB : E * B = B.submatrix p.selected id := by
    exact Matrix.one_submatrix_mul p.selected (Equiv.refl m) B
  have htop : -(Hᵀ * E) * A + Bᵀ = 0 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, hEA, ← Matrix.mul_assoc, hHB]
    have hh := congrArg Matrix.transpose (p.offDiagonal_range B C hD)
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at hh
    rw [hh]
    module
  have heq : Zᵀ * Matrix.fromBlocks A B Bᵀ C * Z = p.schur B C := by
    dsimp only [Z]
    rw [Matrix.transpose_fromRows, Matrix.transpose_neg, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_one,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.one_mul, htop, Matrix.zero_mul, Matrix.mul_one, zero_add]
    rw [Matrix.neg_mul, Matrix.mul_assoc, hEB]
    change -(Hᵀ * B.submatrix p.selected id) + C =
      C - (B.submatrix p.selected id)ᵀ * H
    have hs : Hᵀ * B.submatrix p.selected id = (B.submatrix p.selected id)ᵀ * H := by
      calc
        _ = Hᵀ * (p.gram * H) := congrArg (Hᵀ * ·) hGH.symm
        _ = _ := by rw [← Matrix.mul_assoc, hHB]
    rw [hs]
    module
  have hp := hD.conjTranspose_mul_mul_same Z
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, heq] using hp

end FieldPSDPrincipalData

end
end HierarchicalAbsoluteSpectral
