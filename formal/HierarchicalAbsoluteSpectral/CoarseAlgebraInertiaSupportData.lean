import HierarchicalAbsoluteSpectral.CoarseAlgebraInertiaBlock
import HierarchicalAbsoluteSpectral.CoarseAlgebraRangeProgram

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
variable {n : ℕ}

structure InertiaSupport (D : Core n) where
  dimension : ℕ
  nullity : ℕ
  dimension_le : dimension ≤ n
  total : dimension+nullity = n
  basis : Matrix (Fin n) (Fin dimension) ℝ
  complement : Matrix (Fin n) (Fin nullity) ℝ
  basis_orthogonal : basisᵀ*basis = 1
  complement_orthogonal : complementᵀ*complement = 1
  cross_zero : basisᵀ*complement = 0
  projectors : basis*basisᵀ+complement*complementᵀ = 1
  compressed : Core dimension
  compressed_eq : compressed = basisᵀ*D*basis
  compressed_isUnit : IsUnit compressed.det
  decomposition : D = basis*compressed*basisᵀ

namespace InertiaSupport

variable {D : Core n}

def indexEquiv (out : InertiaSupport D) : Fin out.dimension ⊕ Fin out.nullity ≃ Fin n :=
  finSumFinEquiv.trans (finCongr out.total)

def frame (out : InertiaSupport D) : Core n :=
  (Matrix.fromCols out.basis out.complement).submatrix id out.indexEquiv.symm

theorem frame_orthogonal (out : InertiaSupport D) : out.frameᵀ*out.frame = 1 := by
  have hc : out.complementᵀ*out.basis = 0 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero]
      using congrArg Matrix.transpose out.cross_zero
  have hg : (Matrix.fromCols out.basis out.complement)ᵀ*
      (Matrix.fromCols out.basis out.complement) = 1 := by
    rw [Matrix.transpose_fromCols,Matrix.fromRows_mul_fromCols]
    rw [out.basis_orthogonal,out.complement_orthogonal,out.cross_zero,hc]
    exact Matrix.fromBlocks_one
  change (Matrix.fromCols out.basis out.complement)ᵀ.submatrix out.indexEquiv.symm (Equiv.refl _)*
    (Matrix.fromCols out.basis out.complement).submatrix (Equiv.refl _) out.indexEquiv.symm = 1
  rw [Matrix.submatrix_mul_equiv,hg,Matrix.submatrix_one_equiv]

theorem frame_coorthogonal (out : InertiaSupport D) : out.frame*out.frameᵀ = 1 := by
  have hg : (Matrix.fromCols out.basis out.complement)*
      (Matrix.fromCols out.basis out.complement)ᵀ = 1 := by
    rw [Matrix.transpose_fromCols,Matrix.fromCols_mul_fromRows]
    exact out.projectors
  change (Matrix.fromCols out.basis out.complement).submatrix id out.indexEquiv.symm*
    (Matrix.fromCols out.basis out.complement)ᵀ.submatrix out.indexEquiv.symm id = 1
  rw [Matrix.submatrix_mul_equiv,hg]
  rfl

theorem frame_congruence (out : InertiaSupport D) : out.frameᵀ*D*out.frame =
    (Matrix.fromBlocks out.compressed (0 : Matrix (Fin out.dimension) (Fin out.nullity) ℝ)
      0 (0 : Core out.nullity)).submatrix out.indexEquiv.symm out.indexEquiv.symm := by
  have hc : out.complementᵀ*out.basis = 0 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero]
      using congrArg Matrix.transpose out.cross_zero
  have hDN : D*out.complement = 0 := by
    calc
      _ = out.basis*out.compressed*out.basisᵀ*out.complement := congrArg (·*out.complement) out.decomposition
      _ = 0 := by simp only [Matrix.mul_assoc,out.cross_zero,Matrix.mul_zero]
  have hg : (Matrix.fromCols out.basis out.complement)ᵀ*D*
      (Matrix.fromCols out.basis out.complement) = Matrix.fromBlocks out.compressed 0 0 (0 : Core out.nullity) := by
    rw [Matrix.mul_assoc,Matrix.mul_fromCols,Matrix.transpose_fromCols,Matrix.fromRows_mul_fromCols]
    have hND : out.complementᵀ*D*out.basis = 0 := by
      calc
        _ = out.complementᵀ*(out.basis*out.compressed*out.basisᵀ)*out.basis :=
          congrArg (fun A => out.complementᵀ*A*out.basis) out.decomposition
        _ = 0 := by simp only [← Matrix.mul_assoc,hc,Matrix.zero_mul]
    simp only [hDN,Matrix.mul_zero,← Matrix.mul_assoc,← out.compressed_eq,hND]
  change (Matrix.fromCols out.basis out.complement)ᵀ.submatrix out.indexEquiv.symm (Equiv.refl _)*
    D.submatrix (Equiv.refl _) (Equiv.refl _)*
    (Matrix.fromCols out.basis out.complement).submatrix (Equiv.refl _) out.indexEquiv.symm = _
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,hg]

end InertiaSupport

def CongruenceDiagonalData.blockZero {r z : ℕ} {H : Core r} (out : CongruenceDiagonalData H) :
    CongruenceDiagonalData (Matrix.fromBlocks H (0 : Matrix (Fin r) (Fin z) ℝ) 0 (0 : Core z)) where
  basis := Matrix.fromBlocks out.basis (0 : Matrix (Fin r) (Fin z) ℝ) 0 (1 : Core z)
  inverse := Matrix.fromBlocks out.inverse (0 : Matrix (Fin r) (Fin z) ℝ) 0 (1 : Core z)
  diagonal := Sum.elim out.diagonal (fun _ => 0)
  left_inverse := by simp [Matrix.fromBlocks_multiply,out.left_inverse]
  right_inverse := by simp [Matrix.fromBlocks_multiply,out.right_inverse]
  congruence := by
    rw [Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero,Matrix.transpose_one,Matrix.zero_mul,Matrix.mul_zero,
      add_zero,zero_add,out.congruence]
    simpa using Matrix.fromBlocks_diagonal out.diagonal (fun _ : Fin z => (0:ℝ))

def InertiaSupport.lift {D : Core n} (support : InertiaSupport D)
    (out : FiniteCongruenceDiagonal support.compressed) : FiniteCongruenceDiagonal D :=
  let block := (out.toData.blockZero (z := support.nullity)).reindex support.indexEquiv.symm
  let adapted := block.cast support.frame_congruence.symm
  (CongruenceDiagonalData.conjugate D support.frame support.frameᵀ
    support.frame_orthogonal support.frame_coorthogonal adapted).toFinite

end
end HierarchicalAbsoluteSpectral
