import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixSupport
import HierarchicalAbsoluteSpectral.MassSpectrumSupport

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix WithLp

theorem exactGram_orderedEigenvalue_pos {k : ℕ} (H : Core k) (hH : H.PosDef) (j : Fin k) :
    0 < orderedEigenvalue H hH.isHermitian j := by
  let symm := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH.isHermitian
  let v := symm.eigenvectorBasis finrank_euclideanSpace_fin j
  have hv : v ≠ 0 := (symm.eigenvectorBasis finrank_euclideanSpace_fin).orthonormal.ne_zero j
  have hnonzero : orderedEigenvalue H hH.isHermitian j ≠ 0 := by
    intro hz
    have hz' : symm.eigenvalues finrank_euclideanSpace_fin j = 0 := hz
    have heq := symm.apply_eigenvectorBasis finrank_euclideanSpace_fin j
    rw [hz'] at heq
    simp only [RCLike.ofReal_real_eq_id, id_eq, zero_smul] at heq
    apply hv
    apply toEuclideanLin_injective_of_det H ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit)
    simpa only [map_zero] using heq
  exact lt_of_le_of_ne (orderedEigenvalue_nonneg H hH.posSemidef j) hnonzero.symm

namespace ExactGramAppendixSupport

variable {n m p : ℕ} {A : Matrix (Fin n) (Fin m) ℝ} {B : Matrix (Fin m) (Fin p) ℝ}

theorem dimension_le_rows (out : ExactGramAppendixSupport A B) : out.dimension ≤ n := by
  have hr : (A*out.lift).rank = out.dimension := by
    rw [← Matrix.rank_transpose_mul_self (A*out.lift), out.orthogonal, Matrix.rank_one,
      Fintype.card_fin]
  rw [← hr]
  simpa only [Fintype.card_fin] using Matrix.rank_le_card_height (A*out.lift)

theorem dimension_le_cols (out : ExactGramAppendixSupport A B) : out.dimension ≤ p := by
  have hr : out.core.rank = out.dimension := by
    simpa only [Fintype.card_fin] using Matrix.rank_of_isUnit out.core out.positive.isUnit
  rw [← hr, out.gram]
  apply (Matrix.rank_mul_le_left _ _).trans
  simpa only [Fintype.card_fin] using Matrix.rank_le_card_width (out.right*B)

theorem eigenvalue_pos (out : ExactGramAppendixSupport A B) (j : Fin out.dimension) :
    0 < orderedEigenvalue out.core out.positive.isHermitian j :=
  exactGram_orderedEigenvalue_pos _ out.positive j

theorem eigenvalue_eq_sq_tail (out : ExactGramAppendixSupport A B) (j : Fin out.dimension) :
    orderedEigenvalue out.core out.positive.isHermitian j = tailSingularValue (A*B) j.val^2 := by
  have hZ : ((A*out.lift)ᵀ*(A*out.lift)).PosDef := by
    rw [out.orthogonal]
    exact Matrix.PosDef.one
  have h := support_mass_eigenvalue_eq_sq_tail (A*out.lift) (out.right*B) hZ j
    (j.isLt.trans_le out.dimension_le_cols)
  rw [out.orthogonal, inv_one] at h
  have hmass : massEigenvalue ((out.right*B)*(out.right*B)ᵀ) (1 : Core out.dimension)
      (by simpa only [out.gram] using out.positive.isHermitian) j =
      orderedEigenvalue out.core out.positive.isHermitian j := by
    simp only [massEigenvalue, massInverseFactor, CFC.sqrt_one, inv_one,
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, ← out.gram]
  rw [hmass, ← out.product] at h
  exact h

end ExactGramAppendixSupport

end
end HierarchicalAbsoluteSpectral
