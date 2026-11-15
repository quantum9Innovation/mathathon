import HierarchicalAbsoluteSpectral.GaussianPolynomial
import HierarchicalAbsoluteSpectral.StrongFilterDiagonal
import HierarchicalAbsoluteSpectral.CoarseAlgebraLeading
import Mathlib.LinearAlgebra.Matrix.MvPolynomial

/-! Gaussian congruence makes every leading principal minor of a fixed
nonsingular symmetric matrix nonzero almost surely. The witness proving
each determinant polynomial is nonzero is the actual spectral basis. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

def gaussianSquareMatrix (n : ℕ) (g : Fin (n*n) → ℝ) : Core n :=
  fun i j => g (finProdFinEquiv (i,j))

def congruenceMinorPolynomial {n : ℕ} (H : Core n) (r : ℕ) (hr : r ≤ n) :
    MvPolynomial (Fin n × Fin n) ℝ :=
  (((Matrix.mvPolynomialX (Fin n) (Fin n) ℝ)ᵀ*
      H.map MvPolynomial.C*Matrix.mvPolynomialX (Fin n) (Fin n) ℝ).submatrix
        (Fin.castLEEmb hr) (Fin.castLEEmb hr)).det

theorem congruenceMinorPolynomial_eval {n : ℕ}
    (H S : Core n) (r : ℕ) (hr : r ≤ n) :
    MvPolynomial.eval (fun p : Fin n × Fin n => S p.1 p.2)
        (congruenceMinorPolynomial H r hr) = (leadingPrincipal (Sᵀ*H*S) r hr).det := by
  let ev := MvPolynomial.eval (fun p : Fin n × Fin n => S p.1 p.2)
  have hX : (Matrix.mvPolynomialX (Fin n) (Fin n) ℝ).map ev = S :=
    Matrix.mvPolynomialX_mapMatrix_eval S
  have hH : (H.map MvPolynomial.C).map ev = H := by
    ext i j
    simp [ev]
  unfold congruenceMinorPolynomial
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
    Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hX, hH]
  rfl

theorem strongSpectralQ_congruence {n : ℕ}
    (H : Core n) (hH : H.toEuclideanLin.IsSymmetric) :
    (strongSpectralQ H hH)ᵀ*H*strongSpectralQ H hH = Matrix.diagonal (strongEigenvalues H hH) := by
  let Q := strongSpectralQ H hH
  have hQ : Qᵀ*Q = 1 := strongSpectralQ_gram H hH
  calc
    _ = Qᵀ*(Q*Matrix.diagonal (strongEigenvalues H hH)*Qᵀ)*Q :=
      congrArg (fun A => Qᵀ*A*Q) (strongSpectralQ_diagonalizes H hH)
    _ = _ := by
      simp only [← Matrix.mul_assoc, hQ, Matrix.one_mul]
      rw [Matrix.mul_assoc, hQ, Matrix.mul_one]

theorem nonsingular_spectral_eigenvalues_ne_zero {n : ℕ}
    (H : Core n) (hH : H.toEuclideanLin.IsSymmetric) (hdet : IsUnit H.det) :
    ∀ i, strongEigenvalues H hH i ≠ 0 := by
  let Q := strongSpectralQ H hH
  have hgram : Qᵀ*Q = 1 := strongSpectralQ_gram H hH
  have hqd := congrArg Matrix.det hgram
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hqd
  have hQnz : Q.det ≠ 0 := by intro hz; rw [hz] at hqd; norm_num at hqd
  have hp : (∏ i, strongEigenvalues H hH i) ≠ 0 := by
    rw [← Matrix.det_diagonal, ← strongSpectralQ_congruence H hH,
      Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hQnz (isUnit_iff_ne_zero.mp hdet)) hQnz
  exact fun i => Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)

theorem spectral_congruence_leading_regular {n : ℕ}
    (H : Core n) (hH : H.toEuclideanLin.IsSymmetric) (hdet : IsUnit H.det) :
    LeadingPrincipalRegular ((strongSpectralQ H hH)ᵀ*H*strongSpectralQ H hH) := by
  intro r hr
  rw [strongSpectralQ_congruence, leadingPrincipal, Matrix.submatrix_diagonal_embedding,
    Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => nonsingular_spectral_eigenvalues_ne_zero H hH hdet _)

theorem congruenceMinorPolynomial_ne_zero {n : ℕ}
    (H : Core n) (hH : H.toEuclideanLin.IsSymmetric) (hdet : IsUnit H.det)
    (r : ℕ) (hr : r ≤ n) : congruenceMinorPolynomial H r hr ≠ 0 := by
  intro hz
  have heq := congruenceMinorPolynomial_eval H (strongSpectralQ H hH) r hr
  rw [hz, map_zero] at heq
  exact (isUnit_iff_ne_zero.mp (spectral_congruence_leading_regular H hH hdet r hr)) heq.symm

theorem gaussian_congruence_leading_regular_ae {n : ℕ}
    (H : Core n) (hH : H.toEuclideanLin.IsSymmetric) (hdet : IsUnit H.det) :
    ∀ᵐ g ∂gaussianVector (n*n),
      LeadingPrincipalRegular ((gaussianSquareMatrix n g)ᵀ*H*gaussianSquareMatrix n g) := by
  have hall : ∀ᵐ g ∂gaussianVector (n*n), ∀ (r : ℕ) (hr : r ≤ n),
      MvPolynomial.eval (fun i : Fin n × Fin n => g (finProdFinEquiv i))
        (congruenceMinorPolynomial H r hr) ≠ 0 := by
    apply ae_all_iff.mpr
    intro r
    apply ae_all_iff.mpr
    intro hr
    exact gaussian_polynomial_reindex_ne_zero_ae (n*n) finProdFinEquiv _
      (congruenceMinorPolynomial_ne_zero H hH hdet r hr)
  filter_upwards [hall] with g hg
  intro r hr
  apply isUnit_iff_ne_zero.mpr
  have heq := congruenceMinorPolynomial_eval H (gaussianSquareMatrix n g) r hr
  rw [← heq]
  exact hg r hr

theorem gaussian_congruence_leading_regular_and_invertible_ae {n : ℕ}
    (H : Core n) (hH : H.toEuclideanLin.IsSymmetric) (hdet : IsUnit H.det) :
    ∀ᵐ g ∂gaussianVector (n*n),
      LeadingPrincipalRegular ((gaussianSquareMatrix n g)ᵀ*H*gaussianSquareMatrix n g) ∧
        IsUnit (gaussianSquareMatrix n g).det := by
  filter_upwards [gaussian_congruence_leading_regular_ae H hH hdet] with g hg
  refine ⟨hg,?_⟩
  have hd := isUnit_iff_ne_zero.mp hg.isUnit_det
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [hz] at hd
  simp at hd

end
end HierarchicalAbsoluteSpectral
