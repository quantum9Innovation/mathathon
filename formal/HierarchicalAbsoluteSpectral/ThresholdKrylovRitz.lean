import HierarchicalAbsoluteSpectral.ThresholdKrylovGuarantee
import HierarchicalAbsoluteSpectral.MinMaxSquare

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp Polynomial
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {k r w : ℕ}

theorem square_isHermitian (T : Core k) (hT : T.IsHermitian) : (T*T).IsHermitian := by
  have ht : Tᵀ = T := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hT.eq
  simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, ht]

def thresholdRitzValue (T : Core k) (hT : T.IsHermitian)
    (U : Matrix (Fin k) (Fin w) ℝ) (j : Fin k) : ℝ :=
  if hjw : j.val < w then
    orderedEigenvalue (Uᵀ*(T*T)*U) (compression_isHermitian _ (square_isHermitian T hT) U) ⟨j.val,hjw⟩
  else 0

theorem thresholdRitzValue_always_safe (T : Core k) (hT : T.PosSemidef)
    (U : Matrix (Fin k) (Fin w) ℝ) (hU : Uᵀ*U = 1) (j : Fin k) :
    thresholdRitzValue T hT.isHermitian U j ≤ (orderedEigenvalue T hT.isHermitian j)^2 := by
  unfold thresholdRitzValue
  split_ifs with hjw
  · exact (orderedEigenvalue_compression_le (T*T) (square_isHermitian T hT.isHermitian)
      U hU j.val hjw j.isLt).trans (orderedEigenvalue_square_upper T hT j)
  · exact sq_nonneg _

theorem spectral_basis_square_compression (T : Core k) (hT : T.toEuclideanLin.IsSymmetric) :
    (strongSpectralQ T hT)ᵀ*(T*T)*strongSpectralQ T hT =
      Matrix.diagonal (fun i => (strongEigenvalues T hT i)^2) := by
  let Q := strongSpectralQ T hT
  let d := strongEigenvalues T hT
  have hTQ := strongSpectralQ_intertwines T hT
  have hQ := strongSpectralQ_gram T hT
  calc
    Qᵀ*(T*T)*Q = Qᵀ*(T*(T*Q)) := by simp only [Matrix.mul_assoc]
    _ = Qᵀ*(T*(Q*Matrix.diagonal d)) := by rw [hTQ]
    _ = Qᵀ*((T*Q)*Matrix.diagonal d) := by rw [Matrix.mul_assoc T Q]
    _ = (Qᵀ*Q)*(Matrix.diagonal d*Matrix.diagonal d) := by rw [hTQ]; simp only [Q, d, Matrix.mul_assoc]
    _ = _ := by
      rw [hQ, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      ring

theorem polynomial_graph_in_krylov (T : Core k) (hT : T.toEuclideanLin.IsSymmetric)
    (Ω : Matrix (Fin k) (Fin r) ℝ) (j : Fin k) (p : ℝ[X]) (q : ℕ) (hq : p.natDegree ≤ q)
    (H : Matrix (Fin r) (Fin (j.val+1)) ℝ) :
    strongSpectralQ T hT*diagonalFilteredGraph (strongEigenvalues T hT) p (krylovHeadEmbedding j)
        ((strongSpectralQ T hT)ᵀ*Ω) H =
      blockKrylov T Ω q*blockKrylovCoefficients p q
        (H*Matrix.diagonal (fun s => (p.eval (strongEigenvalues T hT (krylovHeadEmbedding j s)))⁻¹)) := by
  rw [blockKrylov_polynomial_identity T Ω p q hq]
  rw [aeval_orthogonal_diagonal T (strongSpectralQ T hT) (strongEigenvalues T hT)
    (strongSpectralQ_coGram T hT) (strongSpectralQ_intertwines T hT) p]
  simp only [diagonalFilteredGraph, Matrix.mul_assoc]

/-- The actual block-Krylov compression obtains the target-index additive
Ritz guarantee on the explicit Gaussian head-capture event. Its span is the
whole computed Krylov matrix, not a supplied successful filter certificate. -/
theorem thresholdRitzValue_of_capture
    (T : Core k) (hT : T.PosSemidef) (j : Fin k)
    (htarget : 0 < orderedEigenvalue T hT.isHermitian j)
    (ε R : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1) (hR : 1 ≤ R) (q : ℕ)
    (hstop : 10*R/ε ≤ strongFilterDenominator (ε/100) q)
    (Ω : Matrix (Fin k) (Fin r) ℝ)
    (H : Matrix (Fin r) (Fin (j.val+1)) ℝ)
    (U : Matrix (Fin k) (Fin w) ℝ) (W : Matrix (Fin (q+1) × Fin r) (Fin w) ℝ)
    (hU : Uᵀ*U = 1) (hspan : blockKrylov T Ω q = U*Wᵀ)
    (hhead : (((strongSpectralQ T (Matrix.isSymmetric_toEuclideanLin_iff.mpr hT.isHermitian))ᵀ*Ω).submatrix
      (krylovHeadEmbedding j) id)*H = 1)
    (hΩ : ‖((strongSpectralQ T (Matrix.isSymmetric_toEuclideanLin_iff.mpr hT.isHermitian))ᵀ*Ω)*H‖ ≤ R) :
    (1-ε)*(orderedEigenvalue T hT.isHermitian j)^2 ≤ thresholdRitzValue T hT.isHermitian U j := by
  let hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hT.isHermitian
  let Q := strongSpectralQ T hs
  let d := strongEigenvalues T hs
  let e := krylovHeadEmbedding j
  let p := ritzFilterPolynomial ε (d j) q
  let Yd := diagonalFilteredGraph d p e (Qᵀ*Ω) H
  let Y := Q*Yd
  let Coeff := blockKrylovCoefficients p q
    (H*Matrix.diagonal (fun s => (p.eval (d (e s)))⁻¹))
  let X := Wᵀ*Coeff
  have hYspan : Y = U*X := by
    rw [show Y = blockKrylov T Ω q*Coeff from
      polynomial_graph_in_krylov T hs Ω j p q (ritzFilterPolynomial_natDegree_le _ _ _) H]
    rw [hspan]
    simp only [X, Matrix.mul_assoc]
  have hd : Antitone d := hs.eigenvalues_antitone finrank_euclideanSpace_fin
  have hd0 : ∀ i, 0 ≤ d i := fun i => orderedEigenvalue_nonneg T hT i
  have hp : ∀ s, p.eval (d (e s)) ≠ 0 := by
    intro s
    have hh := ritzFilterPolynomial_head ε (d j) q hε htarget (d (e s))
      (hd (show e s ≤ j from Nat.le_of_lt_succ s.isLt))
    linarith
  have hYd : Function.Injective Yd.toEuclideanLin :=
    diagonalFilteredGraph_injective d p e (Qᵀ*Ω) H hhead hp
  have hY : Function.Injective Y.toEuclideanLin := by
    rw [show Y = Q*Yd from rfl, Matrix.toLpLin_mul]
    exact (orthonormal_toEuclideanLin_injective Q (strongSpectralQ_gram T hs)).comp hYd
  have hX : Function.Injective X.toEuclideanLin := by
    intro z z' hz
    apply hY
    rw [hYspan, Matrix.toLpLin_mul 2 2 2]
    simp only [LinearMap.comp_apply, hz]
  have hdim : j.val+1 ≤ w := by
    simpa only [finrank_euclideanSpace_fin] using LinearMap.finrank_le_finrank_of_injective hX
  have hjw : j.val < w := by omega
  unfold thresholdRitzValue
  rw [dif_pos hjw]
  apply orderedEigenvalue_compression_lower (T*T) (square_isHermitian T hT.isHermitian)
    U hU Y X hY hYspan ((1-ε)*(orderedEigenvalue T hT.isHermitian j)^2) _ hjw
  intro z
  have hg := diagonal_krylov_graph_rayleigh d hd hd0 j htarget ε R hε hε' hR q hstop
    (Qᵀ*Ω) H hhead hΩ z
  simp only [Y]
  rw [Matrix.toLpLin_mul 2 2 2]
  simp only [LinearMap.comp_apply]
  rw [orthonormal_toEuclideanLin_inner Q (strongSpectralQ_gram T hs),
    ← quadratic_eq_inner, ← quadratic_compression,
    spectral_basis_square_compression T hs, quadratic_eq_inner]
  exact hg

end
end HierarchicalAbsoluteSpectral
