import HierarchicalAbsoluteSpectral.StrongFilterMasks
import HierarchicalAbsoluteSpectral.MinMaxEigen
import HierarchicalAbsoluteSpectral.MassSpectrum

/-! A Gaussian range initializer with a polynomial bracket ratio. This
constructive initializer replaces characteristic-coefficient extraction in
the main algorithm, preserving its error, rank and arithmetic cost bounds. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix WithLp Polynomial
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace InnerProductSpace

def matrixFrobeniusValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ j, ∑ i, (A i j)^2)

theorem matrixFrobeniusValue_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ matrixFrobeniusValue A := Real.sqrt_nonneg _

theorem spectral_norm_le_matrixFrobeniusValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ ≤ matrixFrobeniusValue A := by
  apply columnsMatrix_norm_le_energy (fun j i => A i j) _ (matrixFrobeniusValue_nonneg A)
  exact (Real.sq_sqrt (by unfold gaussianEnergy; positivity)).ge

theorem matrix_energy_le_cols_mul_norm_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (∑ j, ∑ i, (A i j)^2) ≤ n*‖A‖^2 := by
  have hcol (j : Fin n) : (∑ i, (A i j)^2) ≤ ‖A‖^2 := by
    have heq : A *ᵥ (Pi.single j 1) = (fun i => A i j) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hm := Matrix.l2_opNorm_mulVec A (toLp 2 (Pi.single j 1))
    change ‖toLp 2 (A *ᵥ (Pi.single j 1))‖ ≤ ‖A‖*‖(toLp 2 (Pi.single j 1) : EuclideanSpace ℝ (Fin n))‖ at hm
    rw [heq] at hm
    have hsingle : ‖(toLp 2 (Pi.single j (1 : ℝ)) : EuclideanSpace ℝ (Fin n))‖ = 1 := by simp
    rw [hsingle, mul_one] at hm
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hm
    simpa only [EuclideanSpace.real_norm_sq_eq] using hs
  calc
    _ ≤ ∑ _j : Fin n, ‖A‖^2 := Finset.sum_le_sum (fun j _ => hcol j)
    _ = _ := by simp

theorem matrixFrobeniusValue_le_cols_sqrt_mul_norm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : matrixFrobeniusValue A ≤ Real.sqrt n*‖A‖ := by
  apply (sq_le_sq₀ (matrixFrobeniusValue_nonneg A) (by positivity)).mp
  rw [matrixFrobeniusValue, Real.sq_sqrt (by positivity), mul_pow,
    Real.sq_sqrt (by positivity)]
  exact matrix_energy_le_cols_mul_norm_sq A

theorem matrixFrobeniusValue_eq_zero_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    matrixFrobeniusValue A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hn := spectral_norm_le_matrixFrobeniusValue A
    rw [h] at hn
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg A))
  · rintro rfl
    simp [matrixFrobeniusValue]

theorem gaussian_range_residual_upper {k r w : ℕ}
    (T Q : Core k) (d : Fin k → ℝ) (hr : r ≤ k)
    (hQ : Qᵀ*Q = 1) (hQQ : Q*Qᵀ = 1) (hdiag : T = Q*Matrix.diagonal d*Qᵀ)
    (Ξ : Matrix (Fin k) (Fin r) ℝ) (H : Core r) (ell R : ℝ)
    (hell : 0 ≤ ell) (hR : 0 ≤ R)
    (htail : ∀ i, r ≤ i.val → |d i| ≤ ell)
    (hhead : ((Q*columnEmbedding (leadingEmbedding hr))ᵀ*Ξ)*H = 1)
    (hgraph : ‖(Qᵀ*Ξ)*H‖ ≤ R)
    (U : Matrix (Fin k) (Fin w) ℝ) (W : Matrix (Fin w) (Fin r) ℝ)
    (hU : Uᵀ*U = 1) (hspan : T*Ξ = U*W) :
    ‖((1 : Core k)-U*Uᵀ)*T‖ ≤ (1+R)*ell := by
  let E := columnEmbedding (leadingEmbedding hr)
  let J := Q*E
  let Ω := Qᵀ*Ξ
  let Ωh := Eᵀ*Ω
  let Dh : Core r := Matrix.diagonal (fun j => d (leadingEmbedding hr j))
  let Dt : Core k := Matrix.diagonal (trailingMask r d)
  let P := J*(Dh*Jᵀ)
  let Y := T*Ξ
  let B : Core k := 1-U*Uᵀ
  have hJ : Jᵀ*J = 1 := by
    calc
      _ = Eᵀ*(Qᵀ*Q)*E := by simp only [J, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hQ, Matrix.mul_one]; exact columnEmbedding_gram _
  have hDtn : ‖Dt‖ ≤ ell := by
    dsimp only [Dt]
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hell).mpr
    intro i
    by_cases hi : i.val < r
    · simpa [trailingMask, hi] using hell
    · simpa [trailingMask, hi, Real.norm_eq_abs] using htail i (Nat.le_of_not_gt hi)
  have hY : Y = J*(Dh*Ωh)+Q*(Dt*Ω) := by
    dsimp only [Y]
    rw [hdiag]
    simpa only [J, Dh, Dt, Ωh, Ω, E, Matrix.mul_assoc] using spectral_filter_split hr Q d Ω
  have hH : Ωh*H = 1 := by
    simpa only [J, E, Ωh, Ω, Matrix.transpose_mul, Matrix.mul_assoc] using hhead
  have happrox : ‖P-Y*(H*Jᵀ)‖ ≤ ell*R := by
    have hb := filter_graph_norm_bound J Q Dh Dt Ωh Ω H Jᵀ ell R hell hR hH
      (orthonormal_columns_norm_le_one Q hQ) hDtn hgraph
      (by rw [spectral_norm_transpose]; exact orthonormal_columns_norm_le_one J hJ)
    simpa only [P, ← hY] using hb
  have hdecomp : T = P+Q*Dt*Qᵀ := by
    have hs := spectral_filter_split hr Q d Qᵀ
    simpa only [hdiag, P, J, Dh, Dt, E, Matrix.transpose_mul, Matrix.mul_assoc] using hs
  have htailn : ‖Q*Dt*Qᵀ‖ ≤ ell := by
    calc
      _ ≤ (‖Q‖*‖Dt‖)*‖Qᵀ‖ := (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ (1*ell)*1 := by
        rw [spectral_norm_transpose]
        gcongr
        all_goals exact orthonormal_columns_norm_le_one Q hQ
      _ = ell := by ring
  have hdiff : ‖T-Y*(H*Jᵀ)‖ ≤ (1+R)*ell := by
    have heq : T-Y*(H*Jᵀ) = (P-Y*(H*Jᵀ))+Q*Dt*Qᵀ := by rw [hdecomp]; module
    rw [heq]
    exact (norm_add_le _ _).trans (by nlinarith)
  have hBY : B*Y = 0 := by
    rw [show Y = U*W from hspan]
    simp [B, Matrix.sub_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hU]
  have heq : B*T = B*(T-Y*(H*Jᵀ)) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc B Y, hBY, Matrix.zero_mul, sub_zero]
  rw [heq]
  exact (norm_mul_le _ _).trans
    ((mul_le_mul (orthogonal_complement_norm_le_one U hU) hdiff
      (norm_nonneg _) zero_le_one).trans (by simp))

/-- Every width-at-most-r projection has residual at least the actual
zero-indexed r-th eigenvalue. The proof explicitly intersects the leading
r+1 eigenspace with the orthogonal complement of the supplied basis. -/
theorem projection_residual_ge_eigenvalue {k r w : ℕ}
    (T : Core k) (hT : T.toEuclideanLin.IsSymmetric) (hr : r < k)
    (U : Matrix (Fin k) (Fin w) ℝ) (hw : w ≤ r) :
    strongEigenvalues T hT ⟨r,hr⟩ ≤ ‖((1 : Core k)-U*Uᵀ)*T‖ := by
  let j : Fin k := ⟨r,hr⟩
  let V := spectralHeadEmbedding T.toEuclideanLin hT finrank_euclideanSpace_fin j
  let f := Uᵀ.toEuclideanLin.comp V
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin w)) <
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (r+1))) := by simp; omega
  obtain ⟨z,hz,hzne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
  let y := V z
  have hyne : y ≠ 0 := by
    intro heq
    apply hzne
    apply spectralHeadEmbedding_injective T.toEuclideanLin hT finrank_euclideanSpace_fin j
    simpa only [y, map_zero] using heq
  have hUy : Uᵀ *ᵥ ofLp y = 0 := by
    have hh : Uᵀ.toEuclideanLin y = 0 := hz
    simpa only [Matrix.ofLp_toEuclideanLin_apply, ofLp_zero] using congrArg ofLp hh
  let E : Core k := 1-U*Uᵀ
  have hEy : E *ᵥ ofLp y = ofLp y := by
    simp [E, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hUy]
  have hTT : Tᵀ = T := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.isSymmetric_toEuclideanLin_iff.mp hT).eq
  have hEE : Eᵀ = E := by simp [E, Matrix.transpose_mul]
  have hnorm : ‖T*E‖ = ‖E*T‖ := by
    rw [← spectral_norm_transpose (E*T), Matrix.transpose_mul, hTT, hEE]
  have hm := Matrix.l2_opNorm_mulVec (T*E) y
  change ‖toLp 2 ((T*E) *ᵥ ofLp y)‖ ≤ ‖T*E‖*‖y‖ at hm
  rw [← Matrix.mulVec_mulVec, hEy, hnorm] at hm
  have hhead : strongEigenvalues T hT j*⟪y,y⟫_ℝ ≤ ⟪y,T.toEuclideanLin y⟫_ℝ := by
    exact eigenbasis_head_bound T.toEuclideanLin hT finrank_euclideanSpace_fin j y
      (fun i hi => spectralHeadEmbedding_tail_zero T.toEuclideanLin hT finrank_euclideanSpace_fin j z i hi)
  have hpos : 0 < ⟪y,y⟫_ℝ := real_inner_self_pos.mpr hyne
  have hc : strongEigenvalues T hT j*⟪y,y⟫_ℝ ≤ ‖E*T‖*⟪y,y⟫_ℝ := by
    calc
      _ ≤ ⟪y,T.toEuclideanLin y⟫_ℝ := hhead
      _ ≤ ‖y‖*‖T.toEuclideanLin y‖ := real_inner_le_norm _ _
      _ ≤ ‖y‖*(‖E*T‖*‖y‖) := mul_le_mul_of_nonneg_left hm (norm_nonneg _)
      _ = _ := by rw [real_inner_self_eq_norm_sq]; ring
  exact (mul_le_mul_iff_left₀ hpos).mp hc

end
end HierarchicalAbsoluteSpectral
