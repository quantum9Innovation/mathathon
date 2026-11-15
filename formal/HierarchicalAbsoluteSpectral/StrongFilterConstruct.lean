import HierarchicalAbsoluteSpectral.StrongFilterMasks

/-! Construct the strong-projector approximation from the actual Chebyshev
polynomial and a Gaussian head right inverse, then prove the span residual. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open scoped MatrixOrder Matrix.Norms.L2Operator

def strongFilterIndicator (α x : ℝ) : ℝ := if 1+2*α ≤ x then 1 else 0

def strongFilterInverseWeight (α : ℝ) (v : ℕ) (x : ℝ) : ℝ :=
  if 1+2*α ≤ x then ((strongFilterPolynomial α v).eval x)⁻¹ else 0

theorem strongFilterInverseWeight_bound (α : ℝ) (hα : 0 < α) (v : ℕ) (x : ℝ) :
    |strongFilterInverseWeight α v x| ≤ 1 := by
  unfold strongFilterInverseWeight
  split_ifs with hx
  · have hf := strongFilter_strong_ge_one α hα v x hx
    have hf0 : 0 < (strongFilterPolynomial α v).eval x := by linarith
    rw [abs_of_pos (inv_pos.mpr hf0)]
    exact (inv_le_one₀ hf0).mpr hf
  · norm_num

theorem strongFilterInverseWeight_identity (α : ℝ) (hα : 0 < α) (v : ℕ) (x : ℝ) :
    (strongFilterPolynomial α v).eval x*strongFilterInverseWeight α v x = strongFilterIndicator α x := by
  unfold strongFilterInverseWeight strongFilterIndicator
  split_ifs with hx
  · exact mul_inv_cancel₀ (by have := strongFilter_strong_ge_one α hα v x hx; linarith)
  · simp

theorem chebyshev_strong_filter_from_head_right_inverse {k r w : ℕ}
    (T Q : Core k) (d : Fin k → ℝ) (hr : r ≤ k)
    (hQ : Qᵀ*Q = 1) (hQQ : Q*Qᵀ = 1) (hdiag : T = Q*Matrix.diagonal d*Qᵀ)
    (Ωphys : Matrix (Fin k) (Fin r) ℝ) (H : Matrix (Fin r) (Fin r) ℝ)
    (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α) (v : ℕ)
    (hdlo : ∀ i, 0 ≤ d i) (hdhi : ∀ i, d i ≤ 2)
    (hdtail : ∀ i, r ≤ i.val → d i ≤ 1+α)
    (hden : 2*R/α ≤ strongFilterDenominator α v)
    (hhead : ((Q*columnEmbedding (leadingEmbedding hr))ᵀ*Ωphys)*H = 1)
    (hgraph : ‖(Qᵀ*Ωphys)*H‖ ≤ R)
    (U : Matrix (Fin k) (Fin w) ℝ) (W : Matrix (Fin w) (Fin r) ℝ)
    (hU : Uᵀ*U = 1) (hspan : aeval T (strongFilterPolynomial α v)*Ωphys = U*W) :
    ‖((1 : Core k)-U*Uᵀ)*T‖ ≤ 1+3*α := by
  let E := columnEmbedding (leadingEmbedding hr)
  let J := Q*E
  let f : Fin k → ℝ := fun i => (strongFilterPolynomial α v).eval (d i)
  let Dh : Core r := Matrix.diagonal (fun j => f (leadingEmbedding hr j))
  let Dt : Core k := Matrix.diagonal (trailingMask r f)
  let F : Matrix (Fin r) (Fin k) ℝ :=
    Matrix.diagonal (fun j => strongFilterInverseWeight α v (d (leadingEmbedding hr j)))*Jᵀ
  let p : Fin k → ℝ := leadingMask r (fun i => strongFilterIndicator α (d i))
  let P : Core k := Q*Matrix.diagonal p*Qᵀ
  let Ω := Qᵀ*Ωphys
  let Ωh := Eᵀ*Ω
  let Y := aeval T (strongFilterPolynomial α v)*Ωphys
  have hJ : Jᵀ*J = 1 := by
    calc
      _ = Eᵀ*(Qᵀ*Q)*E := by simp only [J, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hQ, Matrix.mul_one]; exact columnEmbedding_gram _
  have hFn : ‖F‖ ≤ 1 := by
    have hcoeff : ‖Matrix.diagonal (fun j => strongFilterInverseWeight α v (d (leadingEmbedding hr j)))‖ ≤ 1 := by
      rw [Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun j => by
        simpa [Real.norm_eq_abs] using strongFilterInverseWeight_bound α hα v (d (leadingEmbedding hr j)))
    calc
      _ ≤ ‖Matrix.diagonal (fun j => strongFilterInverseWeight α v (d (leadingEmbedding hr j)))‖*‖Jᵀ‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ 1*1 := by
        rw [spectral_norm_transpose]
        exact mul_le_mul hcoeff (orthonormal_columns_norm_le_one J hJ) (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  have hPF : J*(Dh*F) = P := by
    have hdiagprod : Dh*Matrix.diagonal
        (fun j => strongFilterInverseWeight α v (d (leadingEmbedding hr j))) =
        Matrix.diagonal (fun j => strongFilterIndicator α (d (leadingEmbedding hr j))) := by
      dsimp only [Dh]
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext j
      exact strongFilterInverseWeight_identity α hα v _
    calc
      _ = J*(Dh*Matrix.diagonal (fun j => strongFilterInverseWeight α v (d (leadingEmbedding hr j))))*Jᵀ := by
        simp only [F, Matrix.mul_assoc]
      _ = J*Matrix.diagonal (fun j => strongFilterIndicator α (d (leadingEmbedding hr j)))*Jᵀ := by rw [hdiagprod]
      _ = Q*(E*Matrix.diagonal (fun j => strongFilterIndicator α (d (leadingEmbedding hr j)))*Eᵀ)*Qᵀ := by
        simp only [J, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = P := by rw [show E*Matrix.diagonal (fun j => strongFilterIndicator α (d (leadingEmbedding hr j)))*Eᵀ =
          Matrix.diagonal p from leading_diagonal_lift hr (fun i => strongFilterIndicator α (d i))]
  have hTQ : T*Q = Q*Matrix.diagonal d := by
    rw [hdiag]
    simp only [Matrix.mul_assoc, hQ, Matrix.mul_one]
  have hY : Y = J*(Dh*Ωh)+Q*(Dt*Ω) := by
    dsimp only [Y]
    rw [aeval_orthogonal_diagonal T Q d hQQ hTQ]
    have hsplit := spectral_filter_split hr Q f Ω
    simpa only [J, Dh, Dt, Ωh, Ω, E, Matrix.mul_assoc] using hsplit
  have hH : Ωh*H = 1 := by
    simpa only [J, Ωh, Ω, E, Matrix.transpose_mul, Matrix.mul_assoc] using hhead
  have hden0 : 0 < strongFilterDenominator α v := by
    have := strongFilterDenominator_ge_one α hα v
    linarith
  have hDtn : ‖Dt‖ ≤ 1/strongFilterDenominator α v := by
    dsimp only [Dt]
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    by_cases hi : i.val < r
    · simp [trailingMask, hi]
      positivity
    · simpa only [trailingMask, if_neg hi, Real.norm_eq_abs, f] using
        strongFilter_tail_bound α hα v (d i) (hdlo i) (hdtail i (Nat.le_of_not_gt hi))
  have happrox : ‖P-Y*(H*F)‖ ≤ α/2 := by
    have hb := filter_graph_norm_bound J Q Dh Dt Ωh Ω H F
      (1/strongFilterDenominator α v) R (by positivity) hR hH
      (orthonormal_columns_norm_le_one Q hQ) hDtn hgraph hFn
    rw [hPF, ← hY] at hb
    apply hb.trans
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hm := (div_le_iff₀ hα).mp hden
    have he : (1/strongFilterDenominator α v*R)*2 = (2*R)/strongFilterDenominator α v := by ring
    rw [he]
    exact (div_le_iff₀ hden0).mpr (by nlinarith)
  have hcomm : P*T = T*P := by
    rw [hdiag]
    dsimp only [P]
    rw [orthogonal_diagonal_mul Q hQ, orthogonal_diagonal_mul Q hQ]
    rw [show (fun i => p i*d i) = (fun i => d i*p i) from funext (fun i => mul_comm _ _)]
  have hTn : ‖T‖ ≤ 2 := by
    rw [hdiag]
    exact orthogonal_diagonal_norm_le Q hQ d 2 (by norm_num)
      (fun i => by rw [abs_of_nonneg (hdlo i)]; exact hdhi i)
  have hweak : ‖T*(1-P)‖ ≤ 1+2*α := by
    rw [hdiag]
    dsimp only [P]
    rw [orthogonal_diagonal_complement Q hQQ, orthogonal_diagonal_mul Q hQ]
    apply orthogonal_diagonal_norm_le Q hQ _ _ (by linarith)
    intro i
    by_cases hi : i.val < r
    · by_cases hs : 1+2*α ≤ d i
      · simp [p, leadingMask, strongFilterIndicator, hi, hs]
        linarith
      · simp only [p, leadingMask, if_pos hi, strongFilterIndicator, if_neg hs, sub_zero, mul_one,
          abs_of_nonneg (hdlo i)]
        linarith
    · simp only [p, leadingMask, if_neg hi, sub_zero, mul_one, abs_of_nonneg (hdlo i)]
      have := hdtail i (Nat.le_of_not_gt hi)
      linarith
  exact strong_filter_residual_of_right_inverse T P Y (H*F) U W α hα.le hU hspan hcomm happrox hTn hweak

end
end HierarchicalAbsoluteSpectral
