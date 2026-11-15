import HierarchicalAbsoluteSpectral.MinMaxContinuity
import HierarchicalAbsoluteSpectral.CoarseAlgebraRangeProgram
import HierarchicalAbsoluteSpectral.StrongFilterMasks

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp Filter
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {k r w : ℕ}

def regularizedRangeProjector (Y : Matrix (Fin k) (Fin r) ℝ) (a : ℝ) : Core k :=
  (Y*Yᵀ)*(Y*Yᵀ+a • (1 : Core k))⁻¹

theorem orthogonal_projector_spectral
    (Y : Matrix (Fin k) (Fin r) ℝ) (U : Matrix (Fin k) (Fin w) ℝ)
    (V : Matrix (Fin r) (Fin w) ℝ) (hU : Uᵀ*U = 1)
    (hUY : U*Uᵀ*Y = Y) (hUV : U = Y*V) :
    let H := Y*Yᵀ
    let hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.posSemidef_self_mul_conjTranspose Y).isHermitian : H.IsHermitian)
    U*Uᵀ = strongSpectralQ H hs*Matrix.diagonal
      (fun i => if strongEigenvalues H hs i = 0 then 0 else 1)*(strongSpectralQ H hs)ᵀ := by
  let H := Y*Yᵀ
  have hHerm : H.IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_self_mul_conjTranspose Y).isHermitian
  let hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hHerm
  let Q := strongSpectralQ H hs
  let d := strongEigenvalues H hs
  let P := U*Uᵀ
  have hPH : P*H = H := by
    calc
      _ = (U*Uᵀ*Y)*Yᵀ := by simp only [P,H,Matrix.mul_assoc]
      _ = H := by rw [hUY]
  have hPQ : P*Q = Q*Matrix.diagonal (fun i => if d i = 0 then 0 else 1) := by
    ext i j
    let v : Fin k → ℝ := fun i => Q i j
    have heig : H*ᵥ v = d j • v := by
      have hh := congrArg ofLp (hs.apply_eigenvectorBasis finrank_euclideanSpace_fin j)
      simpa only [v,Q,d,strongSpectralQ,strongSpectralBasis,strongEigenvalues,
        Matrix.toLpLin_apply, ofLp_toLp, ofLp_smul,
        RCLike.ofReal_real_eq_id,id_eq] using hh
    rw [Matrix.mul_diagonal]
    change (P*ᵥ v) i = v i*(if d j = 0 then 0 else 1)
    by_cases hd : d j = 0
    · have hHv : H*ᵥ v = 0 := by simpa only [hd,zero_smul] using heig
      have hYv : Yᵀ*ᵥ v = 0 := by
        apply (Matrix.self_mul_conjTranspose_mulVec_eq_zero Y v).mp
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hHv
      have hPv : P*ᵥ v = 0 := by
        simp only [P,hUV,Matrix.transpose_mul,Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
          hYv,Matrix.mulVec_zero]
      simp only [hPv,Pi.zero_apply,hd,if_true,mul_zero]
    · have hh := congrArg (fun A : Core k => A*ᵥ v) hPH
      rw [← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul] at hh
      have hi := congrFun hh i
      have heigi := congrFun heig i
      simp only [Pi.smul_apply,smul_eq_mul] at hi heigi
      have heq : (P*ᵥ v) i = v i := (mul_left_cancel₀ hd) hi
      simp only [hd,if_false,mul_one,heq]
  calc
    P = (P*Q)*Qᵀ := by rw [Matrix.mul_assoc,strongSpectralQ_coGram H hs,Matrix.mul_one]
    _ = _ := by rw [hPQ]

theorem regularizedRangeProjector_spectral (Y : Matrix (Fin k) (Fin r) ℝ) (a : ℝ) (ha : 0 < a) :
    let H := Y*Yᵀ
    let hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.posSemidef_self_mul_conjTranspose Y).isHermitian : H.IsHermitian)
    regularizedRangeProjector Y a = strongSpectralQ H hs*Matrix.diagonal
      (fun i => strongEigenvalues H hs i/(strongEigenvalues H hs i+a))*(strongSpectralQ H hs)ᵀ := by
  let H := Y*Yᵀ
  have hPSD : H.PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose Y
  let hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hPSD.isHermitian
  let Q := strongSpectralQ H hs
  let d := strongEigenvalues H hs
  have hd : ∀ i, d i+a ≠ 0 := fun i => ne_of_gt (add_pos_of_nonneg_of_pos (orderedEigenvalue_nonneg H hPSD i) ha)
  have hshift : H+a • (1 : Core k) = Q*Matrix.diagonal (fun i => d i+a)*Qᵀ := by
    have hdiag : Matrix.diagonal (fun i => d i+a) = Matrix.diagonal d+a • (1 : Core k) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply,Matrix.one_apply,hij]
    rw [hdiag]
    simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,
      Q,d,strongSpectralQ_coGram H hs,← strongSpectralQ_diagonalizes H hs]
  have hinv : (H+a • (1 : Core k))⁻¹ = Q*Matrix.diagonal (fun i => (d i+a)⁻¹)*Qᵀ := by
    apply Matrix.inv_eq_right_inv
    rw [hshift,orthogonal_diagonal_mul Q (strongSpectralQ_gram H hs)]
    simp only [mul_inv_cancel₀ (hd _)]
    simp only [Matrix.diagonal_one,Matrix.mul_one]
    exact strongSpectralQ_coGram H hs
  change H*(H+a • (1 : Core k))⁻¹ = Q*Matrix.diagonal (fun i => d i/(d i+a))*Qᵀ
  rw [hinv,strongSpectralQ_diagonalizes H hs,
    orthogonal_diagonal_mul Q (strongSpectralQ_gram H hs)]
  rfl

theorem regularizedRangeProjector_tendsto
    (Y : Matrix (Fin k) (Fin r) ℝ) (U : Matrix (Fin k) (Fin w) ℝ)
    (V : Matrix (Fin r) (Fin w) ℝ) (hU : Uᵀ*U = 1)
    (hUY : U*Uᵀ*Y = Y) (hUV : U = Y*V) :
    Tendsto (fun n : ℕ => regularizedRangeProjector Y (1/((n:ℝ)+1))) atTop (𝓝 (U*Uᵀ)) := by
  let H := Y*Yᵀ
  have hHerm : H.IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_self_mul_conjTranspose Y).isHermitian
  let hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hHerm
  let Q := strongSpectralQ H hs
  let d := strongEigenvalues H hs
  have hscalar (i : Fin k) : Tendsto (fun n : ℕ => d i/(d i+1/((n:ℝ)+1))) atTop
      (𝓝 (if d i = 0 then 0 else 1)) := by
    by_cases hd : d i = 0
    · simp only [hd,zero_div,if_true]
      exact tendsto_const_nhds
    · have hh := (tendsto_const_nhds (x := d i)).div
        ((tendsto_const_nhds (x := d i)).add tendsto_one_div_add_atTop_nhds_zero_nat) (by simpa using hd)
      have heq : ((fun _ : ℕ => d i)/(fun n : ℕ => d i+1/((n:ℝ)+1))) =
          (fun n : ℕ => d i/(d i+1/((n:ℝ)+1))) := by funext n; rfl
      rw [heq] at hh
      simpa only [add_zero,div_self hd,if_neg hd,Pi.div_apply,Pi.add_apply] using hh
  have hdiag : Tendsto (fun n : ℕ => Matrix.diagonal (fun i => d i/(d i+1/((n:ℝ)+1)))) atTop
      (𝓝 (Matrix.diagonal (fun i => if d i = 0 then 0 else 1))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq] using hscalar i
    · simp only [Matrix.diagonal_apply_ne _ hij]
      exact tendsto_const_nhds
  have hh := ((tendsto_const_nhds (x := Q)).mul hdiag).mul (tendsto_const_nhds (x := Qᵀ))
  rw [← orthogonal_projector_spectral Y U V hU hUY hUV] at hh
  convert hh using 1
  funext n
  exact regularizedRangeProjector_spectral Y _ (by positivity)

end
end HierarchicalAbsoluteSpectral
