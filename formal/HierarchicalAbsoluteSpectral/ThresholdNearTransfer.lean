import HierarchicalAbsoluteSpectral.MinMaxNear

/-! The first assertion of the relaxed min--max transfer lemma. The near
subspace is derived from the normalized pencil's actual sorted eigenvalues. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped InnerProductSpace MatrixOrder
variable {k : ℕ}

theorem real_hermitian_transpose {A : Core k} (hA : A.IsHermitian) : Aᵀ = A := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq

theorem quadratic_neg (A : Core k) (v : Fin k → ℝ) :
    quadratic (-A) v = -quadratic A v := by
  simp [quadratic, Matrix.neg_mulVec, dotProduct_neg]

theorem near_beta_bounds (κ α : ℝ) (hκ : 1 ≤ κ) (hκ' : κ ≤ 5)
    (hα : 0 < α) (hα' : α ≤ 1/(100*κ)) :
    0 < α/(1-κ*α^2) ∧ α/(1-κ*α^2) ≤ 2*α := by
  have hκα : κ*α ≤ 1/100 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 100*κ)).mp hα'
    nlinarith
  have ha : α ≤ 1/100 := by nlinarith
  have hd : 0 < 1-κ*α^2 := by nlinarith
  refine ⟨div_pos hα hd, (div_le_iff₀ hd).mpr ?_⟩
  nlinarith

theorem normalized_defect_quadratic (R K : Core k) (hR : IsUnit R.det)
    (κ : ℝ) (v : EuclideanSpace ℝ (Fin k)) :
    quadratic (inverseMetric R - κ • (K*(inverseMetric R)⁻¹*K))
      (ofLp (R.toEuclideanLin v)) =
    ⟪v,v⟫_ℝ - κ*⟪v,(Rᵀ*K*R).toEuclideanLin ((Rᵀ*K*R).toEuclideanLin v)⟫_ℝ := by
  rw [quadratic_sub, quadratic_smul, metric_norm_identity R hR]
  congr 1
  rw [← quadratic_normalized, inverseMetric_inv R hR, quadratic_eq_inner]
  congr 2
  apply ofLp_injective
  simp only [Matrix.toLpLin_apply, ofLp_toLp, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem near_threshold_generalized_lower
    (Q D R Rb : Core k) (hQ : Q.PosSemidef)
    (hR : IsUnit R.det) (hRb : IsUnit Rb.det) (t κ C h α : ℝ)
    (hκ : 1 ≤ κ) (hκ' : κ ≤ 5) (hC : 0 ≤ C) (hh : 0 ≤ h)
    (hα : 0 < α) (hα' : α ≤ 1/(100*κ))
    (hdom : -(inverseMetric R) ≤ t • inverseMetric Rb-Q)
    (hinvariant : inverseMetric R - κ •
      ((t • inverseMetric Rb-Q)*(inverseMetric R)⁻¹*(t • inverseMetric Rb-Q)) ≤ (C*h) • D)
    (hD : D ≤ (2:ℝ) • (t • inverseMetric Rb+Q))
    (j : Fin k)
    (hnear : orderedEigenvalue (Rᵀ*(t • inverseMetric Rb-Q)*R)
      (normalized_isHermitian R _ (by simp [inverseMetric, Matrix.transpose_mul,
        real_hermitian_transpose hQ.isHermitian])) j.rev ≤ α) :
    let x := 2*C*(α/(1-κ*α^2))*h
    ((1-x)/(1+x))*t ≤ orderedEigenvalue (Rbᵀ*Q*Rb)
      (normalized_isHermitian Rb Q hQ.isHermitian.eq) j := by
  let K := t • inverseMetric Rb-Q
  let F := inverseMetric R
  let A := Rᵀ*K*R
  have hK : Kᵀ = K := by
    simp [K, inverseMetric, Matrix.transpose_mul, real_hermitian_transpose hQ.isHermitian]
  have hA := normalized_isHermitian R K hK
  let S := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let V := spectralBottomEmbedding A.toEuclideanLin S finrank_euclideanSpace_fin j
  let W := (Rb⁻¹).toEuclideanLin.comp (R.toEuclideanLin.comp V)
  let β := α/(1-κ*α^2)
  let x := 2*C*β*h
  have hβ := near_beta_bounds κ α hκ hκ' hα hα'
  have hx : 0 ≤ x := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) hβ.1.le) hh
  have hxp : 0 < 1+x := by linarith
  have hW : Function.Injective W :=
    (toEuclideanLin_injective_of_det _ (Matrix.isUnit_nonsing_inv_det Rb hRb)).comp
      ((toEuclideanLin_injective_of_det R hR).comp
        (spectralBottomEmbedding_injective _ S finrank_euclideanSpace_fin j))
  have hlo : ∀ i, -1 ≤ S.eigenvalues finrank_euclideanSpace_fin i := by
    apply eigenvalue_lower_of_form A.toEuclideanLin S finrank_euclideanSpace_fin (-1)
    intro v
    have hd := quadratic_mono hdom (ofLp (R.toEuclideanLin v))
    rw [quadratic_neg, metric_norm_identity R hR, ← quadratic_normalized] at hd
    simpa only [quadratic_eq_inner, neg_one_mul] using hd
  apply eigenvalue_lower_of_injective_form (Rbᵀ*Q*Rb).toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (normalized_isHermitian Rb Q hQ.isHermitian.eq))
    finrank_euclideanSpace_fin j W hW
  intro z
  have hchange : Rb.toEuclideanLin (W z) = R.toEuclideanLin (V z) :=
    toEuclideanLin_inv_cancel Rb hRb _
  let y := ofLp (R.toEuclideanLin (V z))
  have hnearform : quadratic K y ≤ β*quadratic (F-κ • (K*F⁻¹*K)) y := by
    have hf := spectralBottomEmbedding_near_form A.toEuclideanLin S finrank_euclideanSpace_fin
      j κ α hκ hκ' hα hα' hlo hnear z
    change ⟪V z,A.toEuclideanLin (V z)⟫_ℝ ≤
      β*(⟪V z,V z⟫_ℝ-κ*⟪V z,A.toEuclideanLin (A.toEuclideanLin (V z))⟫_ℝ) at hf
    rw [← normalized_defect_quadratic R K hR κ (V z)] at hf
    simpa only [A, ← quadratic_eq_inner, quadratic_normalized] using hf
  have hfinal : quadratic K y ≤ x*(t*quadratic (inverseMetric Rb) y+quadratic Q y) := by
    calc
      quadratic K y ≤ β*quadratic (F-κ • (K*F⁻¹*K)) y := hnearform
      _ ≤ β*((C*h)*quadratic D y) :=
        mul_le_mul_of_nonneg_left (by simpa only [quadratic_smul] using quadratic_mono hinvariant y) hβ.1.le
      _ ≤ β*((C*h)*(2*(t*quadratic (inverseMetric Rb) y+quadratic Q y))) := by
        apply mul_le_mul_of_nonneg_left _ hβ.1.le
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hh)
        simpa only [quadratic_smul, quadratic_add] using quadratic_mono hD y
      _ = _ := by dsimp [x]; ring
  have hpencil : quadratic K y = t*quadratic (inverseMetric Rb) y-quadratic Q y := by
    simp only [K, quadratic_sub, quadratic_smul]
  have hgeneral : ((1-x)/(1+x))*t*quadratic (inverseMetric Rb) y ≤ quadratic Q y := by
    calc
      _ = ((1-x)*t*quadratic (inverseMetric Rb) y)/(1+x) := by ring
      _ ≤ quadratic Q y := (div_le_iff₀ hxp).mpr (by rw [hpencil] at hfinal; nlinarith)
  have hnorm : quadratic (inverseMetric Rb) y = ⟪W z,W z⟫_ℝ := by
    rw [show y = ofLp (Rb.toEuclideanLin (W z)) from congrArg ofLp hchange.symm]
    exact metric_norm_identity Rb hRb _
  rw [← quadratic_eq_inner, quadratic_normalized, hchange, ← hnorm]
  exact hgeneral

end
end HierarchicalAbsoluteSpectral
