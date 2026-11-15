import HierarchicalAbsoluteSpectral.ThresholdMassDecision
import HierarchicalAbsoluteSpectral.StrongFilterFinalBudget

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {k : ℕ}

theorem near_threshold_literal_upper
    (Q D R Rb : Core k) (hQ : Q.PosSemidef)
    (hR : IsUnit R.det) (hRb : IsUnit Rb.det) (t κ C h θ : ℝ)
    (ht : 0 ≤ t) (hκ : 1 ≤ κ) (hκ' : κ ≤ 5) (hC : 1 ≤ C)
    (hh : 0 < h) (hθ : 0 < θ) (hθh : θ ≤ h) (hθ1 : θ ≤ 1)
    (hdom : -(inverseMetric R) ≤ t • inverseMetric Rb-Q)
    (hinvariant : inverseMetric R-κ •
      ((t • inverseMetric Rb-Q)*(inverseMetric R)⁻¹*(t • inverseMetric Rb-Q)) ≤ (C*h) • D)
    (hD : D ≤ (2:ℝ) • (t • inverseMetric Rb+Q))
    (j : Fin k)
    (hnear : orderedEigenvalue (Rᵀ*(t • inverseMetric Rb-Q)*R)
      (normalized_isHermitian R _ (by
        simp [inverseMetric,Matrix.transpose_mul,real_hermitian_transpose hQ.isHermitian])) j.rev ≤
        literalFinalAlpha C h θ) :
    t ≤ ((1+literalFinalX C h θ)/(1-literalFinalX C h θ))*
      orderedEigenvalue (Rbᵀ*Q*Rb) (normalized_isHermitian Rb Q hQ.isHermitian.eq) j := by
  let α := literalFinalAlpha C h θ
  let β := α/(1-κ*α^2)
  let x := 2*C*β*h
  let X := literalFinalX C h θ
  have hb := literal_final_tolerance_budget C h θ hC hh hθ hθh
  have hα : 0 < α := hb.alpha_positive
  have hαsmall : α ≤ 1/(100*κ) := by
    apply hb.alpha_small.trans
    apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<1000000) (by positivity : 0<100*κ)).mpr
    nlinarith
  have hβ := near_beta_bounds κ α hκ hκ' hα hαsmall
  have hβp : 0 < β := hβ.1
  have hx0 : 0 ≤ x := mul_nonneg (mul_nonneg (by linarith : 0≤2*C) hβp.le) hh.le
  have hxX : x ≤ X := by
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hβ.2 (by positivity : 0≤2*C)) hh.le
    dsimp only [x,X,literalFinalX]
    nlinarith only [hm]
  have hX0 : 0 ≤ X := hb.near_nonneg
  have hX1 : X < 1 := by dsimp only [X]; have := hb.near_error; linarith
  have hx1 : x < 1 := hxX.trans_lt hX1
  have hl := near_threshold_generalized_lower Q D R Rb hQ hR hRb t κ C h α
    hκ hκ' (by linarith) hh.le hα hαsmall hdom hinvariant hD j hnear
  change ((1-x)/(1+x))*t ≤ _ at hl
  have htarget := orderedEigenvalue_nonneg (Rbᵀ*Q*Rb)
    (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using hQ.mul_mul_conjTranspose_same Rbᵀ) j
  have ht' : t ≤ ((1+x)/(1-x))*
      orderedEigenvalue (Rbᵀ*Q*Rb) (normalized_isHermitian Rb Q hQ.isHermitian.eq) j := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0<1-x)).mpr
    rw [div_mul_eq_mul_div] at hl
    have hh' := (div_le_iff₀ (by linarith : 0<1+x)).mp hl
    nlinarith only [hh']
  have hratio : (1+x)/(1-x) ≤ (1+X)/(1-X) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  exact ht'.trans (mul_le_mul_of_nonneg_right hratio htarget)

end
end HierarchicalAbsoluteSpectral
