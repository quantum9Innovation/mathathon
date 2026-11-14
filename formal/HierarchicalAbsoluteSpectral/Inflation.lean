import HierarchicalAbsoluteSpectral.WeightedError

/-! The inflated coarse invariant (10), derived from the preceding invariant
and the fine Loewner proxy. The noncommuting error is explicitly charged. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {k : ℕ}

def inflatedDefectConstant (C κ ε : ℝ) : ℝ :=
  (1+ε)*C + 8*κ*ε*(1+ε)^2

theorem inflated_constant_bounds (C κ ε : ℝ)
    (hC : 1 ≤ C) (hκ : 0 ≤ κ) (hκ' : κ ≤ 5)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1/1024) :
    0 ≤ inflatedDefectConstant C κ ε ∧
    inflatedDefectConstant C κ ε ≤ 2*(C+1) ∧ κ*(1+ε)^3 ≤ 6 := by
  have he1 : ε ≤ 1 := by linarith
  have hs : (1+ε)^2 ≤ 4 := by nlinarith
  have hp : 0 ≤ 8*κ*ε := by positivity
  have hterm := mul_le_mul_of_nonneg_left hs hp
  have hkterm := mul_le_mul_of_nonneg_right hκ' hε
  have heC := mul_le_mul_of_nonneg_right he1 (show 0 ≤ C by linarith)
  have hcube : (1+ε)^3 ≤ (1+(1/1024 : ℝ))^3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hkpow := mul_le_mul hκ' hcube (by positivity) (by norm_num)
  dsimp [inflatedDefectConstant]
  constructor
  · positivity
  constructor
  · nlinarith
  · norm_num at hkpow
    linarith

theorem inflated_coarse_invariant
    (F K Kj D : Core k) (κ C h H ε : ℝ)
    (hF : F.PosDef) (hD : D.PosDef) (hK : Kᵀ = K) (hKj : Kjᵀ = Kj)
    (hκ : 0 ≤ κ) (hh : 0 < h) (hH : 0 < H) (hε : 0 < ε)
    (hscale : h = ε*H)
    (hfloor : (8*H) • D ≤ F)
    (hlow : -((8*h) • D) ≤ Kj-K) (hupper : Kj-K ≤ (8*h) • D)
    (hinvariant : F - κ • (K * F⁻¹ * K) ≤ (C*H) • D) :
    (1+ε) • F - (κ*(1+ε)^3) • (Kj * ((1+ε) • F)⁻¹ * Kj) ≤
      (inflatedDefectConstant C κ ε * H) • D := by
  have hEsym : (Kj-K)ᵀ = Kj-K := by simp [hKj, hK]
  have herr := fine_error_previous_metric D F (Kj-K) h H hD hEsym hh hH
    hlow hupper hfloor
  have hyoung := weighted_young F⁻¹ Kj (-(Kj-K)) hF.posSemidef.inv hKj
    (by simp [hKj, hK]) ε hε
  have hsum : Kj + -(Kj-K) = K := by module
  rw [hsum] at hyoung
  simp only [neg_mul, mul_neg, neg_neg] at hyoung
  have hPF : ((1+ε) • F).PosDef :=
    (IsStrictlyPositive.smul (show 0 < 1+ε by linarith) hF.isStrictlyPositive).posDef
  have hj : (Kj * ((1+ε) • F)⁻¹ * Kj).PosSemidef := by
    simpa [hKj] using hPF.posSemidef.inv.conjTranspose_mul_mul_same Kj
  apply loewner_of_quadratic
    (hPF.isHermitian.sub (hj.isHermitian.smul (IsSelfAdjoint.all _)))
    (hD.isHermitian.smul (IsSelfAdjoint.all _))
  intro v
  have hv := quadratic_mono hinvariant v
  have he := quadratic_mono herr v
  have hy := quadratic_mono hyoung v
  letI : Invertible (1+ε) := invertibleOfNonzero (by linarith)
  rw [Matrix.inv_smul _ _ ((Matrix.isUnit_iff_isUnit_det F).mp hF.isUnit), invOf_eq_inv]
  simp only [quadratic_sub, quadratic_add, quadratic_smul,
    Matrix.mul_smul, Matrix.smul_mul] at hv he hy ⊢
  have hkcoeff : κ*(1+ε)^3*(1+ε)⁻¹ = κ*(1+ε)^2 := by
    field_simp
  have hcoeff : (1+ε)*C*H + κ*(1+ε)*(1+1/ε)*(8*h^2/H) =
      inflatedDefectConstant C κ ε * H := by
    rw [hscale]
    dsimp [inflatedDefectConstant]
    field_simp
    ring
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ 1+ε by linarith)
  have hy' := mul_le_mul_of_nonneg_left hy (show 0 ≤ κ*(1+ε) by positivity)
  have he' := mul_le_mul_of_nonneg_left he (show 0 ≤ κ*(1+ε)*(1+1/ε) by positivity)
  have hcoeff' := congrArg (fun z => z*quadratic D v) hcoeff
  have hkcoeff' := congrArg (fun z => z*quadratic (Kj * F⁻¹ * Kj) v) hkcoeff
  nlinarith

theorem inflated_proxy_domination (F K Kj D : Core k) (h H ε : ℝ)
    (hε : 0 ≤ ε) (hscale : h = ε*H)
    (hfloor : (8*H) • D ≤ F) (hKlo : -F ≤ K) (hKup : K ≤ F)
    (hlow : -((8*h) • D) ≤ Kj-K) (hupper : Kj-K ≤ (8*h) • D) :
    -((1+ε) • F) ≤ Kj ∧ Kj ≤ (1+ε) • F := by
  have hscaled : (8*h) • D ≤ ε • F := by
    have hs := smul_le_smul_of_nonneg_left hfloor hε
    simpa [hscale, smul_smul, mul_assoc, mul_left_comm, mul_comm] using hs
  have hElo : -(ε • F) ≤ Kj-K := (neg_le_neg hscaled).trans hlow
  have hEup : Kj-K ≤ ε • F := hupper.trans hscaled
  have hlo := add_le_add hKlo hElo
  have hup := add_le_add hKup hEup
  constructor
  · convert hlo using 1 <;> module
  · convert hup using 1 <;> module

end
end HierarchicalAbsoluteSpectral
