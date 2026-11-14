import HierarchicalAbsoluteSpectral.MatrixInequalities

/-!
Noncommuting Young and ideal-refinement algebra in Lemma 5.
The ideal-root identity and weighted proxy error are explicit hypotheses:
this file does not construct the interpolating polynomial from Lemma 4.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k : ℕ}

theorem loewner_of_quadratic {A B : Core k}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ v, quadratic A v ≤ quadratic B v) : A ≤ B := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA)
  intro v
  simpa [quadratic, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] using h v

/-- Weighted Young inequality, proved from a positive quadratic form. -/
theorem weighted_young_vector (W : Core k) (hW : W.PosSemidef)
    (u v : Fin k → ℝ) (ε : ℝ) (hε : 0 < ε) :
    quadratic W (u + v) ≤ (1 + ε) * quadratic W u + (1 + 1/ε) * quadratic W v := by
  have hn := quadratic_nonneg hW (ε • u - v)
  simp only [quadratic, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul,
    sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul] at *
  apply (mul_le_mul_iff_right₀ hε).mp
  simp only [add_mul, mul_add, one_div, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
  nlinarith

/-- Young's inequality for symmetric matrices, without any commutation. -/
theorem weighted_young (W K E : Core k) (hW : W.PosSemidef)
    (hK : Kᵀ = K) (hE : Eᵀ = E) (ε : ℝ) (hε : 0 < ε) :
    (K + E) * W * (K + E) ≤
      (1 + ε) • (K * W * K) + (1 + 1/ε) • (E * W * E) := by
  have hs (J : Core k) (hJ : Jᵀ = J) : (J * W * J).PosSemidef := by
    simpa [hJ] using hW.conjTranspose_mul_mul_same J
  apply loewner_of_quadratic (hs (K + E) (by simp [hK, hE])).isHermitian
    (((hs K hK).smul (by linarith : (0:ℝ) ≤ 1+ε)).add
      ((hs E hE).smul (by positivity : (0:ℝ) ≤ 1+1/ε))).isHermitian
  intro v
  have hquad (J : Core k) (hJ : Jᵀ = J) :
      quadratic (J * W * J) v = quadratic W (J *ᵥ v) := by
    simpa [hJ] using quadratic_congruence W J v
  simpa only [quadratic_add, quadratic_smul, hquad K hK, hquad E hE,
    hquad (K + E) (by simp [hK, hE]), Matrix.add_mulVec] using
      weighted_young_vector W hW (K *ᵥ v) (E *ᵥ v) ε hε

/-- Equations (10)--(12): ideal refinement resets the relaxed coefficient to four.

The assumptions `hroot` and `herror` are the ideal absolute-root identity and
weighted fine-error estimate proved analytically in Lemma 5. Every other
matrix step here is derived using inverse order and noncommuting Young.
-/
theorem ideal_refinement_relaxation
    (P Fstar K Kj E D : Core k) (η κp Cp H h : ℝ)
    (hP : P.PosDef) (hF : Fstar.PosDef) (hD : D.PosSemidef)
    (hK : Kᵀ = K) (hKj : Kjᵀ = Kj) (hE : E = Kj - K)
    (hη : 0 ≤ η) (hκ : 0 ≤ κp)
    (hscale : η * H = 8 * h) (hsmall : 2 * η * κp * (5/4) ≤ 1)
    (hcoarse : P - κp • (Kj * P⁻¹ * Kj) ≤ (Cp * H) • D)
    (hupper : Fstar ≤ (5/4 : ℝ) • P)
    (hroot : Fstar - Kj * Fstar⁻¹ * Kj = (2 * η) • P)
    (herror : E * Fstar⁻¹ * E ≤ (h/2) • D) :
    Fstar - (4 : ℝ) • (K * Fstar⁻¹ * K) ≤ ((16 * Cp + 2) * h) • D := by
  have hs (J : Core k) (hJ : Jᵀ = J) : (J * Fstar⁻¹ * J).PosSemidef := by
    simpa [hJ] using hF.posSemidef.inv.conjTranspose_mul_mul_same J
  have hEsym : Eᵀ = E := by rw [hE]; simp [hK, hKj]
  have hinv : P⁻¹ ≤ (5/4 : ℝ) • Fstar⁻¹ := by
    letI : Invertible (5/4 : ℝ) := invertibleOfNonzero (by norm_num)
    have hi := inverse_order hF hupper
    rw [Matrix.inv_smul _ _ ((Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit), invOf_eq_inv] at hi
    have hi' := smul_le_smul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 5/4)
    simpa [smul_smul] using hi'
  have hcong := star_left_conjugate_le_conjugate hinv Kj
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, hKj,
    Matrix.mul_smul, Matrix.smul_mul] at hcong
  have hyoung := weighted_young Fstar⁻¹ K E hF.posSemidef.inv hK hEsym 1 (by norm_num)
  have hsum : K + E = Kj := by rw [hE]; module
  rw [hsum] at hyoung
  norm_num at hyoung
  apply loewner_of_quadratic
    (hF.isHermitian.sub ((hs K hK).isHermitian.smul (IsSelfAdjoint.all _)))
    (hD.isHermitian.smul (IsSelfAdjoint.all _))
  intro v
  have hc := quadratic_mono hcoarse v
  have hi := quadratic_mono hcong v
  have hr := congrArg (fun A => quadratic A v) hroot
  have he := quadratic_mono herror v
  have hy := quadratic_mono hyoung v
  simp only [quadratic_sub, quadratic_smul, quadratic_add] at hc hi hr he hy ⊢
  have hq := quadratic_nonneg (hs Kj hKj) v
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*η by positivity)
  have hi' := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2*η*κp by positivity)
  have hsmall' := mul_nonneg (sub_nonneg.mpr hsmall) hq
  have hscale' := congrArg (fun z => 2 * Cp * quadratic D v * z) hscale
  nlinarith

/-- Finite relative error resets the coefficient from four to five and yields
exactly `Cnext = 100*(C+1)`. This is the last algebraic step of Lemma 5.
-/
theorem finite_relaxation_reset
    (Fstar Fbar K D : Core k) (δ Cp C h : ℝ)
    (hstar : Fstar.PosDef) (hbar : Fbar.PosDef) (hD : D.PosSemidef)
    (hK : Kᵀ = K) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/100)
    (hCp : 0 ≤ Cp) (hC : 1 ≤ C) (hh : 0 ≤ h) (hCp' : Cp ≤ 2*(C+1))
    (hupper : Fbar ≤ (1+δ) • Fstar)
    (hideal : Fstar - (4 : ℝ) • (K * Fstar⁻¹ * K) ≤ ((16*Cp+2)*h) • D) :
    Fbar - (5 : ℝ) • (K * Fbar⁻¹ * K) ≤ (100*(C+1)*h) • D := by
  have hrel := (relative_perturbation Fstar Fbar K D δ 4 (16*Cp+2) h
    hstar hbar hK hδ (by norm_num) hupper hideal)
  have hrel' := hrel.1.trans hrel.2
  have hquad : (K * Fbar⁻¹ * K).PosSemidef := by
    simpa [hK] using hbar.posSemidef.inv.conjTranspose_mul_mul_same K
  have hconstant : (1+δ)*(16*Cp+2) ≤ 100*(C+1) := by
    have := mul_le_mul_of_nonneg_right hδ' (show 0 ≤ 16*Cp+2 by positivity)
    nlinarith
  have hκ : 4*(1+δ)^2 ≤ (5:ℝ) := by nlinarith
  apply loewner_of_quadratic
    (hbar.isHermitian.sub (hquad.isHermitian.smul (IsSelfAdjoint.all _)))
    (hD.isHermitian.smul (IsSelfAdjoint.all _))
  intro v
  have hv := quadratic_mono hrel' v
  simp only [quadratic_sub, quadratic_smul] at hv ⊢
  have hk := mul_nonneg (sub_nonneg.mpr hκ) (quadratic_nonneg hquad v)
  have hc := mul_le_mul_of_nonneg_right hconstant
    (mul_nonneg hh (quadratic_nonneg hD v))
  nlinarith

end
end HierarchicalAbsoluteSpectral
