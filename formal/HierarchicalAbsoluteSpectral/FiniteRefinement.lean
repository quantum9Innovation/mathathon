import HierarchicalAbsoluteSpectral.AnalyticRefinement
import HierarchicalAbsoluteSpectral.PolynomialMetric

/-!
The actual finite inverse factor R_j=R_P*p(A_j), with every metric invariant
derived from the previous invariant and the polynomial's scalar error bound.
The missing approximation construction is precisely the uniform polynomial
theorem, including its degree and coefficient-generation operation count.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open scoped MatrixOrder
variable {k : ℕ}

def refinementTolerance (h B : ℝ) : ℝ := h / (10^6 * (1+B))

theorem refinement_tolerance_bounds (h B : ℝ) (hh : 0 < h) (hh' : h ≤ 1/64)
    (hB : 0 ≤ B) :
    0 < refinementTolerance h B ∧ refinementTolerance h B ≤ 1/4 ∧
    4 * refinementTolerance h B ≤ 1/100 ∧
    (4 * refinementTolerance h B) * (2*B) ≤ h := by
  have hd : 0 < 10^6 * (1+B) := by positivity
  have ht : 0 < refinementTolerance h B := by unfold refinementTolerance; positivity
  have hle : refinementTolerance h B ≤ h/10^6 := by
    unfold refinementTolerance
    apply div_le_div_of_nonneg_left hh.le (by norm_num)
    nlinarith
  refine ⟨ht, by linarith, by linarith, ?_⟩
  unfold refinementTolerance
  rw [mul_div_assoc', div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  nlinarith [mul_nonneg hh.le hB]

theorem finite_metric_bounds (Fs Fb K D : Core k) (h B ε δ : ℝ)
    (hD : D.PosSemidef) (hh : 0 ≤ h) (hB : 0 ≤ B)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1/1024) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/100)
    (hδB : δ*(2*B) ≤ h)
    (hfloor : (128*h) • D ≤ Fs)
    (hbound : Fs ≤ ((5/4)*(1+ε)*B) • D)
    (hminus : (56*h) • D ≤ Fs-K) (hplus : (56*h) • D ≤ Fs+K)
    (hrelativeLo : (1-δ) • Fs ≤ Fb) (hrelativeUp : Fb ≤ (1+δ) • Fs) :
    (8*h) • D ≤ Fb ∧ Fb ≤ (2*B) • D ∧
    (55*h) • D ≤ Fb-K ∧ (55*h) • D ≤ Fb+K := by
  have hscalar : (5/4 : ℝ)*(1+ε) ≤ 2 := by linarith
  have hFs2 : Fs ≤ (2*B) • D := hbound.trans
    (smul_le_smul_of_nonneg_right (mul_le_mul_of_nonneg_right hscalar hB) hD.nonneg)
  have hδFs : δ • Fs ≤ h • D := by
    have hs := smul_le_smul_of_nonneg_left hFs2 hδ
    apply hs.trans
    simpa [smul_smul] using smul_le_smul_of_nonneg_right hδB hD.nonneg
  have hnear : Fs - h • D ≤ Fb := by
    apply (sub_le_sub_left hδFs Fs).trans
    convert hrelativeLo using 1
    module
  have hfloor127 : (127*h) • D ≤ Fb := by
    have hs := sub_le_sub_right hfloor (h • D)
    apply (show (127*h) • D ≤ Fs - h • D from by convert hs using 1; module).trans hnear
  have hscalarUp : (1+δ)*(5/4)*(1+ε) ≤ (2:ℝ) := by
    have h1 : (1+δ)*(5/4) ≤ (101/100 : ℝ)*(5/4) := by linarith
    have h2 : 1+ε ≤ (1025/1024 : ℝ) := by linarith
    have hs := mul_le_mul h1 h2 (by positivity : 0 ≤ 1+ε) (by norm_num)
    norm_num at hs
    linarith
  have hFb2 : Fb ≤ (2*B) • D := by
    apply hrelativeUp.trans
    apply (smul_le_smul_of_nonneg_left hbound (show 0 ≤ 1+δ by linarith)).trans
    simpa [smul_smul, mul_assoc] using smul_le_smul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hscalarUp hB) hD.nonneg
  refine ⟨(smul_le_smul_of_nonneg_right (by nlinarith : 8*h ≤ 127*h) hD.nonneg).trans hfloor127,
    hFb2, ?_, ?_⟩
  · have hs : (55*h) • D ≤ Fs-K-h • D := by
      convert sub_le_sub_right hminus (h • D) using 1
      module
    have ht : Fs-K-h • D ≤ Fb-K := by
      convert sub_le_sub_right hnear K using 1
      module
    exact hs.trans ht
  · have hs : (55*h) • D ≤ Fs+K-h • D := by
      convert sub_le_sub_right hplus (h • D) using 1
      module
    have ht : Fs+K-h • D ≤ Fb+K := by
      convert add_le_add hnear (le_refl K) using 1
      module
    exact hs.trans ht

/-- All inequalities in (9) and the 55h margins for the executed finite factor.
Only the scalar polynomial approximation remains an input to this local
construction lemma; it is not replaced by an assumed metric certificate.
-/
theorem finite_refinement_invariant
    (R K Kj D : Core k) (κ C B h H ε : ℝ)
    (hR : IsUnit R.det) (hD : D.PosDef) (hK : Kᵀ = K) (hKj : Kjᵀ = Kj)
    (hκ : 0 ≤ κ) (hκ' : κ ≤ 5) (hC : 1 ≤ C) (hB : 0 ≤ B)
    (hh : 0 < h) (hh' : h ≤ 1/64) (hH : 0 < H) (hε : 0 < ε) (hε' : ε ≤ 1/1024)
    (hscale : h = ε*H)
    (hfloor : (8*H) • D ≤ inverseMetric R)
    (hbound : inverseMetric R ≤ B • D)
    (hKlo : -inverseMetric R ≤ K) (hKup : K ≤ inverseMetric R)
    (hlow : -((8*h) • D) ≤ Kj-K) (hupper : Kj-K ≤ (8*h) • D)
    (hinvariant : inverseMetric R - κ • (K * (inverseMetric R)⁻¹ * K) ≤ (C*H) • D)
    (p : ℝ[X])
    (happrox : ∀ x ∈ Set.Icc (-1:ℝ) 1,
      |p.eval x * Real.sqrt (absoluteRootScalar (8*ε) x) - 1| ≤ refinementTolerance h B) :
    IsUnit (refinedInverseFactor R Kj ε p).det ∧
    (8*h) • D ≤ inverseMetric (refinedInverseFactor R Kj ε p) ∧
    inverseMetric (refinedInverseFactor R Kj ε p) ≤ (2*B) • D ∧
    (55*h) • D ≤ inverseMetric (refinedInverseFactor R Kj ε p)-K ∧
    (55*h) • D ≤ inverseMetric (refinedInverseFactor R Kj ε p)+K ∧
    inverseMetric (refinedInverseFactor R Kj ε p) - (5:ℝ) •
      (K * (inverseMetric (refinedInverseFactor R Kj ε p))⁻¹ * K) ≤ (100*(C+1)*h) • D := by
  have hideal := constructed_ideal_refinement R K Kj D κ C B h H ε hR hD hK hKj
    hκ hκ' hC hB hh hH hε hε' hscale hfloor hbound hKlo hKup hlow hupper hinvariant
  have ht := refinement_tolerance_bounds h B hh hh' hB
  have hτpos := ht.1
  have hRp := inflatedInverseFactor_isUnit R hR ε hε.le
  have hdom := inflated_proxy_domination (inverseMetric R) K Kj D h H ε hε.le
    hscale hfloor hKlo hKup hlow hupper
  rw [← inflatedInverseFactor_metric R hR ε hε.le] at hdom
  have hspec := normalized_spectrum_of_bounds (inflatedInverseFactor R ε) Kj hRp hKj hdom.1 hdom.2
  have hrel := refinedInverseFactor_relative R Kj hR hKj ε (refinementTolerance h B) hε
    ht.1.le ht.2.1 p (fun x hx => happrox x (hspec x hx))
  have hfb := inverseMetric_posDef _ hrel.1
  have hb := finite_metric_bounds (refinementIdeal R Kj ε)
    (inverseMetric (refinedInverseFactor R Kj ε p)) K D h B ε (4*refinementTolerance h B)
    hD.posSemidef hh.le hB hε.le hε' (by positivity) ht.2.2.1 ht.2.2.2
    hideal.2.1 hideal.2.2.1 hideal.2.2.2.1 hideal.2.2.2.2.1 hrel.2.1 hrel.2.2
  have hdefect := finite_relaxation_reset (refinementIdeal R Kj ε)
    (inverseMetric (refinedInverseFactor R Kj ε p)) K D (4*refinementTolerance h B)
    (2*(C+1)) C h hideal.1 hfb hD.posSemidef hK (by positivity) ht.2.2.1
    (by positivity) hC hh.le (le_refl _) hrel.2.2
    (by convert hideal.2.2.2.2.2 using 1; congr 1; ring)
  exact ⟨hrel.1, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hdefect⟩

end
end HierarchicalAbsoluteSpectral
