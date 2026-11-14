import HierarchicalAbsoluteSpectral.IdealMetric
import HierarchicalAbsoluteSpectral.Inflation

/-!
Construct the ideal metric in one refinement and prove its complete floor,
upper bound, two physical margins and relaxed defect from the PREVIOUS
invariant and the fine Loewner proxy. The root identity and weighted error
are proved internally; neither is supplied as a certificate hypothesis.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {k : ℕ}

def refinementIdeal (R Kj : Core k) (ε : ℝ) : Core k :=
  idealMetric (inflatedInverseFactor R ε) Kj (8*ε)

theorem constructed_ideal_refinement
    (R K Kj D : Core k) (κ C B h H ε : ℝ)
    (hR : IsUnit R.det) (hD : D.PosDef) (hK : Kᵀ = K) (hKj : Kjᵀ = Kj)
    (hκ : 0 ≤ κ) (hκ' : κ ≤ 5) (hC : 1 ≤ C) (_hB : 0 ≤ B)
    (hh : 0 < h) (hH : 0 < H) (hε : 0 < ε) (hε' : ε ≤ 1/1024)
    (hscale : h = ε*H)
    (hfloor : (8*H) • D ≤ inverseMetric R)
    (hbound : inverseMetric R ≤ B • D)
    (hKlo : -inverseMetric R ≤ K) (hKup : K ≤ inverseMetric R)
    (hlow : -((8*h) • D) ≤ Kj-K) (hupper : Kj-K ≤ (8*h) • D)
    (hinvariant : inverseMetric R - κ • (K * (inverseMetric R)⁻¹ * K) ≤ (C*H) • D) :
    (refinementIdeal R Kj ε).PosDef ∧
    (128*h) • D ≤ refinementIdeal R Kj ε ∧
    refinementIdeal R Kj ε ≤ ((5/4)*(1+ε)*B) • D ∧
    (56*h) • D ≤ refinementIdeal R Kj ε - K ∧
    (56*h) • D ≤ refinementIdeal R Kj ε + K ∧
    refinementIdeal R Kj ε - (4 : ℝ) •
      (K * (refinementIdeal R Kj ε)⁻¹ * K) ≤ ((32*(C+1)+2)*h) • D := by
  let Rp := inflatedInverseFactor R ε
  let P := inverseMetric Rp
  let Fs := refinementIdeal R Kj ε
  have hRp : IsUnit Rp.det := inflatedInverseFactor_isUnit R hR ε hε.le
  have hP : P = (1+ε) • inverseMetric R := inflatedInverseFactor_metric R hR ε hε.le
  have hFprev := inverseMetric_posDef R hR
  have hPpos : P.PosDef := inverseMetric_posDef Rp hRp
  have hFs : Fs.PosDef := idealMetric_posDef Rp Kj hRp hKj (8*ε) (by positivity)
  have hFleP : inverseMetric R ≤ P := by
    rw [hP, add_smul, one_smul]
    exact le_add_of_nonneg_right (smul_nonneg hε.le hFprev.posSemidef.nonneg)
  have hPfloor : (8*H) • D ≤ P := hfloor.trans hFleP
  have hdom := inflated_proxy_domination (inverseMetric R) K Kj D h H ε hε.le hscale
    hfloor hKlo hKup hlow hupper
  rw [← hP] at hdom
  have hspec := normalized_spectrum_of_bounds Rp Kj hRp hKj hdom.1 hdom.2
  have hupperRoot := idealMetric_upper Rp Kj hKj (8*ε) (by positivity) hspec
  have hFsP : Fs ≤ (5/4 : ℝ) • P := by
    apply hupperRoot.trans
    exact smul_le_smul_of_nonneg_right (by linarith : 1+2*(8*ε) ≤ (5/4:ℝ))
      hPpos.posSemidef.nonneg
  have hFsBound : Fs ≤ ((5/4)*(1+ε)*B) • D := by
    apply hFsP.trans
    rw [hP]
    simpa [smul_smul, mul_assoc] using
      smul_le_smul_of_nonneg_left hbound (show 0 ≤ (5/4:ℝ)*(1+ε) by positivity)
  have hFsFloor : (128*h) • D ≤ Fs := by
    have hs := smul_le_smul_of_nonneg_left hPfloor (show 0 ≤ 2*(8*ε) by positivity)
    have hc : (2*(8*ε))*(8*H) = 128*h := by rw [hscale]; ring
    rw [smul_smul, hc] at hs
    exact hs.trans (idealMetric_floor Rp Kj hKj (8*ε) (by positivity))
  have hηP : (64*h) • D ≤ (8*ε) • P := by
    have hs := smul_le_smul_of_nonneg_left hPfloor (show 0 ≤ 8*ε by positivity)
    have hc : (8*ε)*(8*H) = 64*h := by rw [hscale]; ring
    simpa [smul_smul, hc] using hs
  have hsubJ : (64*h) • D ≤ Fs - Kj :=
    hηP.trans (idealMetric_sub_margin Rp Kj hRp hKj (8*ε))
  have haddJ : (64*h) • D ≤ Fs + Kj :=
    hηP.trans (idealMetric_add_margin Rp Kj hRp hKj (8*ε))
  have hsub : (56*h) • D ≤ Fs-K := by
    have hs := add_le_add hsubJ hlow
    convert hs using 1 <;> module
  have hadd : (56*h) • D ≤ Fs+K := by
    have hs := add_le_add haddJ (neg_le_neg hupper)
    convert hs using 1 <;> module
  have hconstants := inflated_constant_bounds C κ ε hC hκ hκ' hε.le hε'
  have hcoarse := inflated_coarse_invariant (inverseMetric R) K Kj D κ C h H ε
    hFprev hD hK hKj hκ hh hH hε hscale hfloor hlow hupper hinvariant
  rw [← hP] at hcoarse
  have hcoarse' : P - (κ*(1+ε)^3) • (Kj * P⁻¹ * Kj) ≤ (2*(C+1)*H) • D :=
    hcoarse.trans (smul_le_smul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconstants.2.1 hH.le) hD.posSemidef.nonneg)
  have hsmall : 2*(8*ε)*(κ*(1+ε)^3)*(5/4) ≤ (1:ℝ) := by
    have hs := mul_le_mul_of_nonneg_left hconstants.2.2 hε.le
    nlinarith
  have hroot : Fs - Kj * Fs⁻¹ * Kj = (2*(8*ε)) • P :=
    idealMetric_defect Rp Kj hRp hKj (8*ε) (by positivity)
  have herr := fine_error_ideal_metric D Fs (Kj-K) h hD
    (by simp [hKj, hK]) hh hlow hupper hFsFloor
  have hrelax := ideal_refinement_relaxation P Fs K Kj (Kj-K) D
    (8*ε) (κ*(1+ε)^3) (2*(C+1)) H h hPpos hFs hD.posSemidef hK hKj rfl
    (by positivity) (by positivity) (by rw [hscale]; ring) hsmall hcoarse' hFsP hroot herr
  refine ⟨hFs, hFsFloor, hFsBound, hsub, hadd, ?_⟩
  convert hrelax using 1
  congr 1
  ring

end
end HierarchicalAbsoluteSpectral
