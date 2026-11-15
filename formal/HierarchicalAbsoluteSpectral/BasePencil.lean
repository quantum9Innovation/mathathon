import HierarchicalAbsoluteSpectral.BaseFinite
import HierarchicalAbsoluteSpectral.FineProxy

/-! Derive the base pencil hypotheses from the actual Neumann mass and
coarse Gram/sketch estimates. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {k : ℕ}

theorem base_mass_error (G B : Core k) (h ε : ℝ) (hh : 0 < h) (hh' : h ≤ 1/64)
    (hε : 0 ≤ ε) (hε' : ε ≤ h/100) (_hG : G.PosDef)
    (hilo : (1-h) • (1 : Core k) ≤ G⁻¹) (hiup : G⁻¹ ≤ (1+h) • (1 : Core k))
    (hblo : (1-ε) • G⁻¹ ≤ B) (hbup : B ≤ (1+ε) • G⁻¹) :
    -((2*h) • (1 : Core k)) ≤ B-1 ∧ B-1 ≤ (2*h) • (1 : Core k) := by
  have hl := (smul_le_smul_of_nonneg_left hilo (show 0 ≤ 1-ε by linarith)).trans hblo
  have hu := hbup.trans (smul_le_smul_of_nonneg_left hiup (show 0 ≤ 1+ε by positivity))
  have hcoefflo : 1-2*h ≤ (1-ε)*(1-h) := by nlinarith
  have hcoeffup : (1+ε)*(1+h) ≤ 1+2*h := by
    have hhh := mul_le_mul_of_nonneg_right hh' hh.le
    nlinarith
  have hlo : (1-2*h) • (1 : Core k) ≤ B := by
    apply (smul_le_smul_of_nonneg_right hcoefflo (Matrix.PosSemidef.one : (1 : Core k).PosSemidef).nonneg).trans
    simpa only [smul_smul] using hl
  have hup : B ≤ (1+2*h) • (1 : Core k) := by
    apply (show B ≤ ((1+ε)*(1+h)) • (1 : Core k) by simpa only [smul_smul] using hu).trans
    exact smul_le_smul_of_nonneg_right hcoeffup (Matrix.PosSemidef.one : (1 : Core k).PosSemidef).nonneg
  constructor
  · convert sub_le_sub_right hlo (1 : Core k) using 1; module
  · convert sub_le_sub_right hup (1 : Core k) using 1; module

theorem base_coarse_right_error (Q Q0 : Core k) (h : ℝ) (hh : 0 ≤ h) (hh' : h ≤ 1/64)
    (hQ : Q.PosSemidef) (hlo : (1-h) • Q ≤ Q0) (hup : Q0 ≤ (1+h) • Q) :
    -((2*h) • Q0) ≤ Q-Q0 ∧ Q-Q0 ≤ (2*h) • Q0 := by
  have hQupper : Q ≤ (2:ℝ) • Q0 := by
    have hco : 1 ≤ 2*(1-h) := by linarith
    have hc := smul_le_smul_of_nonneg_right hco hQ.nonneg
    have hs := smul_le_smul_of_nonneg_left hlo (by norm_num : (0:ℝ) ≤ 2)
    have hc' : Q ≤ (2*(1-h)) • Q := by simpa only [one_smul] using hc
    exact hc'.trans (by simpa only [smul_smul] using hs)
  have hbudget : h • Q ≤ (2*h) • Q0 := by
    convert smul_le_smul_of_nonneg_left hQupper hh using 1 <;> module
  have hl : -(h • Q) ≤ Q-Q0 := by convert sub_le_sub_left hup Q using 1 <;> module
  have hu : Q-Q0 ≤ h • Q := by convert sub_le_sub_left hlo Q using 1 <;> module
  exact ⟨(neg_le_neg hbudget).trans hl, hu.trans hbudget⟩

theorem base_pencil_error (B Q Q0 : Core k) (h t : ℝ) (ht : 0 ≤ t)
    (hmlo : -((2*h) • (1 : Core k)) ≤ B-1) (hmup : B-1 ≤ (2*h) • (1 : Core k))
    (hqlo : -((2*h) • Q0) ≤ Q-Q0) (hqup : Q-Q0 ≤ (2*h) • Q0) :
    -((2*h) • (t • (1 : Core k)+Q0)) ≤ (t • B-Q)-(t • (1 : Core k)-Q0) ∧
      (t • B-Q)-(t • (1 : Core k)-Q0) ≤ (2*h) • (t • (1 : Core k)+Q0) := by
  constructor
  · convert sub_le_sub (smul_le_smul_of_nonneg_left hmlo ht) hqup using 1 <;> module
  · convert sub_le_sub (smul_le_smul_of_nonneg_left hmup ht) hqlo using 1 <;> module

theorem base_pencil_bands (Q0 : Core k) (t : ℝ) (ht : 0 ≤ t) (hQ0 : Q0.PosSemidef) :
    -(t • (1 : Core k)+Q0) ≤ t • (1 : Core k)-Q0 ∧
      t • (1 : Core k)-Q0 ≤ t • (1 : Core k)+Q0 := by
  constructor
  · change ((t • (1 : Core k)-Q0)-(-(t • (1 : Core k)+Q0))).PosSemidef
    convert (Matrix.PosSemidef.one : (1 : Core k).PosSemidef).smul (show 0 ≤ 2*t by positivity) using 1; module
  · change ((t • (1 : Core k)+Q0)-(t • (1 : Core k)-Q0)).PosSemidef
    convert hQ0.smul (show (0:ℝ) ≤ 2 by norm_num) using 1; module

theorem coarse_gram_inverse_bands (G : Core k) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/64)
    (hlo : (1/(1+h)) • (1 : Core k) ≤ G) (hup : G ≤ (1/(1-h)) • (1 : Core k)) :
    G.PosDef ∧ (1/2:ℝ) • (1 : Core k) ≤ G ∧ G ≤ (3/2:ℝ) • (1 : Core k) ∧
      (1-h) • (1 : Core k) ≤ G⁻¹ ∧ G⁻¹ ≤ (1+h) • (1 : Core k) := by
  have hm : 0 < 1-h := by linarith
  have hp : 0 < 1+h := by positivity
  have hhalf : (1/2:ℝ) ≤ 1/(1+h) := by apply (le_div_iff₀ hp).mpr; linarith
  have hthree : 1/(1-h) ≤ (3/2:ℝ) := by apply (div_le_iff₀ hm).mpr; linarith
  have hfloor := (smul_le_smul_of_nonneg_right hhalf (Matrix.PosSemidef.one : (1 : Core k).PosSemidef).nonneg).trans hlo
  have hceil := hup.trans (smul_le_smul_of_nonneg_right hthree (Matrix.PosSemidef.one : (1 : Core k).PosSemidef).nonneg)
  have hG := posDef_of_half_identity_le G hfloor
  have hs : ((1/(1+h)) • (1 : Core k)).PosDef := Matrix.PosDef.one.smul (by positivity)
  letI : Invertible (1/(1+h)) := invertibleOfNonzero (by positivity)
  letI : Invertible (1/(1-h)) := invertibleOfNonzero (by positivity)
  have hil := inverse_order hG hup
  have hiu := inverse_order hs hlo
  rw [Matrix.inv_smul _ _ (by simp), invOf_eq_inv, inv_one] at hil hiu
  simp only [one_div, inv_inv] at hil hiu
  exact ⟨hG, hfloor, hceil, hil, hiu⟩

theorem constructed_base_pencil_error (G Q Q0 : Core k) (h ε t : ℝ)
    (hh : 0 < h) (hh' : h ≤ 1/64) (hε : 0 < ε) (hε' : ε ≤ h/100) (ht : 0 ≤ t)
    (hQ : Q.PosSemidef)
    (hGlo : (1/(1+h)) • (1 : Core k) ≤ G) (hGup : G ≤ (1/(1-h)) • (1 : Core k))
    (hQlo : (1-h) • Q ≤ Q0) (hQup : Q0 ≤ (1+h) • Q) :
    -((2*h) • (t • (1 : Core k)+Q0)) ≤ trueNeumannPencil G Q t ε hε-(t • (1 : Core k)-Q0) ∧
      trueNeumannPencil G Q t ε hε-(t • (1 : Core k)-Q0) ≤ (2*h) • (t • (1 : Core k)+Q0) := by
  have hg := coarse_gram_inverse_bands G h hh hh' hGlo hGup
  have hb := constructedNeumannMass_relative G hg.1 ε hε hg.2.1 hg.2.2.1
  have hm := base_mass_error G (constructedNeumannMass G ε hε) h ε hh hh' hε.le hε'
    hg.1 hg.2.2.2.1 hg.2.2.2.2 hb.1 hb.2
  have hq := base_coarse_right_error Q Q0 h hh.le hh' hQ hQlo hQup
  exact base_pencil_error _ Q Q0 h t ht hm.1 hm.2 hq.1 hq.2

end
end HierarchicalAbsoluteSpectral
