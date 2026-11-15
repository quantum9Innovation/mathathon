import HierarchicalAbsoluteSpectral.NeumannMass
import HierarchicalAbsoluteSpectral.NeumannDegree
import HierarchicalAbsoluteSpectral.MatrixInequalities

/-! The fine inverse-mass and pencil error estimates from Section 3. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {k : ℕ}

theorem posDef_of_half_identity_le (G : Core k) (hG : (1/2:ℝ) • (1 : Core k) ≤ G) :
    G.PosDef := by
  have hp : ((1/2:ℝ) • (1 : Core k)).PosDef := Matrix.PosDef.one.smul (by norm_num)
  simpa using hp.add_posSemidef (show (G-(1/2:ℝ) • (1 : Core k)).PosSemidef from hG)

theorem inverse_le_two_of_half_identity_le (G : Core k)
    (hG : (1/2:ℝ) • (1 : Core k) ≤ G) : G⁻¹ ≤ (2:ℝ) • (1 : Core k) := by
  letI : Invertible (1/2:ℝ) := invertibleOfNonzero (by norm_num)
  have hp : ((1/2:ℝ) • (1 : Core k)).PosDef := Matrix.PosDef.one.smul (by norm_num)
  have hi := inverse_order hp hG
  rw [Matrix.inv_smul _ _ (by simp), invOf_eq_inv] at hi
  norm_num at hi
  exact hi

theorem fine_inverse_coefficients (h ef em : ℝ) (hh : 0 < h) (hh' : h ≤ 1/64)
    (hef : 0 ≤ ef) (hef' : ef ≤ h/100) (_hem : 0 ≤ em) (hem' : em ≤ h/100) :
    (1+ef)/(1-h)-(1-em) ≤ 2*h ∧ (1+em)-(1-ef)/(1+h) ≤ 2*h := by
  have hm : 0 < 1-h := by linarith
  have hp : 0 < 1+h := by linarith
  have hs := mul_le_mul_of_nonneg_right hh' hh.le
  have hupper : (1+ef)/(1-h) ≤ 1+3*h/2 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith
  have hlower : 1-ef-h ≤ (1-ef)/(1+h) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith [mul_nonneg hh.le hef]
  constructor <;> linarith

theorem inverse_mass_perturbation (G Gj B N : Core k) (h ef em : ℝ)
    (hG : G.PosDef) (hGj : Gj.PosDef) (hh : 0 < h) (hh' : h ≤ 1/64)
    (hef : 0 ≤ ef) (hef' : ef ≤ h/100) (hem : 0 ≤ em) (hem' : em ≤ h/100)
    (hGlo : (1-h) • G ≤ Gj) (hGup : Gj ≤ (1+h) • G)
    (hNlo : (1-ef) • Gj⁻¹ ≤ N) (hNup : N ≤ (1+ef) • Gj⁻¹)
    (hBlo : (1-em) • G⁻¹ ≤ B) (hBup : B ≤ (1+em) • G⁻¹)
    (hGinv : G⁻¹ ≤ (2:ℝ) • (1 : Core k)) :
    -((4*h) • (1 : Core k)) ≤ N-B ∧ N-B ≤ (4*h) • (1 : Core k) := by
  have hm : 0 < 1-h := by linarith
  have hp : 0 < 1+h := by linarith
  letI : Invertible (1-h) := invertibleOfNonzero hm.ne'
  letI : Invertible (1+h) := invertibleOfNonzero hp.ne'
  have hilo := inverse_order hGj hGup
  have hiup := inverse_order (hG.smul hm) hGlo
  rw [Matrix.inv_smul _ _ ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit), invOf_eq_inv] at hilo hiup
  have hnlo : ((1-ef)/(1+h)) • G⁻¹ ≤ N := by
    have hs := (smul_le_smul_of_nonneg_left hilo (by linarith : 0 ≤ 1-ef)).trans hNlo
    simpa only [smul_smul, div_eq_mul_inv] using hs
  have hnup : N ≤ ((1+ef)/(1-h)) • G⁻¹ := by
    have hs := hNup.trans (smul_le_smul_of_nonneg_left hiup (by positivity : 0 ≤ 1+ef))
    simpa only [smul_smul, div_eq_mul_inv] using hs
  have hcoeff := fine_inverse_coefficients h ef em hh hh' hef hef' hem hem'
  have hmass : (2*h) • G⁻¹ ≤ (4*h) • (1 : Core k) := by
    convert smul_le_smul_of_nonneg_left hGinv (show 0 ≤ 2*h by positivity) using 1; module
  have hup : N-B ≤ (4*h) • (1 : Core k) := by
    have hd : N-B ≤ ((1+ef)/(1-h)-(1-em)) • G⁻¹ := by
      convert sub_le_sub hnup hBlo using 1; module
    exact hd.trans ((smul_le_smul_of_nonneg_right hcoeff.1 hG.inv.posSemidef.nonneg).trans hmass)
  have hlo : B-N ≤ (4*h) • (1 : Core k) := by
    have hd : B-N ≤ ((1+em)-(1-ef)/(1+h)) • G⁻¹ := by
      convert sub_le_sub hBup hnlo using 1; module
    exact hd.trans ((smul_le_smul_of_nonneg_right hcoeff.2 hG.inv.posSemidef.nonneg).trans hmass)
  refine ⟨?_, hup⟩
  convert neg_le_neg hlo using 1; module

theorem fine_pencil_error (B N Q Qj Q0 : Core k) (h t : ℝ)
    (hh : 0 ≤ h) (ht : 0 ≤ t) (hQ0 : Q0.PosSemidef)
    (hmlo : -((4*h) • (1 : Core k)) ≤ N-B) (hmup : N-B ≤ (4*h) • (1 : Core k))
    (hQ : Q ≤ (2:ℝ) • Q0) (hQlo : -(h • Q) ≤ Qj-Q) (hQup : Qj-Q ≤ h • Q) :
    -((8*h) • (t • (1 : Core k)+Q0)) ≤ (t • N-Qj)-(t • B-Q) ∧
      (t • N-Qj)-(t • B-Q) ≤ (8*h) • (t • (1 : Core k)+Q0) := by
  have hright : h • Q ≤ (2*h) • Q0 := by
    convert smul_le_smul_of_nonneg_left hQ hh using 1; module
  have hl : -((2*h) • Q0) ≤ Qj-Q := (neg_le_neg hright).trans hQlo
  have hu : Qj-Q ≤ (2*h) • Q0 := hQup.trans hright
  have hbudget : (4*h*t) • (1 : Core k)+(2*h) • Q0 ≤
      (8*h) • (t • (1 : Core k)+Q0) := by
    have hi := smul_le_smul_of_nonneg_right
      (show 4*h*t ≤ 8*h*t by nlinarith) (Matrix.PosSemidef.one : (1 : Core k).PosSemidef).nonneg
    have hq := smul_le_smul_of_nonneg_right (show 2*h ≤ 8*h by linarith) hQ0.nonneg
    convert add_le_add hi hq using 1; module
  have hup : (t • N-Qj)-(t • B-Q) ≤
      (4*h*t) • (1 : Core k)+(2*h) • Q0 := by
    convert sub_le_sub (smul_le_smul_of_nonneg_left hmup ht) hl using 1 <;> module
  have hlo : (t • B-Q)-(t • N-Qj) ≤
      (4*h*t) • (1 : Core k)+(2*h) • Q0 := by
    have hm : B-N ≤ (4*h) • (1 : Core k) := by
      simpa only [neg_sub, neg_neg] using neg_le_neg hmlo
    convert add_le_add (smul_le_smul_of_nonneg_left hm ht) hu using 1 <;> module
  refine ⟨?_, hup.trans hbudget⟩
  convert neg_le_neg (hlo.trans hbudget) using 1; module

def trueNeumannPencil (G Q : Core k) (t ε : ℝ) (hε : 0 < ε) : Core k :=
  t • constructedNeumannMass G ε hε-Q

def fineNeumannPencil (Gj Qj : Core k) (t h : ℝ) (hh : 0 < h) : Core k :=
  t • constructedNeumannMass Gj (h/100) (by positivity)-Qj

/-- The actual two Neumann polynomials satisfy the proxy error (8).
The hypotheses are the Gram/sketch estimates, rather than an assumed
inverse-mass or pencil approximation certificate. -/
theorem constructed_fine_pencil_error (G Gj Q Qj Q0 : Core k) (h t ε : ℝ)
    (hh : 0 < h) (hh' : h ≤ 1/64)
    (hε : 0 < ε) (hε' : ε ≤ h/100) (ht : 0 ≤ t) (hQ0 : Q0.PosSemidef)
    (hGfloor : (1/2:ℝ) • (1 : Core k) ≤ G) (hGceil : G ≤ (3/2:ℝ) • (1 : Core k))
    (hGjfloor : (1/2:ℝ) • (1 : Core k) ≤ Gj) (hGjceil : Gj ≤ (3/2:ℝ) • (1 : Core k))
    (hGlo : (1-h) • G ≤ Gj) (hGup : Gj ≤ (1+h) • G)
    (hQ : Q ≤ (2:ℝ) • Q0) (hQlo : (1-h) • Q ≤ Qj) (hQup : Qj ≤ (1+h) • Q) :
    -((8*h) • (t • (1 : Core k)+Q0)) ≤ fineNeumannPencil Gj Qj t h hh-trueNeumannPencil G Q t ε hε ∧
      fineNeumannPencil Gj Qj t h hh-trueNeumannPencil G Q t ε hε ≤
        (8*h) • (t • (1 : Core k)+Q0) := by
  have hG := posDef_of_half_identity_le G hGfloor
  have hGj := posDef_of_half_identity_le Gj hGjfloor
  have hGinv := inverse_le_two_of_half_identity_le G hGfloor
  have hb := constructedNeumannMass_relative G hG ε hε hGfloor hGceil
  have hn := constructedNeumannMass_relative Gj hGj (h/100) (by positivity) hGjfloor hGjceil
  have hm := inverse_mass_perturbation G Gj (constructedNeumannMass G ε hε)
    (constructedNeumannMass Gj (h/100) (by positivity)) h (h/100) ε hG hGj hh hh'
    (by positivity) (le_refl _) hε.le hε' hGlo hGup hn.1 hn.2 hb.1 hb.2 hGinv
  apply fine_pencil_error _ _ Q Qj Q0 h t hh.le ht hQ0 hm.1 hm.2 hQ
  · convert sub_le_sub_right hQlo Q using 1; module
  · convert sub_le_sub_right hQup Q using 1; module

end
end HierarchicalAbsoluteSpectral
