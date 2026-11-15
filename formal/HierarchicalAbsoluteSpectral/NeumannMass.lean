import HierarchicalAbsoluteSpectral.IdealMetric
import Mathlib.Algebra.Order.Ring.GeomSum

/-! Even finite Neumann polynomials for the true and fine inverse masses.
Even degree gives positivity on every symmetric input; relative inverse
accuracy additionally uses spectral proximity to the identity. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Polynomial Matrix
open scoped MatrixOrder
variable {k : ℕ}

def evenNeumannPolynomial (q : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (2*q+1), (1-X)^i

def evenNeumannMass (G : Core k) (q : ℕ) : Core k := aeval G (evenNeumannPolynomial q)

theorem evenNeumannPolynomial_eval (q : ℕ) (x : ℝ) :
    (evenNeumannPolynomial q).eval x = ∑ i ∈ Finset.range (2*q+1), (1-x)^i := by
  simp only [evenNeumannPolynomial, eval_finsetSum, eval_pow, eval_sub, eval_one, eval_X]

theorem evenNeumannPolynomial_pos (q : ℕ) (x : ℝ) : 0 < (evenNeumannPolynomial q).eval x := by
  rw [evenNeumannPolynomial_eval]
  exact (show Odd (2*q+1) from ⟨q, rfl⟩).geom_sum_pos

theorem evenNeumannPolynomial_identity (q : ℕ) (x : ℝ) :
    (evenNeumannPolynomial q).eval x*x = 1-(1-x)^(2*q+1) := by
  have h := geom_sum_mul_neg (1-x) (2*q+1)
  simpa only [sub_sub_cancel, evenNeumannPolynomial_eval] using h

theorem evenNeumannPolynomial_relative (q : ℕ) (x b ε : ℝ)
    (hx : 0 < x) (_hb : 0 ≤ b) (hclose : |1-x| ≤ b) (hdegree : b^(2*q+1) ≤ ε) :
    (1-ε)*x⁻¹ ≤ (evenNeumannPolynomial q).eval x ∧
      (evenNeumannPolynomial q).eval x ≤ (1+ε)*x⁻¹ := by
  have hpow := pow_le_pow_left₀ (abs_nonneg (1-x)) hclose (2*q+1)
  have he : |(evenNeumannPolynomial q).eval x*x-1| ≤ ε := by
    rw [evenNeumannPolynomial_identity]
    have heq : 1-(1-x)^(2*q+1)-1 = -(1-x)^(2*q+1) := by ring
    rw [heq, abs_neg, abs_pow]
    exact hpow.trans hdegree
  have hlo := (abs_le.mp he).1
  have hup := (abs_le.mp he).2
  constructor
  · apply (mul_le_mul_iff_left₀ hx).mp
    rw [mul_assoc, inv_mul_cancel₀ hx.ne', mul_one]
    linarith
  · apply (mul_le_mul_iff_left₀ hx).mp
    rw [mul_assoc, inv_mul_cancel₀ hx.ne', mul_one]
    linarith

theorem evenNeumannMass_eq_sum (G : Core k) (q : ℕ) :
    evenNeumannMass G q = ∑ i ∈ Finset.range (2*q+1), (1-G)^i := by
  simp only [evenNeumannMass, evenNeumannPolynomial, map_sum, map_pow, map_sub,
    map_one, aeval_X]

theorem evenNeumannMass_posDef (G : Core k) (hG : G.IsHermitian) (q : ℕ) :
    (evenNeumannMass G q).PosDef := by
  apply Matrix.IsStrictlyPositive.posDef
  rw [evenNeumannMass, ← cfc_polynomial (evenNeumannPolynomial q) G hG]
  exact (cfc_isStrictlyPositive_iff (p := IsSelfAdjoint) (evenNeumannPolynomial q).eval G
    (finite_spectrum_continuous G _) hG).mpr (fun x _ => evenNeumannPolynomial_pos q x)

theorem evenNeumannMass_relative (G : Core k) (hG : G.PosDef) (q : ℕ) (b ε : ℝ)
    (hb : 0 ≤ b) (hspec : ∀ x ∈ spectrum ℝ G, |1-x| ≤ b) (hdegree : b^(2*q+1) ≤ ε) :
    (1-ε) • G⁻¹ ≤ evenNeumannMass G q ∧ evenNeumannMass G q ≤ (1+ε) • G⁻¹ := by
  have hx (x : ℝ) (hx : x ∈ spectrum ℝ G) : 0 < x := hG.isStrictlyPositive.spectrum_pos hx
  have hid : cfc (p := IsSelfAdjoint) (fun x : ℝ => x) G = G :=
    cfc_id' (p := IsSelfAdjoint) ℝ G hG.isHermitian
  have hi : cfc (p := IsSelfAdjoint) (fun x : ℝ => x⁻¹) G = G⁻¹ := by
    simpa only [hid, Matrix.nonsing_inv_eq_ringInverse] using
      cfc_inv (p := IsSelfAdjoint) (fun x : ℝ => x) G
        (fun x h => (hx x h).ne') (finite_spectrum_continuous G _) hG.isHermitian
  have hp : cfc (p := IsSelfAdjoint) (evenNeumannPolynomial q).eval G = evenNeumannMass G q :=
    cfc_polynomial _ G hG.isHermitian
  have hlo := cfc_mono (p := IsSelfAdjoint) (a := G)
    (fun x h => (evenNeumannPolynomial_relative q x b ε (hx x h) hb (hspec x h) hdegree).1)
    (finite_spectrum_continuous G _) (finite_spectrum_continuous G _)
  have hup := cfc_mono (p := IsSelfAdjoint) (a := G)
    (fun x h => (evenNeumannPolynomial_relative q x b ε (hx x h) hb (hspec x h) hdegree).2)
    (finite_spectrum_continuous G _) (finite_spectrum_continuous G _)
  rw [hp, cfc_const_mul (p := IsSelfAdjoint) _ _ G (finite_spectrum_continuous G _), hi] at hlo hup
  exact ⟨hlo, hup⟩

theorem spectrum_close_to_one_of_bounds (G : Core k) (hG : G.IsHermitian) (b : ℝ)
    (hlo : (1-b) • (1 : Core k) ≤ G) (hup : G ≤ (1+b) • (1 : Core k)) :
    ∀ x ∈ spectrum ℝ G, |1-x| ≤ b := by
  have hl : algebraMap ℝ (Core k) (1-b) ≤ G := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hlo
  have hu : G ≤ algebraMap ℝ (Core k) (1+b) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hup
  have hslo := (algebraMap_le_iff_le_spectrum (p := IsSelfAdjoint) hG).mp hl
  have hsup := (le_algebraMap_iff_spectrum_le (p := IsSelfAdjoint) hG).mp hu
  intro x hx
  exact abs_le.mpr ⟨by linarith [hsup x hx], by linarith [hslo x hx]⟩

theorem evenNeumannMass_relative_of_bounds (G : Core k) (hG : G.PosDef)
    (q : ℕ) (b ε : ℝ) (hb : 0 ≤ b)
    (hlo : (1-b) • (1 : Core k) ≤ G) (hup : G ≤ (1+b) • (1 : Core k))
    (hdegree : b^(2*q+1) ≤ ε) :
    (1-ε) • G⁻¹ ≤ evenNeumannMass G q ∧ evenNeumannMass G q ≤ (1+ε) • G⁻¹ :=
  evenNeumannMass_relative G hG q b ε hb
    (spectrum_close_to_one_of_bounds G hG.isHermitian b hlo hup) hdegree

end
end HierarchicalAbsoluteSpectral
