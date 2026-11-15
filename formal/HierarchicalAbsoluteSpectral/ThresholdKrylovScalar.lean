import HierarchicalAbsoluteSpectral.StrongFilterScalar

/-! Proof-only scaled Chebyshev polynomial witnessing the additive Krylov
Ritz guarantee. The algorithm stores all powers and never evaluates the
unknown target eigenvalue used in this witness. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Polynomial

theorem strongFilterPolynomial_natDegree_le (α : ℝ) (q : ℕ) :
    (strongFilterPolynomial α q).natDegree ≤ q := by
  have ha : (C (2/(1+α))*X-1 : ℝ[X]).natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simpa using natDegree_C_mul_le (2/(1+α)) (X : ℝ[X])
    · simp
  have hc : ((Polynomial.Chebyshev.T ℝ (q:ℤ)).comp
      (C (2/(1+α))*X-1)).natDegree ≤ q := by
    calc
      _ ≤ (Polynomial.Chebyshev.T ℝ (q:ℤ)).natDegree*
          (C (2/(1+α))*X-1 : ℝ[X]).natDegree := natDegree_comp_le
      _ ≤ q*1 := by simpa only [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast] using Nat.mul_le_mul_left q ha
      _ = q := Nat.mul_one _
  exact natDegree_mul_le.trans (by simpa only [natDegree_C, zero_add] using hc)

def ritzFilterPolynomial (ε target : ℝ) (q : ℕ) : ℝ[X] :=
  (strongFilterPolynomial (ε/100) q).comp (C ((1+2*(ε/100))/target)*X)

theorem ritzFilterPolynomial_eval (ε target : ℝ) (q : ℕ) (x : ℝ) :
    (ritzFilterPolynomial ε target q).eval x =
      (strongFilterPolynomial (ε/100) q).eval (((1+2*(ε/100))*x)/target) := by
  simp only [ritzFilterPolynomial, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  congr 1
  ring

theorem ritzFilterPolynomial_natDegree_le (ε target : ℝ) (q : ℕ) :
    (ritzFilterPolynomial ε target q).natDegree ≤ q := by
  calc
    _ ≤ (strongFilterPolynomial (ε/100) q).natDegree*
        (C ((1+2*(ε/100))/target)*X : ℝ[X]).natDegree := natDegree_comp_le
    _ ≤ q*1 := Nat.mul_le_mul (strongFilterPolynomial_natDegree_le _ _)
      (by simpa using natDegree_C_mul_le ((1+2*(ε/100))/target) (X : ℝ[X]))
    _ = q := Nat.mul_one _

theorem ritzFilterPolynomial_head (ε target : ℝ) (q : ℕ)
    (hε : 0 < ε) (htarget : 0 < target) (x : ℝ) (hx : target ≤ x) :
    1 ≤ (ritzFilterPolynomial ε target q).eval x := by
  rw [ritzFilterPolynomial_eval]
  apply strongFilter_strong_ge_one (ε/100) (by positivity)
  apply (le_div_iff₀ htarget).mpr
  nlinarith

theorem ritzFilterPolynomial_tail (ε target : ℝ) (q : ℕ)
    (hε : 0 < ε) (htarget : 0 < target) (x : ℝ) (hx : 0 ≤ x)
    (hweak : (1+2*(ε/100))*x ≤ (1+ε/100)*target) :
    |(ritzFilterPolynomial ε target q).eval x| ≤ 1/strongFilterDenominator (ε/100) q := by
  rw [ritzFilterPolynomial_eval]
  apply strongFilter_tail_bound (ε/100) (by positivity)
  · positivity
  · exact (div_le_iff₀ htarget).mpr hweak

theorem ritzFilterPolynomial_middle (ε target x : ℝ)
    (hε : 0 < ε) (hε' : ε ≤ 1) (htarget : 0 ≤ target) (hx : 0 ≤ x)
    (hweak : ¬(1+2*(ε/100))*x ≤ (1+ε/100)*target) :
    (1-ε)*target^2 ≤ x^2 := by
  have hd : 0 < 1+2*(ε/100) := by positivity
  have hr : 1-ε/2 ≤ (1+ε/100)/(1+2*(ε/100)) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have hx' : ((1+ε/100)/(1+2*(ε/100)))*target ≤ x := by
    have hn : (1+ε/100)*target < x*(1+2*(ε/100)) := by
      have hh := lt_of_not_ge hweak
      nlinarith
    have hh := (div_lt_iff₀ hd).mpr hn
    calc
      _ = ((1+ε/100)*target)/(1+2*(ε/100)) := by ring
      _ ≤ x := hh.le
  have hr' : (1-ε/2)*target ≤ x :=
    (mul_le_mul_of_nonneg_right hr htarget).trans hx'
  have hs : ((1-ε/2)*target)^2 ≤ x^2 :=
    (sq_le_sq₀ (mul_nonneg (by linarith) htarget) hx).mpr hr'
  nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg target)]

end
end HierarchicalAbsoluteSpectral
