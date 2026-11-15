import HierarchicalAbsoluteSpectral.PolynomialDegreeLowerBernsteinAffine
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Polynomial.Roots

namespace HierarchicalAbsoluteSpectral

open Polynomial Set

noncomputable section

/-- The odd part preserves the derivative at the origin. -/
def centralOddPart (p : ℝ[X]) : ℝ[X] :=
  C (1 / 2) * (p - p.comp (-X))

theorem centralOddPart_coeff (p : ℝ[X]) (k : ℕ) :
    (centralOddPart p).coeff k =
      (1 / 2 : ℝ) * (p.coeff k - p.coeff k * (-1 : ℝ) ^ k) := by
  have hneg : (-X : ℝ[X]) = C (-1) * X := by simp
  unfold centralOddPart
  rw [coeff_C_mul, coeff_sub, hneg, comp_C_mul_X_coeff]

@[simp] theorem centralOddPart_eval_zero (p : ℝ[X]) :
    (centralOddPart p).eval 0 = 0 := by
  simp [centralOddPart]

@[simp] theorem centralOddPart_derivative_eval_zero (p : ℝ[X]) :
    (centralOddPart p).derivative.eval 0 = p.derivative.eval 0 := by
  simp [centralOddPart, derivative_comp]
  ring

theorem centralOddPart_bound (p : ℝ[X]) (M : ℝ)
    (hp : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    ∀ x ∈ Icc (-1 : ℝ) 1, |(centralOddPart p).eval x| ≤ M := by
  intro x hx
  have hxneg : -x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hxp := hp x hx
  have hxn := hp (-x) hxneg
  have hsub := abs_sub (p.eval x) (p.eval (-x))
  simp only [centralOddPart, eval_mul, eval_C, eval_sub, eval_comp, eval_neg, eval_X]
  rw [abs_mul]
  norm_num
  nlinarith

/-- Odd projection removes a possible top coefficient of even degree. -/
theorem centralOddPart_natDegree_le (p : ℝ[X]) (d : ℕ)
    (hdeg : p.natDegree ≤ 2 * d + 2) :
    (centralOddPart p).natDegree ≤ 2 * d + 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [centralOddPart_coeff]
  by_cases hpk : p.natDegree < k
  · rw [coeff_eq_zero_of_natDegree_lt hpk]
    ring
  · have hk' : k = 2 * d + 2 := by omega
    subst k
    have heven : Even (2 * d + 2) := ⟨d + 1, by omega⟩
    rw [heven.neg_one_pow]
    ring

/-- The odd-degree central estimate implies the central estimate for an
arbitrary real polynomial and any uniform bound. -/
theorem central_derivative_bound_of_odd
    (hodd : ∀ (q : ℝ[X]) (d : ℕ),
      q.natDegree ≤ 2 * d + 1 → q.eval 0 = 0 →
      (∀ x ∈ Icc (-1 : ℝ) 1, |q.eval x| ≤ 1) →
        |q.derivative.eval 0| ≤ (2 * d + 1 : ℕ))
    (p : ℝ[X]) (M : ℝ)
    (hp : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    |p.derivative.eval 0| ≤ p.natDegree * M := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hp 0 (by norm_num))
  by_cases hMzero : M = 0
  · have hpzero : p = 0 := by
      apply p.eq_zero_of_infinite_isRoot
      apply (Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono
      intro x hx
      change p.eval x = 0
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa [hMzero] using hp x hx) (abs_nonneg _)
    simp [hpzero]
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
  by_cases hdegzero : p.natDegree = 0
  · simp [derivative_of_natDegree_zero hdegzero, hdegzero]
  let d : ℕ := (p.natDegree - 1) / 2
  have hdle : 2 * d + 1 ≤ p.natDegree := by dsimp [d]; omega
  have hdeg : p.natDegree ≤ 2 * d + 2 := by dsimp [d]; omega
  let q : ℝ[X] := C M⁻¹ * centralOddPart p
  have hqdeg : q.natDegree ≤ 2 * d + 1 := by
    exact (natDegree_C_mul_le M⁻¹ (centralOddPart p)).trans
      (centralOddPart_natDegree_le p d hdeg)
  have hqzero : q.eval 0 = 0 := by simp [q]
  have hqbnd : ∀ x ∈ Icc (-1 : ℝ) 1, |q.eval x| ≤ 1 := by
    intro x hx
    have ho := centralOddPart_bound p M hp x hx
    simp only [q, eval_mul, eval_C, abs_mul, abs_inv, abs_of_pos hMpos]
    exact (inv_mul_le_iff₀ hMpos).mpr (by simpa using ho)
  have hc := hodd q d hqdeg hqzero hqbnd
  have hqder : q.derivative.eval 0 = M⁻¹ * p.derivative.eval 0 := by
    simp [q, derivative_mul]
  rw [hqder, abs_mul, abs_inv, abs_of_pos hMpos] at hc
  have hc' : |p.derivative.eval 0| ≤ (2 * d + 1 : ℕ) * M := by
    simpa only [mul_comm] using (inv_mul_le_iff₀ hMpos).mp hc
  exact hc'.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hdle) hM)

end

end HierarchicalAbsoluteSpectral
