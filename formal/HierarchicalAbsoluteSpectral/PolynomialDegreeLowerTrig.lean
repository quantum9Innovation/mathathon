import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- A polynomial with strict alternating signs at all Chebyshev extrema has at least
as large a degree. This is the leading-coefficient form of Lagrange interpolation. -/
theorem chebyshev_alternation_natDegree_le {N : ℕ} (s : ℝ[X])
    (hpos : ∀ i ≤ N, 0 < (-1 : ℝ) ^ i * s.eval (node N i)) :
    N ≤ s.natDegree := by
  by_contra h
  have hs : s.natDegree < N := by omega
  have hsdeg : s.degree < (Finset.range (N + 1)).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt (degree_le_natDegree) (by exact_mod_cast (by omega : s.natDegree < N + 1))
  have hinterp := Lagrange.coeff_eq_sum (strictAntiOn_node N).injOn hsdeg
  simp only [Finset.card_range, Nat.add_sub_cancel] at hinterp
  have hzero : s.coeff N = 0 := coeff_eq_zero_of_natDegree_lt hs
  have hsum : 0 < ∑ i ∈ Finset.range (N + 1),
      s.eval (node N i) / ∏ j ∈ (Finset.range (N + 1)).erase i,
        (node N i - node N j) := by
    apply Finset.sum_pos
    · intro i hi
      have hiN : i ≤ N := Finset.mem_range_succ_iff.mp hi
      have hp := div_pos (hpos i hiN) (zero_lt_prod_node_sub_node hiN)
      simpa only [mul_div_mul_left _ _ (pow_ne_zero i (by norm_num : (-1 : ℝ) ≠ 0))] using hp
    · exact Finset.nonempty_range_iff.mpr (by omega)
  rw [← hinterp, hzero] at hsum
  exact (lt_irrefl 0) hsum

/-- The odd Chebyshev polynomial vanishes at the origin. -/
theorem chebyshev_odd_eval_zero (d : ℕ) :
    (T ℝ (2 * (d : ℤ) + 1)).eval 0 = 0 :=
  T_eval_zero_of_odd ℝ (by exact ⟨d, by ring⟩)

/-- Its derivative at the origin has magnitude equal to its degree. -/
theorem chebyshev_odd_derivative_eval_zero (d : ℕ) :
    (T ℝ (2 * (d : ℤ) + 1)).derivative.eval 0 =
      (2 * (d : ℝ) + 1) * (-1 : ℝ) ^ d := by
  rw [T_derivative_eq_U]
  simp

/-- Central Bernstein inequality for a polynomial vanishing at the origin and bounded by one,
with an odd degree bound. -/
theorem central_odd_degree_derivative_upper (q : ℝ[X]) (d : ℕ)
    (hqdeg : q.natDegree ≤ 2 * d + 1) (hqzero : q.eval 0 = 0)
    (hqbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |q.eval x| ≤ 1) :
    q.derivative.eval 0 ≤ ((2 * d + 1 : ℕ) : ℝ) := by
  by_contra hbad
  have hbad : ((2 * d + 1 : ℕ) : ℝ) < q.derivative.eval 0 := lt_of_not_ge hbad
  let N : ℕ := 2 * d + 1
  let a : ℝ := (-1) ^ d
  let c : ℝ := q.derivative.eval 0 / N
  have hN : 0 < (N : ℝ) := by dsimp [N]; positivity
  have hc : 1 < c := by
    dsimp [c]
    exact (lt_div_iff₀ hN).mpr (by simpa [N] using hbad)
  have hcN : c * N = q.derivative.eval 0 := by
    dsimp [c]
    exact div_mul_cancel₀ _ hN.ne'
  have hTzero : (T ℝ N).eval 0 = 0 := by
    simpa [N, Nat.cast_add, Nat.cast_mul] using chebyshev_odd_eval_zero d
  have hTderiv : (T ℝ N).derivative.eval 0 = (N : ℝ) * a := by
    simpa [N, a, Nat.cast_add, Nat.cast_mul] using chebyshev_odd_derivative_eval_zero d
  let R : ℝ[X] := C c * T ℝ N - C a * q
  have hRdeg : R.natDegree ≤ N := by
    exact (natDegree_sub_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans (by simp))
      ((natDegree_C_mul_le _ _).trans hqdeg))
  have hRzero : R.eval 0 = 0 := by simp [R, hTzero, hqzero]
  have hRderiv : R.derivative.eval 0 = 0 := by
    simp only [R, derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add,
      eval_sub, eval_mul, eval_C, hTderiv]
    rw [← mul_assoc, hcN]
    ring
  have hRpos : ∀ i ≤ N, 0 < (-1 : ℝ) ^ i * R.eval (node N i) := by
    intro i hi
    have hval : |(-1 : ℝ) ^ i * (a * q.eval (node N i))| ≤ 1 := by
      simpa [a, abs_mul] using hqbnd _ node_mem_Icc
    have hvalupper := le_of_abs_le hval
    have hpow : (-1 : ℝ) ^ i * (-1 : ℝ) ^ i = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      0 < c - (-1 : ℝ) ^ i * (a * q.eval (node N i)) := by linarith
      _ = (-1 : ℝ) ^ i * R.eval (node N i) := by
        simp only [R, eval_sub, eval_mul, eval_C, eval_T_real_node (Finset.mem_Iic.mpr hi)]
        calc
          _ = c * ((-1 : ℝ) ^ i * (-1 : ℝ) ^ i) -
              (-1 : ℝ) ^ i * (a * q.eval (node N i)) := by rw [hpow, mul_one]
          _ = _ := by ring
  have hRcoeff0 : R.coeff 0 = 0 := by simpa only [coeff_zero_eq_eval_zero] using hRzero
  have hRcoeff1 : R.coeff 1 = 0 := by
    simpa only [← coeff_zero_eq_eval_zero, coeff_derivative, Nat.cast_zero, zero_add, Nat.cast_one, mul_one]
      using hRderiv
  obtain ⟨s, hs⟩ : (X : ℝ[X]) ^ 2 ∣ R := X_pow_dvd_iff.mpr (by
    intro k hk
    interval_cases k <;> assumption)
  have hnode : ∀ i ≤ N, node N i ≠ 0 := by
    intro i hi hzero
    have ht := eval_T_real_node (Finset.mem_Iic.mpr hi)
    rw [hzero, hTzero] at ht
    exact (pow_ne_zero i (by norm_num : (-1 : ℝ) ≠ 0)) ht.symm
  have hspos : ∀ i ≤ N, 0 < (-1 : ℝ) ^ i * s.eval (node N i) := by
    intro i hi
    have hp := hRpos i hi
    rw [hs] at hp
    simp only [eval_mul, eval_pow, eval_X] at hp
    have heq : (-1 : ℝ) ^ i * (node N i ^ 2 * s.eval (node N i)) =
        node N i ^ 2 * ((-1 : ℝ) ^ i * s.eval (node N i)) := by ring
    rw [heq] at hp
    exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero (hnode i hi))).mp hp
  have hsne : s ≠ 0 := by
    intro hz
    have hp := hspos 0 (by omega)
    simp [hz] at hp
  have hRdeg' : R.natDegree = 2 + s.natDegree := by
    rw [hs, natDegree_mul (pow_ne_zero 2 X_ne_zero) hsne, natDegree_X_pow]
  have hslarge := chebyshev_alternation_natDegree_le s hspos
  omega

/-- The absolute-value version of central Bernstein with an odd degree bound. -/
theorem central_odd_degree_derivative_le (q : ℝ[X]) (d : ℕ)
    (hqdeg : q.natDegree ≤ 2 * d + 1) (hqzero : q.eval 0 = 0)
    (hqbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |q.eval x| ≤ 1) :
    |q.derivative.eval 0| ≤ ((2 * d + 1 : ℕ) : ℝ) := by
  apply abs_le.mpr
  refine ⟨?_, central_odd_degree_derivative_upper q d hqdeg hqzero hqbnd⟩
  have h := central_odd_degree_derivative_upper (-q) d
    (by simpa using hqdeg) (by simpa using hqzero)
    (fun x hx => by simpa using hqbnd x hx)
  simp only [derivative_neg, eval_neg] at h
  linarith

/-- Applying central Bernstein to `X * p^2` controls the value at the origin directly
from the weighted square bound. -/
theorem weighted_square_eval_zero_le_degree (p : ℝ[X])
    (hp : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |x| * (p.eval x) ^ 2 ≤ 1) :
    (p.eval 0) ^ 2 ≤ 2 * (p.natDegree : ℝ) + 1 := by
  let q : ℝ[X] := X * p ^ 2
  have hqdeg : q.natDegree ≤ 2 * p.natDegree + 1 := by
    dsimp [q]
    calc
      (X * p ^ 2).natDegree ≤ X.natDegree + (p ^ 2).natDegree := natDegree_mul_le
      _ ≤ 1 + 2 * p.natDegree := by
        rw [natDegree_X]
        gcongr
        exact natDegree_pow_le
      _ = 2 * p.natDegree + 1 := by omega
  have hqzero : q.eval 0 = 0 := by simp [q]
  have hqbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |q.eval x| ≤ 1 := by
    intro x hx
    simpa [q, abs_mul, abs_sq] using hp x hx
  have hderiv : q.derivative.eval 0 = (p.eval 0) ^ 2 := by
    simp [q, derivative_mul]
  have h := central_odd_degree_derivative_upper q p.natDegree hqdeg hqzero hqbnd
  simpa only [hderiv, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h

end
end HierarchicalAbsoluteSpectral
