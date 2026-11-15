import HierarchicalAbsoluteSpectral.DyadicNodes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! At Gauss--Chebyshev nodes each Chebyshev polynomial aliases to a
polynomial of degree below the number of nodes and interval norm at most one.
These are proof polynomials; the constructed interpolant is still Lagrange's
finite value polynomial from `DyadicNodes`.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Polynomial Polynomial.Chebyshev Set

def dyadicAngle (s j : ℕ) : ℝ := ((2*j+1 : ℕ) : ℝ)*Real.pi/(2*(2:ℝ)^s)

theorem chebyshev_at_dyadic_node (s k j : ℕ) :
    (T ℝ (k : ℤ)).eval (dyadicNode s j) = Real.cos ((k : ℝ)*dyadicAngle s j) := by
  rw [dyadicNode_eq_cos, T_real_cos]
  simp only [dyadicAngle, Int.cast_natCast]

theorem dyadicAngle_multiple (s j : ℕ) :
    (2*(2^s : ℕ) : ℝ)*dyadicAngle s j = ((2*j+1 : ℕ) : ℝ)*Real.pi := by
  unfold dyadicAngle
  push_cast
  field_simp

theorem dyadic_chebyshev_period (s k j : ℕ) :
    (T ℝ ((k+2*2^s : ℕ) : ℤ)).eval (dyadicNode s j) =
      -(T ℝ (k : ℤ)).eval (dyadicNode s j) := by
  rw [chebyshev_at_dyadic_node, chebyshev_at_dyadic_node]
  have heq : ((k+2*2^s : ℕ) : ℝ)*dyadicAngle s j =
      (k : ℝ)*dyadicAngle s j + ((2*j+1 : ℕ) : ℝ)*Real.pi := by
    rw [Nat.cast_add, add_mul, ← dyadicAngle_multiple s j]
    norm_cast
  rw [heq, Real.cos_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
  simp [pow_add, pow_mul]

theorem dyadic_chebyshev_reflection (s k j : ℕ) (hk : k ≤ 2*2^s) :
    (T ℝ ((2*2^s-k : ℕ) : ℤ)).eval (dyadicNode s j) =
      -(T ℝ (k : ℤ)).eval (dyadicNode s j) := by
  rw [chebyshev_at_dyadic_node, chebyshev_at_dyadic_node]
  have heq : ((2*2^s-k : ℕ) : ℝ)*dyadicAngle s j =
      ((2*j+1 : ℕ) : ℝ)*Real.pi - (k : ℝ)*dyadicAngle s j := by
    rw [Nat.cast_sub hk, sub_mul, ← dyadicAngle_multiple s j]
    norm_cast
  rw [heq, Real.cos_nat_mul_pi_sub]
  simp [pow_add, pow_mul]

theorem dyadic_chebyshev_zero (s j : ℕ) :
    (T ℝ ((2^s : ℕ) : ℤ)).eval (dyadicNode s j) = 0 := by
  rw [chebyshev_at_dyadic_node]
  have heq : ((2^s : ℕ) : ℝ)*dyadicAngle s j = (j : ℝ)*Real.pi + Real.pi/2 := by
    have hm := dyadicAngle_multiple s j
    push_cast at hm ⊢
    nlinarith
  rw [heq, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]

theorem dyadic_chebyshev_alias (s k : ℕ) :
    ∃ p : ℝ[X], p.degree < (2^s : ℕ) ∧
      (∀ x ∈ Icc (-1:ℝ) 1, |p.eval x| ≤ 1) ∧
      (∀ j : Fin (2^s), p.eval (dyadicNode s j) = (T ℝ (k : ℤ)).eval (dyadicNode s j)) := by
  have hn : 0 < 2^s := by positivity
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 2^s
    · refine ⟨T ℝ (k : ℤ), ?_, ?_, fun _ => rfl⟩
      · simpa only [degree_T, Int.natAbs_natCast, Nat.cast_lt] using hk
      · exact fun x hx => abs_eval_T_real_le_one _ (abs_le.mpr hx)
    · by_cases he : k = 2^s
      · subst k
        refine ⟨0, ?_, ?_, ?_⟩
        · rw [degree_zero]
          exact WithBot.bot_lt_coe _
        · intro x hx
          norm_num
        · intro j
          simpa using (dyadic_chebyshev_zero s j).symm
      · by_cases hk' : k ≤ 2*2^s
        · have hr : 2*2^s-k < 2^s := by omega
          refine ⟨-T ℝ ((2*2^s-k : ℕ) : ℤ), ?_, ?_, ?_⟩
          · simpa only [degree_neg, degree_T, Int.natAbs_natCast, Nat.cast_lt] using hr
          · intro x hx
            simpa only [eval_neg, abs_neg] using
              abs_eval_T_real_le_one (2*2^s-k : ℕ) (abs_le.mpr hx)
          · intro j
            rw [eval_neg, dyadic_chebyshev_reflection s k j hk', neg_neg]
        · have hr : k-2*2^s < k := by omega
          obtain ⟨p, hp, hb, hv⟩ := ih (k-2*2^s) hr
          refine ⟨-p, by simpa only [degree_neg] using hp, ?_, ?_⟩
          · intro x hx
            simpa only [eval_neg, abs_neg] using hb x hx
          · intro j
            have heq : k = (k-2*2^s)+2*2^s := by omega
            rw [eval_neg, hv]
            conv_rhs => rw [heq, dyadic_chebyshev_period]

def dyadicChebyshevInterpolant (s k : ℕ) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (fun j : Fin (2^s) => dyadicNode s j)
    (fun j => (T ℝ (k : ℤ)).eval (dyadicNode s j))

theorem dyadicChebyshevInterpolant_bound (s k : ℕ) (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    |(dyadicChebyshevInterpolant s k).eval x| ≤ 1 := by
  obtain ⟨p, hp, hb, hv⟩ := dyadic_chebyshev_alias s k
  have heq : p = dyadicChebyshevInterpolant s k := by
    apply Lagrange.eq_interpolate_of_eval_eq _ (dyadicNode_injective s).injOn
    · simpa using hp
    · exact fun j _ => hv j
  rw [← heq]
  exact hb x hx

theorem dyadicChebyshevInterpolant_exact (s k : ℕ) (hk : k < 2^s) :
    dyadicChebyshevInterpolant s k = T ℝ (k : ℤ) := by
  symm
  apply Lagrange.eq_interpolate (dyadicNode_injective s).injOn
  simpa only [degree_T, Int.natAbs_natCast, Finset.card_univ, Fintype.card_fin,
    Nat.cast_lt] using hk

end
end HierarchicalAbsoluteSpectral
