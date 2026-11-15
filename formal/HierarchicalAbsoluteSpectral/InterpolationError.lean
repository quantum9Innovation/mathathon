import HierarchicalAbsoluteSpectral.InverseRootSeries
import HierarchicalAbsoluteSpectral.ChebyshevAliasing

/-! Uniform error of the actual finite value interpolant in Lemma 4. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Polynomial Polynomial.Chebyshev Set

theorem dyadic_interpolation_eval (s : ℕ) (v : Fin (2^s) → ℝ) (x : ℝ) :
    (Lagrange.interpolate Finset.univ (fun j : Fin (2^s) => dyadicNode s j) v).eval x =
      ∑ j : Fin (2^s), v j * (Lagrange.basis Finset.univ
        (fun j : Fin (2^s) => dyadicNode s j) j).eval x := by
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]

theorem hasSum_dyadic_interpolation (s : ℕ) (a : ℕ → ℝ) (v : Fin (2^s) → ℝ)
    (hv : ∀ j : Fin (2^s), HasSum (fun k : ℕ => a k * (T ℝ (k : ℤ)).eval (dyadicNode s j)) (v j))
    (x : ℝ) :
    HasSum (fun k : ℕ => a k * (dyadicChebyshevInterpolant s k).eval x)
      ((Lagrange.interpolate Finset.univ (fun j : Fin (2^s) => dyadicNode s j) v).eval x) := by
  have h := hasSum_sum (s := Finset.univ) (fun j _ => (hv j).mul_right
    ((Lagrange.basis Finset.univ (fun j : Fin (2^s) => dyadicNode s j) j).eval x))
  rw [dyadic_interpolation_eval]
  apply h.congr_fun
  intro k
  rw [dyadicChebyshevInterpolant, dyadic_interpolation_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem inverseRootInterpolant_hasSum (s : ℕ) (η x : ℝ) (hη : 0 < η) :
    HasSum (fun k : ℕ => inverseRootChebyshevCoeff η hη k *
      (dyadicChebyshevInterpolant s k).eval x) ((inverseRootInterpolant s η).eval x) := by
  exact hasSum_dyadic_interpolation s (inverseRootChebyshevCoeff η hη)
    (fun j => inverseRootValue η (dyadicNode s j))
    (fun j => inverseRootChebyshev_hasSum η _ hη (dyadicNode_mem_interval s j)) x

theorem inverseRootInterpolant_error_geometric (s : ℕ) (η x : ℝ) (hη : 0 < η)
    (hx : x ∈ Icc (-1:ℝ) 1) :
    |(inverseRootInterpolant s η).eval x - inverseRootValue η x| ≤
      4*(Real.sqrt η)⁻¹*((1+η/4)⁻¹)^(2^s)*(1-(1+η/4)⁻¹)⁻¹ := by
  let r : ℝ := (1+η/4)⁻¹
  let a := inverseRootChebyshevCoeff η hη
  let e : ℕ → ℝ := fun k => a k*((dyadicChebyshevInterpolant s k).eval x - (T ℝ (k : ℤ)).eval x)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (inv_lt_one₀ (by positivity)).mpr (by linarith)
  have hb (k : ℕ) : |e k| ≤ 4*(Real.sqrt η)⁻¹*r^k := by
    have hi := dyadicChebyshevInterpolant_bound s k x hx
    have ht := abs_eval_T_real_le_one (k : ℤ) (abs_le.mpr hx)
    have hd : |(dyadicChebyshevInterpolant s k).eval x - (T ℝ (k : ℤ)).eval x| ≤ 2 := by
      exact (abs_sub _ _).trans (by linarith)
    have ha := inverseRootChebyshevCoeff_bound η hη k
    dsimp [e, a]
    rw [abs_mul]
    calc
      _ ≤ (2*(Real.sqrt η)⁻¹*r^k)*2 :=
        mul_le_mul ha hd (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have he0 (k : ℕ) (hk : k < 2^s) : e k = 0 := by
    simp only [e, dyadicChebyshevInterpolant_exact s k hk, sub_self, mul_zero]
  have hs : HasSum e ((inverseRootInterpolant s η).eval x - inverseRootValue η x) := by
    have h := (inverseRootInterpolant_hasSum s η x hη).sub
      (inverseRootChebyshev_hasSum η x hη hx)
    apply h.congr_fun
    intro k
    dsimp [e, a]
    ring
  have hpre : ∑ k ∈ Finset.range (2^s), e k = 0 :=
    Finset.sum_eq_zero fun k hk => he0 k (Finset.mem_range.mp hk)
  have htail : HasSum (fun k : ℕ => e (k+2^s))
      ((inverseRootInterpolant s η).eval x - inverseRootValue η x) := by
    have h := (hasSum_nat_add_iff' (2^s)).mpr hs
    simpa only [hpre, sub_zero] using h
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (4*(Real.sqrt η)⁻¹*r^(2^s))
  have hbound : ‖∑' k : ℕ, e (k+2^s)‖ ≤
      (4*(Real.sqrt η)⁻¹*r^(2^s))*(1-r)⁻¹ := by
    apply tsum_of_norm_bounded hg
    intro k
    simpa only [Real.norm_eq_abs, pow_add, mul_assoc, mul_left_comm, mul_comm] using hb (k+2^s)
  simpa only [htail.tsum_eq, Real.norm_eq_abs, r, mul_assoc] using hbound

theorem inverseRootInterpolant_uniform_error (s : ℕ) (η x : ℝ)
    (hη : 0 < η) (hη' : η ≤ 1/8) (hx : x ∈ Icc (-1:ℝ) 1) :
    |(inverseRootInterpolant s η).eval x - inverseRootValue η x| ≤
      (24/(η*Real.sqrt η))*((1+η/4)⁻¹)^(2^s) := by
  have h := inverseRootInterpolant_error_geometric s η x hη hx
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hR : 0 < 1+η/4 := by positivity
  have hr : (1+η/4)⁻¹ < 1 := (inv_lt_one₀ hR).mpr (by linarith)
  have hid : 4*(Real.sqrt η)⁻¹*(1-(1+η/4)⁻¹)⁻¹ =
      (16+4*η)/(η*Real.sqrt η) := by
    field_simp [hη.ne', hs.ne']
    ring
  have hb : 4*(Real.sqrt η)⁻¹*(1-(1+η/4)⁻¹)⁻¹ ≤ 24/(η*Real.sqrt η) := by
    rw [hid]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  calc
    _ ≤ _ := h
    _ = (4*(Real.sqrt η)⁻¹*(1-(1+η/4)⁻¹)⁻¹)*((1+η/4)⁻¹)^(2^s) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (by positivity)

end
end HierarchicalAbsoluteSpectral
