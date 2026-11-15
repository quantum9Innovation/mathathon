import HierarchicalAbsoluteSpectral.RuntimeFamilyBounds
import HierarchicalAbsoluteSpectral.RuntimeFamilyAsymptotics

/-! Unfolding the actual level-dependent action recurrence multiplies the
common overhead once and sums leaf costs; a kernel overhead is never raised
to the depth. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter Asymptotics
open scoped BigOperators

theorem family_cost_recurrence_unfold (a : ℝ) (h c leaf : ℕ → ℝ) (L : ℕ)
    (ha : 1 ≤ a) (hpositive : ∀ j ≤ L, 0 < h j)
    (hleaf : ∀ j < L, 0 ≤ leaf j)
    (hstep : ∀ j < L, c (j+1) ≤ a*(h j/h (j+1))*(c j+leaf j)) :
    h L*c L ≤ a^L*(h 0*c 0+∑ j ∈ Finset.range L, h j*leaf j) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hp := hpositive (L+1) (by omega)
    have hpL := hpositive L (by omega)
    have hi := ih (fun j hj => hpositive j (by omega))
      (fun j hj => hleaf j (by omega)) (fun j hj => hstep j (by omega))
    have hs := mul_le_mul_of_nonneg_left (hstep L (by omega)) hp.le
    have he : h (L+1)*(a*(h L/h (L+1))*(c L+leaf L)) = a*(h L*c L+h L*leaf L) := by
      field_simp [hp.ne']
      <;> ring
    rw [he] at hs
    have hpow : 1 ≤ a^L := one_le_pow₀ ha
    have hleaf0 : 0 ≤ h L*leaf L := mul_nonneg hpL.le (hleaf L (by omega))
    calc
      _ ≤ a*(h L*c L+h L*leaf L) := hs
      _ ≤ a*(a^L*(h 0*c 0+∑ j ∈ Finset.range L, h j*leaf j)+h L*leaf L) :=
        mul_le_mul_of_nonneg_left (add_le_add hi (le_refl _)) (by linarith)
      _ ≤ _ := by
        rw [Finset.sum_range_succ,pow_succ]
        have hh := mul_nonneg (sub_nonneg.mpr hpow) hleaf0
        nlinarith

theorem family_cost_recurrence_shared_kernel (a χ : ℝ) (h c leaf : ℕ → ℝ) (L : ℕ)
    (ha : 1 ≤ a) (hχ : 0 ≤ χ) (hpositive : ∀ j ≤ L, 0 < h j)
    (hleaf : ∀ j < L, 0 ≤ leaf j)
    (hbase : h 0*c 0 ≤ χ)
    (hleaf_bound : ∀ j < L, h j*leaf j ≤ χ)
    (hstep : ∀ j < L, c (j+1) ≤ a*(h j/h (j+1))*(c j+leaf j)) :
    h L*c L ≤ a^L*((L+1 : ℕ) : ℝ)*χ := by
  have hu := family_cost_recurrence_unfold a h c leaf L ha hpositive hleaf hstep
  have hsum : (∑ j ∈ Finset.range L, h j*leaf j) ≤ (L : ℝ)*χ := by
    calc
      _ ≤ ∑ j ∈ Finset.range L, χ :=
        Finset.sum_le_sum (fun j hj => hleaf_bound j (Finset.mem_range.mp hj))
      _ = _ := by simp
  calc
    _ ≤ a^L*(h 0*c 0+∑ j ∈ Finset.range L, h j*leaf j) := hu
    _ ≤ a^L*(χ+(L : ℝ)*χ) :=
      mul_le_mul_of_nonneg_left (add_le_add hbase hsum) (by positivity)
    _ = _ := by push_cast; ring

/-- The displayed unfolded cost has exponent two plus an arbitrarily
small slack once its normalized kernel overhead is subpolynomial. -/
theorem family_unfolded_cost_eventually (χ N cost : ℝ → ℝ) (K : ℝ)
    (hχ : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, χ m ≤ m^ε)
    (hbound : ∀ᶠ m in atTop, cost m ≤
      (N m)^2*χ m*Real.exp (K*(1+Real.log (Real.log (2*m)))^2))
    (hχ0 : ∀ᶠ m in atTop, 0 ≤ χ m) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, cost m ≤ (N m)^2*m^ε := by
  intro ε hε
  filter_upwards [hbound,hχ (ε/2) (by positivity),hχ0,
    family_exp_loglog_two_mul_eventually_le_rpow K (ε/2) (by positivity),
    eventually_gt_atTop (0 : ℝ)] with m hm hkernel hk0 hover hm0
  calc
    _ ≤ (N m)^2*χ m*Real.exp (K*(1+Real.log (Real.log (2*m)))^2) := hm
    _ ≤ ((N m)^2*m^(ε/2))*m^(ε/2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hkernel (sq_nonneg _)) hover
        (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hm0]; congr 2 <;> ring

end
end HierarchicalAbsoluteSpectral
