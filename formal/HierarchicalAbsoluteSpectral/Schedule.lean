import HierarchicalAbsoluteSpectral.Scalars
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The uniform action-cost cancellations in Section 8. We write `s=sqrt(rho)`;
then `m=N*s^2` and `theta=s^5`. This avoids any ambiguity about real powers.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open Filter Asymptotics

/-- First inequality of equation (22), including its factor 32. -/
theorem true_cost_cancellation (m N s hL : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hs : 0 < s) (hh : 0 ≤ hL)
    (hrho : m = N * s^2) (hterminal : hL ≤ 1024 * s) :
    m * N * Real.sqrt (hL / s^5) ≤ 32 * N^2 := by
  have hroot : Real.sqrt (hL / s^5) ≤ 32 / s^2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), div_pow]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have := mul_le_mul_of_nonneg_left hterminal (show 0 ≤ s^4 by positivity)
    nlinarith
  calc
    m * N * Real.sqrt (hL / s^5) ≤ m * N * (32 / s^2) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = 32 * N^2 := by rw [hrho]; field_simp

/-- Second inequality of equation (22), uniform in the refinement level. -/
theorem fine_cost_cancellation (m N s h₀ H hj hL : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hs : 0 < s) (hbase : 0 < h₀)
    (hH : 0 < H)
    (hrho : m = N * s^2) (hterminal : s ≤ hL)
    (hschedule : hj^2 = H * h₀ * s) :
    m^2 * H / (hj^2 * Real.sqrt (hL * s^5)) ≤ N^2 / h₀ := by
  have hLpos : 0 < hL := hs.trans_le hterminal
  have hroot : s^3 ≤ Real.sqrt (hL * s^5) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity)]
    have := mul_le_mul_of_nonneg_right hterminal (show 0 ≤ s^5 by positivity)
    nlinarith
  calc
    m^2 * H / (hj^2 * Real.sqrt (hL * s^5)) =
        m^2 / (h₀ * s * Real.sqrt (hL * s^5)) := by
      rw [hschedule]
      field_simp
    _ ≤ m^2 / (h₀ * s * s^3) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = N^2 / h₀ := by rw [hrho]; field_simp

/-- A linear recurrence accumulates a common overhead once per leaf. -/
theorem cost_recurrence_unfold (a : ℝ) (d leaf : ℕ → ℝ)
    (ha : 1 ≤ a) (hleaf : ∀ j, 0 ≤ leaf j)
    (hstep : ∀ j, d (j + 1) ≤ a * (d j + leaf j)) (L : ℕ) :
    d L ≤ a^L * (d 0 + ∑ j ∈ Finset.range L, leaf j) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have ha0 : 0 ≤ a := by linarith
    have hpow : 1 ≤ a^L := one_le_pow₀ ha
    have hnonneg := mul_nonneg (sub_nonneg.mpr hpow) (hleaf L)
    calc
      d (L + 1) ≤ a * (d L + leaf L) := hstep L
      _ ≤ a * (a^L * (d 0 + ∑ j ∈ Finset.range L, leaf j) + leaf L) :=
        mul_le_mul_of_nonneg_left (add_le_add ih (le_refl (leaf L))) ha0
      _ ≤ a^(L+1) * (d 0 + ∑ j ∈ Finset.range (L+1), leaf j) := by
        rw [Finset.sum_range_succ, pow_succ]
        nlinarith

/-- The logarithm of the displayed growing-depth overhead is o(log m). -/
theorem loglog_sq_isLittleO_log :
    (fun m : ℝ => (Real.log (Real.log m))^2) =o[atTop] Real.log := by
  simpa only [Function.comp_def, id_eq] using
    (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto Real.tendsto_log_atTop

/-- The first refinement's acceptance test forces N/m >= 2^40. -/
theorem first_level_cutoff (s : ℝ) (hs : 0 ≤ s)
    (haccept : Real.sqrt s ≤ (1 / 1024 : ℝ)) :
    s^2 ≤ (1 / 1024 : ℝ)^4 := by
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg s) (by norm_num : (0:ℝ) ≤ 1/1024)).mpr haccept
  rw [Real.sq_sqrt hs] at hsq
  nlinarith [sq_nonneg (s - (1/1024 : ℝ)^2)]

end
end HierarchicalAbsoluteSpectral
