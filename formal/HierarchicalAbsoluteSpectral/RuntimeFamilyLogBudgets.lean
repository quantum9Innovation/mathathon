import HierarchicalAbsoluteSpectral.RuntimeFamilyUniformDegrees
import HierarchicalAbsoluteSpectral.NeumannDegree
import HierarchicalAbsoluteSpectral.ProbabilityEmbeddingSize

/-! Explicit confidence and mass-inverse budgets for the computed degrees;
all constants are independent of the refinement level. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open SRHT

theorem family_log_two_lower : (1/2 : ℝ) ≤ Real.log 2 := by
  have hh := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  norm_num at hh
  linarith

theorem family_neumann_uniform_bound (s m D : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1/1024) (hm : 2 ≤ m) (hD : 0 ≤ D)
    (hscale : Real.log (1/s) ≤ D*Real.log m) :
    ∃ hε : 0 < s^5/1000000000,
      (neumannCount (s^5/1000000000) hε : ℝ) ≤ (20*D+122)*Real.log m := by
  have hε : 0 < s^5/1000000000 := by positivity
  have hslt : s < 1 := by linarith
  have hs5 : s^5 < 1 := pow_lt_one₀ hs.le hslt (by omega)
  have hε1 : s^5/1000000000 < 1 := by nlinarith
  have hu := neumannCount_bound (s^5/1000000000) hε hε1
  have hlogm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hm
  have hc : Real.log (1000000000 : ℝ) ≤ 30*Real.log 2 := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1000000000)
      (by norm_num : (1000000000 : ℝ) ≤ (2 : ℝ)^30)
    rw [Real.log_pow] at hl
    exact hl
  have he : Real.log (1/(s^5/1000000000)) =
      Real.log (1000000000 : ℝ)+5*Real.log (1/s) := by
    rw [one_div,Real.log_inv,Real.log_div (pow_pos hs _).ne' (by norm_num),
      Real.log_pow,one_div,Real.log_inv]
    ring
  rw [he] at hu
  refine ⟨hε,?_⟩
  have ht := family_log_two_lower
  nlinarith

theorem family_embedding_order_uniform_bound (m : ℕ) (δ D : ℝ)
    (hm : 2 ≤ m) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hconfidence : Real.log (1/δ) ≤ D*Real.log (m : ℝ)) :
    (embeddingMomentOrder m δ : ℝ) ≤ ((D+5)/Real.log 2)*Real.log (m : ℝ) := by
  have hu := embeddingMomentOrder_log_bound m δ (by omega) hδ hδ1
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hmR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmpos : (0 : ℝ) < m := by linarith
  have he : Real.log (4*(m : ℝ)/δ) = 2*Real.log 2+Real.log (m : ℝ)+Real.log (1/δ) := by
    rw [Real.log_div (by positivity) hδ.ne',Real.log_mul (by norm_num) hmpos.ne',
      one_div,Real.log_inv,show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
    ring
  rw [he] at hu
  have hh := mul_le_mul_of_nonneg_right hu hlog2.le
  have hclear : (2+(2*Real.log 2+Real.log (m : ℝ)+Real.log (1/δ))/Real.log 2)*Real.log 2 =
      4*Real.log 2+Real.log (m : ℝ)+Real.log (1/δ) := by
    field_simp
    <;> ring
  rw [hclear] at hh
  have htarget : (D+5)/Real.log 2*Real.log (m : ℝ) =
      ((D+5)*Real.log (m : ℝ))/Real.log 2 := by ring
  rw [htarget]
  apply (le_div_iff₀ hlog2).mpr
  nlinarith

theorem family_embedding_rows_uniform_bound (n m : ℕ) (ε δ D : ℝ)
    (hm : 2 ≤ m) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hD : 0 ≤ D)
    (hconfidence : Real.log (1/δ) ≤ D*Real.log (m : ℝ)) :
    (embeddingComputedRowCount n m ε δ : ℝ) ≤
      1+8192*((m : ℝ)+27*(((D+5)/Real.log 2)*Real.log (m : ℝ))^3)/ε^2 := by
  have hu := embeddingComputedRowCount_size n m ε δ hε
  have hq := family_embedding_order_uniform_bound m δ D hm hδ hδ1 hconfidence
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (embeddingMomentOrder m δ)) hq 3
  have hDcast : (effectiveDimension m (embeddingMomentOrder m δ) : ℝ) =
      (m : ℝ)+27*(embeddingMomentOrder m δ : ℝ)^3 := by
    simp [effectiveDimension]
  rw [hDcast] at hu
  apply hu.trans
  apply add_le_add (le_refl (1 : ℝ))
  apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
  nlinarith

end
end HierarchicalAbsoluteSpectral
