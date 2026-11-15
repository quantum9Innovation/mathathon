import HierarchicalAbsoluteSpectral.ProbabilityEmbeddingParameters

/-! Explicit bounds for the integers produced by the counted parameter
programs. The logarithm occurs only in these cost and size bounds. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix SRHT

theorem embeddingMomentOrder_log_bound (m : ℕ) (δ : ℝ)
    (hm : 1 ≤ m) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (embeddingMomentOrder m δ : ℝ) ≤ 2+Real.log (4*(m : ℝ)/δ)/Real.log 2 := by
  let x : ℝ := 4*(m : ℝ)/δ
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 1 ≤ x := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  cases he : leastHalvings x 1 (by norm_num) with
  | zero =>
    have hq : embeddingMomentOrder m δ = 1 := by
      simp only [embeddingMomentOrder]
      change leastHalvings x 1 _+1 = 1
      rw [he]
    rw [hq]
    have hn := div_nonneg hlog hlog2.le
    simpa only [Nat.cast_one,x] using (show (1 : ℝ) ≤ 2+Real.log x/Real.log 2 by linarith)
  | succ j =>
    have hmin : ¬x/(2 : ℝ)^j ≤ 1 :=
      Nat.find_min (exists_halving_bound x 1 (by norm_num)) (by
        change j < leastHalvings x 1 (by norm_num)
        omega)
    have hp : (2 : ℝ)^j < x := by
      simpa only [one_mul] using (lt_div_iff₀ (by positivity)).mp (lt_of_not_ge hmin)
    have hl := Real.log_lt_log (by positivity : (0 : ℝ) < 2^j) hp
    rw [Real.log_pow] at hl
    have hj : (j : ℝ) < Real.log x/Real.log 2 := (lt_div_iff₀ hlog2).mpr hl
    have hq : embeddingMomentOrder m δ = j+2 := by
      unfold embeddingMomentOrder
      change leastHalvings x 1 _+1 = j+2
      rw [he]
    rw [hq]
    push_cast
    change (j : ℝ)+2 ≤ 2+Real.log x/Real.log 2
    linarith

theorem embeddingComputedRowCount_size (n m : ℕ) (ε δ : ℝ) (hε : 0 < ε) :
    (embeddingComputedRowCount n m ε δ : ℝ) ≤
      1+8192*(effectiveDimension m (embeddingMomentOrder m δ) : ℝ)/ε^2 := by
  have hx : 0 ≤ embeddingRowTarget m (embeddingMomentOrder m δ) ε := by
    unfold embeddingRowTarget
    positivity
  calc
    _ ≤ (⌈embeddingRowTarget m (embeddingMomentOrder m δ) ε⌉₊ : ℝ) := by
      exact_mod_cast (min_le_right n ⌈embeddingRowTarget m (embeddingMomentOrder m δ) ε⌉₊)
    _ ≤ _ := by
      have hh := (Nat.ceil_lt_add_one hx).le
      simpa only [embeddingRowTarget,add_comm] using hh

end
end HierarchicalAbsoluteSpectral
