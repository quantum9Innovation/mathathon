import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace ClosePair

noncomputable def constantProjection (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ _ => 1 / (n : ℝ)

theorem far_row_entry (n : ℕ) (R T W : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hR : R = T - α • constantProjection n + W)
    (c j : Fin n) (hzero : T c j = 0) :
    R c j = W c j - α / (n : ℝ) := by
  rw [hR]
  simp [constantProjection, hzero]
  ring

theorem far_row_energy (n : ℕ) (hn : 0 < n)
    (R T W : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hR : R = T - α • constantProjection n + W)
    (c : Fin n) (S : Finset (Fin n)) (hzero : ∀ j ∈ S, T c j = 0) :
    ∑ j ∈ S, R c j ^ 2 ≤
      2 * ∑ j : Fin n, W c j ^ 2 + 2 * α ^ 2 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hcard : (S.card : ℝ) ≤ (n : ℝ) := by
    have hnat : S.card ≤ n := by simpa using Finset.card_le_univ S
    exact_mod_cast hnat
  have hcount : (S.card : ℝ) * (α / (n : ℝ)) ^ 2 ≤ α ^ 2 / (n : ℝ) := by
    calc
      (S.card : ℝ) * (α / (n : ℝ)) ^ 2 ≤
          (n : ℝ) * (α / (n : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = α ^ 2 / (n : ℝ) := by field_simp
  have hsub : ∑ j ∈ S, W c j ^ 2 ≤ ∑ j : Fin n, W c j ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    intro j _ _
    exact sq_nonneg _
  calc
    ∑ j ∈ S, R c j ^ 2 ≤ ∑ j ∈ S, (2 * W c j ^ 2 + 2 * (α / (n : ℝ)) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [far_row_entry n R T W α hR c j (hzero j hj)]
      nlinarith [sq_nonneg (W c j + α / (n : ℝ))]
    _ = 2 * ∑ j ∈ S, W c j ^ 2 + 2 * (S.card : ℝ) * (α / (n : ℝ)) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 2 * ∑ j : Fin n, W c j ^ 2 + 2 * α ^ 2 / (n : ℝ) := by
      calc
        2 * ∑ j ∈ S, W c j ^ 2 + 2 * (S.card : ℝ) * (α / (n : ℝ)) ^ 2 =
            2 * ∑ j ∈ S, W c j ^ 2 + 2 * ((S.card : ℝ) * (α / (n : ℝ)) ^ 2) := by ring
        _ ≤ 2 * ∑ j : Fin n, W c j ^ 2 + 2 * (α ^ 2 / (n : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_left hsub (by norm_num))
            (mul_le_mul_of_nonneg_left hcount (by norm_num))
        _ = _ := by ring

#print axioms far_row_entry
#print axioms far_row_energy

end ClosePair
