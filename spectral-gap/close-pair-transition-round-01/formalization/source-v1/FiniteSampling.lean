import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace ClosePair

theorem pair_membership_count (n m : ℕ) (hm : 2 ≤ m)
    (a b : Fin n) (hab : a ≠ b) :
    ((Finset.univ.powersetCard m).filter
      (fun S : Finset (Fin n) => (a, b) ∈ S.offDiag)).card =
      (n - 2).choose (m - 2) := by
  have h := Finset.card_filter_powersetCard_subset
    ({a, b} : Finset (Fin n)) Finset.univ m (Finset.subset_univ _)
    (by simpa [hab] using hm)
  simpa [Finset.mem_offDiag, Finset.insert_subset_iff, Finset.singleton_subset_iff, hab] using h

theorem sum_offDiag_as_indicator (n : ℕ) (S : Finset (Fin n))
    (w : Fin n × Fin n → ℝ) :
    ∑ p ∈ S.offDiag, w p =
      ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
        if p ∈ S.offDiag then w p else 0 := by
  have heq : S.offDiag = (Finset.univ : Finset (Fin n)).offDiag.filter
      (fun p => p ∈ S.offDiag) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · intro hp
      exact ⟨Finset.offDiag_mono (Finset.subset_univ S) hp, hp⟩
    · exact And.right
  calc
    ∑ p ∈ S.offDiag, w p =
        ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag.filter
          (fun p => p ∈ S.offDiag), w p := congrArg (fun T => ∑ p ∈ T, w p) heq
    _ = _ := by rw [Finset.sum_filter]

theorem sum_subset_offDiag (n m : ℕ) (hm : 2 ≤ m)
    (w : Fin n × Fin n → ℝ) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ∑ p ∈ S.offDiag, w p =
      ((n - 2).choose (m - 2) : ℝ) *
        ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, w p := by
  have hstep :
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        ∑ p ∈ S.offDiag, w p) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
          if p ∈ S.offDiag then w p else 0 := by
    apply Finset.sum_congr rfl
    intro S _
    exact sum_offDiag_as_indicator n S w
  rw [hstep, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hab : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [pair_membership_count n m hm p.1 p.2 hab]

theorem choose_pair_ratio (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    ((n - 2).choose (m - 2) : ℝ) / (n.choose m : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hn : 2 ≤ n := hm.trans hmn
  have hc : (n.choose m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hmn)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0 < n)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h := Nat.choose_mul (n := n) (k := m) (s := 2) hm
  have hr : (n.choose m : ℝ) * (m.choose 2 : ℝ) =
      (n.choose 2 : ℝ) * ((n - 2).choose (m - 2) : ℝ) := by exact_mod_cast h
  rw [Nat.cast_choose_two, Nat.cast_choose_two] at hr
  apply (div_eq_div_iff hc (mul_ne_zero hn0 hn1)).mpr
  nlinarith

theorem uniform_subset_offDiag_average (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n)
    (w : Fin n × Fin n → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ∑ p ∈ S.offDiag, w p) / (n.choose m : ℝ) =
      ((m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1))) *
        ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, w p := by
  rw [sum_subset_offDiag n m hm]
  rw [mul_div_right_comm, choose_pair_ratio n m hm hmn]

theorem uniform_subset_frobenius (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n)
    (K : Fin n → Fin n → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ∑ p ∈ S.offDiag, K p.1 p.2 ^ 2) / (n.choose m : ℝ) =
      ((m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1))) *
        ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, K p.1 p.2 ^ 2 :=
  uniform_subset_offDiag_average n m hm hmn (fun p => K p.1 p.2 ^ 2)

#print axioms pair_membership_count
#print axioms sum_offDiag_as_indicator
#print axioms sum_subset_offDiag
#print axioms choose_pair_ratio
#print axioms uniform_subset_offDiag_average
#print axioms uniform_subset_frobenius

end ClosePair
