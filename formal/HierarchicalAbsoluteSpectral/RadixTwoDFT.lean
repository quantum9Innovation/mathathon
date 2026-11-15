import HierarchicalAbsoluteSpectral.DyadicNodes
import Mathlib.Algebra.BigOperators.Intervals

/-! Algebraic correctness of the radix-two recurrence. This is its value
specification, preceding the materialized implementation and its cost proof. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Finset

def finiteDFT (n : ℕ) (w : ℂ) (v : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, w^(j*k)*v j

theorem sum_range_even_odd {M : Type*} [AddCommMonoid M] (v : ℕ → M) (m : ℕ) :
    ∑ j ∈ range (2*m), v j = (∑ j ∈ range m, v (2*j)) + ∑ j ∈ range m, v (2*j+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1) = (2*m+1)+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ac_rfl

theorem finiteDFT_split (m k : ℕ) (w : ℂ) (v : ℕ → ℂ) :
    finiteDFT (2*m) w v k = finiteDFT m (w^2) (fun j => v (2*j)) k +
      w^k * finiteDFT m (w^2) (fun j => v (2*j+1)) k := by
  unfold finiteDFT
  rw [sum_range_even_odd, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [← pow_mul]
    congr 1
    congr 1
    ring
  · apply Finset.sum_congr rfl
    intro j hj
    rw [show (2*j+1)*k = 2*(j*k)+k by ring, pow_add, pow_mul]
    ring

theorem finiteDFT_period (n k : ℕ) (w : ℂ) (v : ℕ → ℂ) (hw : w^n = 1) :
    finiteDFT n w v (k+n) = finiteDFT n w v k := by
  unfold finiteDFT
  apply Finset.sum_congr rfl
  intro j hj
  have heq : w^(j*n) = (w^n)^j := by rw [Nat.mul_comm j n, pow_mul]
  rw [Nat.mul_add, pow_add, heq, hw, one_pow, mul_one]

def radixTwoDFT : ℕ → ℂ → (ℕ → ℂ) → ℕ → ℂ
  | 0, _, v, _ => v 0
  | s+1, w, v, k =>
      let a := radixTwoDFT s (w^2) (fun j => v (2*j))
      let b := radixTwoDFT s (w^2) (fun j => v (2*j+1))
      if k < 2^s then a k + w^k*b k
      else a (k-2^s) - w^(k-2^s)*b (k-2^s)

def IsDyadicRoot (w : ℂ) (s : ℕ) : Prop :=
  match s with
  | 0 => True
  | t+1 => w^(2^t) = -1

theorem isDyadicRoot_square (s : ℕ) (w : ℂ) (hw : IsDyadicRoot w (s+1)) :
    IsDyadicRoot (w^2) s := by
  cases s with
  | zero => trivial
  | succ s =>
    change (w^2)^(2^s) = -1
    change w^(2^(s+1)) = -1 at hw
    rw [← pow_mul]
    simpa only [pow_succ'] using hw

theorem radixTwoDFT_correct (s : ℕ) (w : ℂ) (v : ℕ → ℂ) (hw : IsDyadicRoot w s)
    (k : ℕ) (hk : k < 2^s) : radixTwoDFT s w v k = finiteDFT (2^s) w v k := by
  induction s generalizing w v k with
  | zero =>
    simp only [pow_zero] at hk
    have hk0 : k = 0 := by omega
    simp [radixTwoDFT, finiteDFT, hk0]
  | succ s ih =>
    have hroot := isDyadicRoot_square s w hw
    have hw' : w^(2^s) = -1 := hw
    have hw2 : (w^2)^(2^s) = 1 := by
      rw [← pow_mul, Nat.mul_comm 2 (2^s), pow_mul, hw']
      norm_num
    rw [radixTwoDFT, pow_succ' (2:ℕ) s, finiteDFT_split]
    split_ifs with hkm
    · rw [ih (w^2) (fun j => v (2*j)) hroot k hkm,
        ih (w^2) (fun j => v (2*j+1)) hroot k hkm]
    · have hkm' : k-2^s < 2^s := by rw [pow_succ] at hk; omega
      have heq : k = (k-2^s)+2^s := by omega
      rw [ih (w^2) (fun j => v (2*j)) hroot (k-2^s) hkm',
        ih (w^2) (fun j => v (2*j+1)) hroot (k-2^s) hkm']
      conv_rhs => rw [heq, finiteDFT_period _ _ _ _ hw2, finiteDFT_period _ _ _ _ hw2,
        pow_add, hw']
      ring

end
end HierarchicalAbsoluteSpectral
