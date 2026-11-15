import HierarchicalAbsoluteSpectral.ThresholdSearch

/-! The search-cap integer is found by scalar comparison and halving.
The least integer is used only as a termination measure; the program executes
the displayed field/comparison instructions and does not call a logarithm. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

theorem exists_halving_bound (x ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, x/(2:ℝ)^n ≤ ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (x/ε)
  have hp : (n:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  refine ⟨n, (div_le_iff₀ (pow_pos (by norm_num) _)).mpr ?_⟩
  have hh := (div_lt_iff₀ hε).mp (hn.trans_le hp)
  nlinarith

def leastHalvings (x ε : ℝ) (hε : 0 < ε) : ℕ := Nat.find (exists_halving_bound x ε hε)

theorem leastHalvings_spec (x ε : ℝ) (hε : 0 < ε) :
    x/(2:ℝ)^(leastHalvings x ε hε) ≤ ε := Nat.find_spec (exists_halving_bound x ε hε)

theorem leastHalvings_le (x ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : x/(2:ℝ)^n ≤ ε) : leastHalvings x ε hε ≤ n :=
  Nat.find_min' (exists_halving_bound x ε hε) hn

theorem leastHalvings_zero (x ε : ℝ) (hε : 0 < ε) (hx : x ≤ ε) :
    leastHalvings x ε hε = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact leastHalvings_le x ε hε 0 (by simpa using hx)

theorem leastHalvings_half_lt (x ε : ℝ) (hε : 0 < ε) (hx : ¬x ≤ ε) :
    leastHalvings (x/2) ε hε < leastHalvings x ε hε := by
  have hn : leastHalvings x ε hε ≠ 0 := by
    intro hz
    have hs := leastHalvings_spec x ε hε
    rw [hz] at hs
    exact hx (by simpa using hs)
  obtain ⟨n, hn'⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hs := leastHalvings_spec x ε hε
  rw [hn', pow_succ] at hs
  have hm : leastHalvings (x/2) ε hε ≤ n :=
    leastHalvings_le (x/2) ε hε n (by convert hs using 1 <;> field_simp <;> ring)
  omega

theorem leastHalvings_half_succ (x ε : ℝ) (hε : 0 < ε) (hx : ¬x ≤ ε) :
    leastHalvings x ε hε = leastHalvings (x/2) ε hε+1 := by
  have hlo := leastHalvings_half_lt x ε hε hx
  have hhi : leastHalvings x ε hε ≤ leastHalvings (x/2) ε hε+1 := by
    apply leastHalvings_le
    have hs := leastHalvings_spec (x/2) ε hε
    rw [pow_succ]
    convert hs using 1 <;> field_simp <;> ring
  omega

def scalarHalving (x ε : ℝ) (hε : 0 < ε) : ArithmeticProgram ℕ :=
  .branch x ε
    (fun _ => .pure 0)
    (fun hx => .certifiedStep (.div x 2) (fun y => do
      let n ← scalarHalving y.val ε hε
      .pure (n+1)))
termination_by leastHalvings x ε hε
decreasing_by
  rw [y.property]
  exact leastHalvings_half_lt x ε hε hx

theorem scalarHalving_checked (x ε : ℝ) (hε : 0 < ε) :
    (scalarHalving x ε hε).eval = leastHalvings x ε hε ∧
    (scalarHalving x ε hε).work = 2*leastHalvings x ε hε+1 ∧
    (scalarHalving x ε hε).admissible := by
  have aux : ∀ n : ℕ, ∀ x : ℝ, leastHalvings x ε hε = n →
      (scalarHalving x ε hε).eval = leastHalvings x ε hε ∧
      (scalarHalving x ε hε).work = 2*leastHalvings x ε hε+1 ∧
      (scalarHalving x ε hε).admissible := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hn
      rw [scalarHalving]
      by_cases hx : x ≤ ε
      · simp [ArithmeticProgram.eval, ArithmeticProgram.work, ArithmeticProgram.admissible,
          hx, leastHalvings_zero x ε hε hx]
      · have hlt := leastHalvings_half_lt x ε hε hx
        have hr := leastHalvings_half_succ x ε hε hx
        have hh := ih (leastHalvings (x/2) ε hε) (by omega) (x/2) rfl
        simp only [ArithmeticProgram.eval, ArithmeticProgram.work, ArithmeticProgram.admissible,
          dif_neg hx, ArithmeticOp.eval, ArithmeticOp.admissible, eval_bind, work_bind,
          admissible_bind, ArithmeticProgram.eval_pure, ArithmeticProgram.work_pure,
          ArithmeticProgram.admissible_pure, and_true, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, true_and]
        rw [hh.1, hh.2.1, hr]
        exact ⟨rfl, by omega, hh.2.2⟩
  exact aux (leastHalvings x ε hε) x rfl

end
end HierarchicalAbsoluteSpectral
