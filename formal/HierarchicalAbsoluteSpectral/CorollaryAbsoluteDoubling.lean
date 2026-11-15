import HierarchicalAbsoluteSpectral.CorollaryAbsoluteRank
import Mathlib.Data.Nat.Log

/-! A finite, executed rank-doubling controller. Its inputs are programs for
attempts and an explicit fallback, not a rank to be discovered. The later
caller supplies the actual hierarchical query and carried-output programs. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped Matrix.Norms.L2Operator
variable {n m p : ℕ}

def absoluteRankAt : ℕ → ℕ
  | 0 => 0
  | i+1 => 2^i

@[simp] theorem absoluteRankAt_zero : absoluteRankAt 0 = 0 := rfl
@[simp] theorem absoluteRankAt_succ (i : ℕ) : absoluteRankAt (i+1) = 2^i := rfl

theorem absoluteRankAt_succ_le {i s : ℕ} (hs : absoluteRankAt i < s) :
    absoluteRankAt (i+1) ≤ 2*s := by
  cases i with
  | zero => simp only [absoluteRankAt] at *; omega
  | succ i => simp only [absoluteRankAt,pow_succ] at *; omega

structure AbsoluteOutput (n p m : ℕ) where
  attemptRank : ℕ
  attemptRank_le : attemptRank ≤ m
  result : FixedRankOutput n p attemptRank
  usedFallback : Bool

def absoluteFallbackOutput (out : FixedRankOutput n p m) : AbsoluteOutput n p m :=
  ⟨m,le_rfl,out,true⟩

/-- Each `none` executes the next doubled rank. At or beyond the core
dimension the actual fallback executes before any out-of-range query. -/
def absoluteDoublingLoop
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m)) :
    ℕ → ℕ → ArithmeticProgram (AbsoluteOutput n p m)
  | 0, _ => do
    let out ← fallback
    .pure (absoluteFallbackOutput out)
  | fuel+1, offset =>
    if hcap : m ≤ absoluteRankAt offset then do
      let out ← fallback
      .pure (absoluteFallbackOutput out)
    else do
      let out? ← attempt (absoluteRankAt offset)
      match out? with
      | some out => .pure ⟨absoluteRankAt offset,le_of_lt (Nat.lt_of_not_ge hcap),out,false⟩
      | none => absoluteDoublingLoop attempt fallback fuel (offset+1)

def absoluteDoublingProgram
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m)) :
    ArithmeticProgram (AbsoluteOutput n p m) :=
  absoluteDoublingLoop attempt fallback (Nat.log 2 m+2) 0

@[simp] theorem absoluteDoublingLoop_eval_zero
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m)) (offset : ℕ) :
    (absoluteDoublingLoop attempt fallback 0 offset).eval = absoluteFallbackOutput fallback.eval :=
  ArithmeticProgram.eval_bind _ _

theorem absoluteDoublingLoop_eval_succ
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m)) (fuel offset : ℕ) :
    (absoluteDoublingLoop attempt fallback (fuel+1) offset).eval =
      if hcap : m ≤ absoluteRankAt offset then absoluteFallbackOutput fallback.eval
      else match (attempt (absoluteRankAt offset)).eval with
      | some out => ⟨absoluteRankAt offset,le_of_lt (Nat.lt_of_not_ge hcap),out,false⟩
      | none => (absoluteDoublingLoop attempt fallback fuel (offset+1)).eval := by
  conv_lhs => unfold absoluteDoublingLoop
  by_cases hm : m ≤ absoluteRankAt offset
  · simp only [dif_pos hm,eval_bind,eval_pure]
  · simp only [dif_neg hm,eval_bind]
    cases (attempt (absoluteRankAt offset)).eval <;> rfl

theorem absoluteDoublingLoop_admissible
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m))
    (ha : ∀ s, (attempt s).admissible) (hf : fallback.admissible)
    (fuel offset : ℕ) :
    (absoluteDoublingLoop attempt fallback fuel offset).admissible := by
  induction fuel generalizing offset with
  | zero => simpa only [absoluteDoublingLoop,admissible_bind,admissible_pure,and_true] using hf
  | succ fuel ih =>
    simp only [absoluteDoublingLoop]
    split_ifs
    · simpa only [admissible_bind,admissible_pure,and_true] using hf
    · simp only [admissible_bind,ha,true_and]
      split
      · trivial
      · exact ih _

/-- Deterministic stopping-rank reduction. The caller must establish that
its *computed* attempt cannot advance at/above the true slack rank. -/
theorem absoluteDoublingLoop_rank_bound
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m)) (s fuel offset : ℕ)
    (hstop : ∀ r, s ≤ r → r < m → (attempt r).eval ≠ none)
    (hr : absoluteRankAt offset ≤ 2*s)
    (hcap : m ≤ absoluteRankAt (offset+fuel)) :
    (absoluteDoublingLoop attempt fallback fuel offset).eval.attemptRank ≤ 2*s := by
  induction fuel generalizing offset with
  | zero =>
    simp only [Nat.add_zero] at hcap
    simpa only [absoluteDoublingLoop,eval_bind,eval_pure,absoluteFallbackOutput] using hcap.trans hr
  | succ fuel ih =>
    simp only [absoluteDoublingLoop]
    split_ifs with hm
    · simpa only [eval_bind,eval_pure,absoluteFallbackOutput] using hm.trans hr
    · simp only [eval_bind]
      cases ho : (attempt (absoluteRankAt offset)).eval with
      | some out => simpa only [eval_pure] using hr
      | none =>
        have hlt : absoluteRankAt offset < s := by
          by_contra hh
          exact hstop _ (Nat.le_of_not_gt hh) (Nat.lt_of_not_ge hm) ho
        exact ih (offset+1) (absoluteRankAt_succ_le hlt) (by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hcap)

theorem absoluteDoublingProgram_rank_bound
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m)) (s : ℕ)
    (hstop : ∀ r, s ≤ r → r < m → (attempt r).eval ≠ none) :
    (absoluteDoublingProgram attempt fallback).eval.attemptRank ≤ 2*s := by
  apply absoluteDoublingLoop_rank_bound attempt fallback s _ _ hstop (Nat.zero_le _)
  simpa only [Nat.zero_add,absoluteRankAt_succ] using
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) m).le

theorem absoluteDoublingLoop_work_succ
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m)) (fuel offset : ℕ) :
    (absoluteDoublingLoop attempt fallback (fuel+1) offset).work =
      if m ≤ absoluteRankAt offset then fallback.work else
        (attempt (absoluteRankAt offset)).work+
          (match (attempt (absoluteRankAt offset)).eval with
          | some _ => 0
          | none => (absoluteDoublingLoop attempt fallback fuel (offset+1)).work) := by
  conv_lhs => unfold absoluteDoublingLoop
  by_cases hm : m ≤ absoluteRankAt offset
  · simp only [dif_pos hm,if_pos hm,work_bind,work_pure,Nat.add_zero]
  · simp only [dif_neg hm,if_neg hm,work_bind]
    cases (attempt (absoluteRankAt offset)).eval <;> rfl

/-- On a small-slack stopping event the dense full-product fallback never
executes, and only low-rank attempts contribute work. The cap is logarithmic. -/
theorem absoluteDoublingLoop_small_work
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m)) (s fuel offset K : ℕ)
    (hstop : ∀ r, s ≤ r → r < m → (attempt r).eval ≠ none)
    (hsmall : 2*s < m)
    (hwork : ∀ r ≤ 2*s, (attempt r).work ≤ K)
    (hr : absoluteRankAt offset ≤ 2*s)
    (hcap : m ≤ absoluteRankAt (offset+fuel)) :
    (absoluteDoublingLoop attempt fallback fuel offset).work ≤ fuel*K ∧
      (absoluteDoublingLoop attempt fallback fuel offset).eval.usedFallback=false := by
  induction fuel generalizing offset with
  | zero => simp only [Nat.add_zero] at hcap; omega
  | succ fuel ih =>
    have hm : ¬m ≤ absoluteRankAt offset := by omega
    rw [absoluteDoublingLoop_work_succ,if_neg hm,absoluteDoublingLoop_eval_succ,dif_neg hm]
    cases ho : (attempt (absoluteRankAt offset)).eval with
    | some out =>
      refine ⟨?_,rfl⟩
      have hw := hwork _ hr
      simp only [Nat.add_zero]
      nlinarith
    | none =>
      have hlt : absoluteRankAt offset < s := by
        by_contra hh
        exact hstop _ (Nat.le_of_not_gt hh) (Nat.lt_of_not_ge hm) ho
      obtain ⟨hw,hf⟩ := ih (offset+1) (absoluteRankAt_succ_le hlt)
        (by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hcap)
      exact ⟨by have := hwork _ hr; nlinarith,hf⟩

theorem absoluteDoublingProgram_small_work
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m)) (s K : ℕ)
    (hstop : ∀ r, s ≤ r → r < m → (attempt r).eval ≠ none)
    (hsmall : 2*s < m)
    (hwork : ∀ r ≤ 2*s, (attempt r).work ≤ K) :
    (absoluteDoublingProgram attempt fallback).work ≤ (Nat.log 2 m+2)*K ∧
      (absoluteDoublingProgram attempt fallback).eval.usedFallback=false := by
  apply absoluteDoublingLoop_small_work attempt fallback s _ _ K hstop hsmall hwork (Nat.zero_le _)
  simpa only [Nat.zero_add,absoluteRankAt_succ] using
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) m).le

theorem absoluteDoublingLoop_work_cap
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m)) (fuel offset K : ℕ)
    (hwork : ∀ r < m, (attempt r).work ≤ K) :
    (absoluteDoublingLoop attempt fallback fuel offset).work ≤ fuel*K+fallback.work := by
  induction fuel generalizing offset with
  | zero => simp only [absoluteDoublingLoop,work_bind,work_pure,Nat.add_zero,Nat.zero_mul,Nat.zero_add]
  | succ fuel ih =>
    rw [absoluteDoublingLoop_work_succ]
    split_ifs with hm
    · omega
    · have hw := hwork _ (Nat.lt_of_not_ge hm)
      cases (attempt (absoluteRankAt offset)).eval with
      | some _ => simp only [Nat.add_zero]; nlinarith
      | none => have hh := ih (offset+1); nlinarith

/-- Error and stopping rank are transferred on the same pointwise event. -/
theorem absoluteDoublingLoop_error
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m))
    (M : Matrix (Fin n) (Fin p) ℝ) (e : ℝ)
    (ha : ∀ s out, (attempt s).eval = some out → ‖M-out.product‖ ≤ e)
    (hf : ‖M-fallback.eval.product‖ ≤ e) (fuel offset : ℕ) :
    ‖M-(absoluteDoublingLoop attempt fallback fuel offset).eval.result.product‖ ≤ e := by
  induction fuel generalizing offset with
  | zero => rw [absoluteDoublingLoop_eval_zero]; exact hf
  | succ fuel ih =>
    rw [absoluteDoublingLoop_eval_succ]
    by_cases hm : m ≤ absoluteRankAt offset
    · rw [dif_pos hm]; exact hf
    · rw [dif_neg hm]
      cases ho : (attempt (absoluteRankAt offset)).eval with
      | some out => exact ha _ out ho
      | none => exact ih _

end
end HierarchicalAbsoluteSpectral
