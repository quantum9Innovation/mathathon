import HierarchicalAbsoluteSpectral.ThresholdSearchCapped
import HierarchicalAbsoluteSpectral.ProbabilityInitializerProgram

/-! Counted, indexed bisection with explicit propagation of failed exact
tests. The query's Boolean means that the midpoint is below the target. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open ArithmeticProgram hiding pure

variable {cap : ℕ}

def ExactGramAppendixSearchConclusion (target ε : ℝ) : InitializerResult → Prop
  | .exact => target = 0
  | .bracket l u => 0 < l ∧ l ≤ target ∧ target ≤ u ∧
      u-l ≤ ε*l ∧ u ≤ (1+ε)*target

def exactGramAppendixSearchIndexedValue (query : Fin cap → ℝ → Option Bool) (ε : ℝ) :
    (fuel offset : ℕ) → offset+fuel ≤ cap → ℝ → ℝ → Option InitializerResult
  | 0, _, _, l, u => some (.bracket l u)
  | fuel+1, offset, hcap, l, u =>
      if u-l ≤ ε*l then some (.bracket l u) else
        let t := (l+u)/2
        match query ⟨offset, by omega⟩ t with
        | none => none
        | some true => exactGramAppendixSearchIndexedValue query ε fuel (offset+1) (by omega) t u
        | some false => exactGramAppendixSearchIndexedValue query ε fuel (offset+1) (by omega) l t

/-- Every queried midpoint consumes a new tape index. An unsuccessful
inertia test stops the computation and returns `none`. -/
def exactGramAppendixSearchIndexed
    (query : Fin cap → ℝ → ArithmeticProgram (Option Bool)) (ε : ℝ) :
    (fuel offset : ℕ) → offset+fuel ≤ cap → ℝ → ℝ →
      ArithmeticProgram (Option InitializerResult)
  | 0, _, _, l, u => .pure (some (.bracket l u))
  | fuel+1, offset, hcap, l, u => do
      let width ← sub u l
      let tolerance ← mul ε l
      .branch width tolerance
        (fun _ => .pure (some (.bracket l u)))
        (fun _ => do
          let total ← add l u
          let t ← div total 2
          let answer? ← query ⟨offset, by omega⟩ t
          match answer? with
          | none => .pure none
          | some true => exactGramAppendixSearchIndexed query ε fuel (offset+1) (by omega) t u
          | some false => exactGramAppendixSearchIndexed query ε fuel (offset+1) (by omega) l t)

theorem exactGramAppendixSearchIndexed_eval
    (query : Fin cap → ℝ → ArithmeticProgram (Option Bool)) (ε : ℝ)
    (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ) :
    (exactGramAppendixSearchIndexed query ε fuel offset hcap l u).eval =
      exactGramAppendixSearchIndexedValue (fun i t => (query i t).eval)
        ε fuel offset hcap l u := by
  induction fuel generalizing offset l u with
  | zero => rfl
  | succ fuel ih =>
      simp only [exactGramAppendixSearchIndexed, eval_bind, eval_sub, eval_mul,
        ArithmeticProgram.eval, exactGramAppendixSearchIndexedValue]
      split_ifs
      · rfl
      · simp only [eval_add, eval_div]
        cases (query ⟨offset, by omega⟩ ((l+u)/2)).eval with
        | none => rfl
        | some b => cases b <;> exact ih _ _ _ _

theorem exactGramAppendixSearchIndexedValue_correct
    (query : Fin cap → ℝ → Option Bool) (target ε : ℝ)
    (hsound : ∀ i t b, query i t = some b → (b = true ↔ t < target))
    (hε : 0 ≤ ε) (fuel offset : ℕ) (hcap : offset+fuel ≤ cap)
    (l u : ℝ) (hl : 0 < l) (hlo : l ≤ target) (hhi : target ≤ u)
    (hwidth : u-l ≤ (2:ℝ)^fuel*ε*l) :
    ∀ out, exactGramAppendixSearchIndexedValue query ε fuel offset hcap l u = some out →
      ExactGramAppendixSearchConclusion target ε out := by
  have finish (a b : ℝ) (ha : 0 < a) (hal : a ≤ target) (hbu : target ≤ b)
      (hw : b-a ≤ ε*a) : ExactGramAppendixSearchConclusion target ε (.bracket a b) := by
    refine ⟨ha, hal, hbu, hw, ?_⟩
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hal)]
  induction fuel generalizing offset l u with
  | zero =>
      intro out hout
      have heq : InitializerResult.bracket l u = out := Option.some.inj hout
      subst out
      apply finish l u hl hlo hhi
      simpa only [pow_zero, one_mul] using hwidth
  | succ fuel ih =>
      intro out hout
      rw [exactGramAppendixSearchIndexedValue] at hout
      split_ifs at hout with hstop
      · have heq : InitializerResult.bracket l u = out := Option.some.inj hout
        subst out
        exact finish l u hl hlo hhi hstop
      · let t := (l+u)/2
        have hlt : l ≤ t := by dsimp [t]; linarith
        have htu : t ≤ u := by dsimp [t]; linarith
        have ht : 0 < t := hl.trans_le hlt
        have hc : u-l ≤ 2*((2:ℝ)^fuel*ε*l) := by
          rw [pow_succ] at hwidth
          nlinarith only [hwidth]
        change (match query ⟨offset, by omega⟩ t with
          | none => none
          | some true => exactGramAppendixSearchIndexedValue query ε fuel (offset+1) (by omega) t u
          | some false => exactGramAppendixSearchIndexedValue query ε fuel (offset+1) (by omega) l t)
            = some out at hout
        cases hq : query ⟨offset, by omega⟩ t with
        | none => simp only [hq] at hout; cases hout
        | some b =>
            have hs := hsound ⟨offset, by omega⟩ t b hq
            cases b with
            | false =>
                have htarget : target ≤ t := le_of_not_gt (by simpa using hs)
                simp only [hq] at hout
                exact ih (offset+1) (by omega) l t hl hlo htarget
                  (by dsimp [t] at *; nlinarith) out hout
            | true =>
                have htarget : t ≤ target := (show t < target by simpa using hs).le
                simp only [hq] at hout
                apply ih (offset+1) (by omega) t u ht htarget hhi ?_ out hout
                have he := mul_le_mul_of_nonneg_left hlt
                  (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) fuel) hε)
                dsimp [t] at *
                nlinarith

theorem exactGramAppendixSearchIndexed_correct
    (query : Fin cap → ℝ → ArithmeticProgram (Option Bool)) (target ε : ℝ)
    (hsound : ∀ i t b, (query i t).eval = some b → (b = true ↔ t < target))
    (hε : 0 ≤ ε) (fuel offset : ℕ) (hcap : offset+fuel ≤ cap)
    (l u : ℝ) (hl : 0 < l) (hlo : l ≤ target) (hhi : target ≤ u)
    (hwidth : u-l ≤ (2:ℝ)^fuel*ε*l) (out : InitializerResult)
    (hout : (exactGramAppendixSearchIndexed query ε fuel offset hcap l u).eval = some out) :
    ExactGramAppendixSearchConclusion target ε out := by
  rw [exactGramAppendixSearchIndexed_eval] at hout
  exact exactGramAppendixSearchIndexedValue_correct _ target ε hsound hε fuel offset hcap
    l u hl hlo hhi hwidth out hout

theorem exactGramAppendixSearchIndexed_admissible
    (query : Fin cap → ℝ → ArithmeticProgram (Option Bool))
    (hquery : ∀ i t, (query i t).admissible) (ε : ℝ)
    (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ) :
    (exactGramAppendixSearchIndexed query ε fuel offset hcap l u).admissible := by
  induction fuel generalizing offset l u with
  | zero => trivial
  | succ fuel ih =>
      simp only [exactGramAppendixSearchIndexed, admissible_bind, admissible_sub,
        admissible_mul, eval_sub, eval_mul, true_and, ArithmeticProgram.admissible]
      split_ifs
      simp only [admissible_add, admissible_div, eval_add, eval_div,
        true_and, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
      refine ⟨hquery _ _, ?_⟩
      cases (query ⟨offset, by omega⟩ ((l+u)/2)).eval with
      | none => trivial
      | some b => cases b <;> exact ih (offset+1) (by omega) _ _

/-- Uniform work on every tape, including a failed query. The five scalar
instructions per attempted midpoint are the same as in `thresholdSearch`. -/
theorem exactGramAppendixSearchIndexed_work_bound
    (query : Fin cap → ℝ → ArithmeticProgram (Option Bool))
    (cost : ℝ) (hcost : 0 ≤ cost)
    (hquery : ∀ i t, ((query i t).work : ℝ) ≤ cost) (ε : ℝ)
    (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ) :
    ((exactGramAppendixSearchIndexed query ε fuel offset hcap l u).work : ℝ) ≤
      (fuel : ℝ)*(5+cost) := by
  induction fuel generalizing offset l u with
  | zero => simp [exactGramAppendixSearchIndexed]
  | succ fuel ih =>
      simp only [exactGramAppendixSearchIndexed, work_bind, work_sub, work_mul,
        eval_sub, eval_mul, ArithmeticProgram.work]
      split_ifs
      · simp only [Nat.cast_zero, Nat.cast_succ]
        nlinarith [mul_nonneg (Nat.cast_nonneg fuel) (show 0 ≤ 5+cost by linarith)]
      · simp only [work_add, work_div, eval_add, eval_div, Nat.cast_add, Nat.cast_succ]
        have hq := hquery ⟨offset, by omega⟩ ((l+u)/2)
        cases hqe : (query ⟨offset, by omega⟩ ((l+u)/2)).eval with
        | none =>
            simp only [work_pure, Nat.cast_zero]
            nlinarith [mul_nonneg (Nat.cast_nonneg fuel) (show 0 ≤ 5+cost by linarith)]
        | some b =>
            cases b with
            | false =>
                dsimp only
                have hh := ih (offset+1) (by omega) l ((l+u)/2)
                nlinarith
            | true =>
                dsimp only
                have hh := ih (offset+1) (by omega) ((l+u)/2) u
                nlinarith

end
end HierarchicalAbsoluteSpectral
