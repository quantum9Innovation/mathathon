import HierarchicalAbsoluteSpectral.ThresholdSearchPositive

/-! The random tape's fixed cap is computed by an executed scalar halving
program, before any adaptive threshold is queried. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

theorem thresholdSearchIndexed_admissible_all {cap : ℕ}
    (query : Fin cap → ℝ → ArithmeticProgram ThresholdDecision)
    (hquery : ∀ i t, (query i t).admissible) (ε : ℝ)
    (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ) :
    (thresholdSearchIndexed query ε fuel offset hcap l u).admissible := by
  induction fuel generalizing offset l u with
  | zero => trivial
  | succ fuel ih =>
    simp only [thresholdSearchIndexed,admissible_bind,admissible_sub,admissible_mul,
      eval_sub,eval_mul,true_and,ArithmeticProgram.admissible]
    split_ifs
    simp only [admissible_bind,admissible_add,admissible_div,eval_add,eval_div,
      true_and,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
    refine ⟨hquery _ _,?_⟩
    cases (query ⟨offset,by omega⟩ ((l+u)/2)).eval
    · exact ih (offset+1) (by omega) _ _
    · exact ih (offset+1) (by omega) _ _
    · trivial

def thresholdSearchCapped (x ε : ℝ) (hε : 0<ε)
    (query : Fin (leastHalvings x ε hε) → ℝ → ArithmeticProgram ThresholdDecision)
    (l u : ℝ) : ArithmeticProgram ThresholdSearchResult := do
  let n ← (scalarHalving x ε hε).certify
  have hn : n.val=leastHalvings x ε hε := n.property.trans (scalarHalving_checked x ε hε).1
  thresholdSearchIndexed query ε n.val 0 (by rw [hn]; omega) l u

theorem thresholdSearchCapped_eval (x ε : ℝ) (hε : 0<ε)
    (query : Fin (leastHalvings x ε hε) → ℝ → ArithmeticProgram ThresholdDecision)
    (l u : ℝ) :
    (thresholdSearchCapped x ε hε query l u).eval =
      (thresholdSearchIndexed query ε (leastHalvings x ε hε) 0 (by omega) l u).eval := by
  simp only [thresholdSearchCapped,eval_bind]
  have hn : (scalarHalving x ε hε).certify.eval.val=leastHalvings x ε hε :=
    (scalarHalving x ε hε).certify.eval.property.trans (scalarHalving_checked x ε hε).1
  simp only [hn]

theorem thresholdSearchCapped_correct (x target ε : ℝ) (hε : 0<ε) (near : ℝ → Prop)
    (query : Fin (leastHalvings x ε hε) → ℝ → ArithmeticProgram ThresholdDecision)
    (hsound : ∀ i, ThresholdSearchSound (fun t => (query i t).eval) target near)
    (l u : ℝ) (hl : 0<l) (hlo : l≤target) (hhi : target≤u)
    (hwidth : u-l≤x*l) :
    ThresholdSearchConclusion target ε near (thresholdSearchCapped x ε hε query l u).eval := by
  rw [thresholdSearchCapped_eval]
  apply thresholdSearchIndexed_correct query target ε near hsound hε.le _ _ _ l u hl hlo hhi
  have hs := (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) (leastHalvings x ε hε))).mp
    (leastHalvings_spec x ε hε)
  exact hwidth.trans (by nlinarith [mul_le_mul_of_nonneg_right hs hl.le])

theorem thresholdSearchCapped_admissible (x ε : ℝ) (hε : 0<ε)
    (query : Fin (leastHalvings x ε hε) → ℝ → ArithmeticProgram ThresholdDecision)
    (hquery : ∀ i t, 0<t → (query i t).admissible)
    (l u : ℝ) (hl : 0<l) (hlu : l≤u) :
    (thresholdSearchCapped x ε hε query l u).admissible := by
  simp only [thresholdSearchCapped,admissible_bind,certify_admissible]
  refine ⟨(scalarHalving_checked x ε hε).2.2,?_⟩
  exact thresholdSearchIndexed_admissible query hquery ε _ _ _ l u hl hlu

theorem thresholdSearchCapped_admissible_all (x ε : ℝ) (hε : 0 < ε)
    (query : Fin (leastHalvings x ε hε) → ℝ → ArithmeticProgram ThresholdDecision)
    (hquery : ∀ i t, (query i t).admissible) (l u : ℝ) :
    (thresholdSearchCapped x ε hε query l u).admissible := by
  simp only [thresholdSearchCapped,admissible_bind,certify_admissible]
  exact ⟨(scalarHalving_checked x ε hε).2.2,
    thresholdSearchIndexed_admissible_all query hquery ε _ _ _ l u⟩

theorem thresholdSearchCapped_work_le (x ε : ℝ) (hε : 0<ε)
    (query : Fin (leastHalvings x ε hε) → ℝ → ArithmeticProgram ThresholdDecision)
    (cost : ℕ) (hquery : ∀ i t, 0<t → (query i t).work≤cost)
    (l u : ℝ) (hl : 0<l) (hlu : l≤u) :
    (thresholdSearchCapped x ε hε query l u).work ≤ 1+leastHalvings x ε hε*(7+cost) := by
  simp only [thresholdSearchCapped,work_bind,certify_work]
  have hn : (scalarHalving x ε hε).certify.eval.val=leastHalvings x ε hε :=
    (scalarHalving x ε hε).certify.eval.property.trans (scalarHalving_checked x ε hε).1
  have hs := thresholdSearchIndexed_work_le query cost hquery ε (scalarHalving x ε hε).certify.eval.val 0
    (by rw [hn]; omega) l u hl hlu
  have hs' := hs.trans_eq (congrArg (fun v : ℕ => v*(5+cost)) hn)
  have hw := (scalarHalving_checked x ε hε).2.1
  nlinarith only [hs',hw]

end
end HierarchicalAbsoluteSpectral
