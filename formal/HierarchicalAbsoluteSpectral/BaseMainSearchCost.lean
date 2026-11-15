import HierarchicalAbsoluteSpectral.BaseMainQueryCost
import HierarchicalAbsoluteSpectral.ThresholdSearchCapped

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure
variable {cap : ℕ}

theorem thresholdSearchIndexed_work_le_all
    (query : Fin cap → ℝ → ArithmeticProgram ThresholdDecision)
    (cost : ℕ) (hquery : ∀ i t, (query i t).work ≤ cost) (ε : ℝ)
    (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ) :
    (thresholdSearchIndexed query ε fuel offset hcap l u).work ≤ fuel*(5+cost) := by
  induction fuel generalizing offset l u with
  | zero => simp [thresholdSearchIndexed]
  | succ n ih =>
    rw [Nat.succ_mul]
    simp only [thresholdSearchIndexed,work_bind,work_sub,work_mul,eval_sub,eval_mul,ArithmeticProgram.work]
    split_ifs
    · omega
    · simp only [work_bind,work_add,work_div,eval_add,eval_div]
      have hq := hquery (⟨offset,by omega⟩ : Fin cap) ((l+u)/2)
      cases (query ⟨offset,by omega⟩ ((l+u)/2)).eval
      · have hh := ih (offset+1) (by omega) ((l+u)/2) u
        dsimp only
        omega
      · have hh := ih (offset+1) (by omega) l ((l+u)/2)
        dsimp only
        omega
      · simp only [ArithmeticProgram.work]
        omega

theorem thresholdSearchCapped_work_le_all (x ε : ℝ) (hε : 0 < ε)
    (query : Fin (leastHalvings x ε hε) → ℝ → ArithmeticProgram ThresholdDecision)
    (cost : ℕ) (hquery : ∀ i t, (query i t).work ≤ cost) (l u : ℝ) :
    (thresholdSearchCapped x ε hε query l u).work ≤ 1+leastHalvings x ε hε*(7+cost) := by
  simp only [thresholdSearchCapped,work_bind,certify_work]
  have hn : (scalarHalving x ε hε).certify.eval.val=leastHalvings x ε hε :=
    (scalarHalving x ε hε).certify.eval.property.trans (scalarHalving_checked x ε hε).1
  have hs := thresholdSearchIndexed_work_le_all query cost hquery ε
    (scalarHalving x ε hε).certify.eval.val 0 (by rw [hn]; omega) l u
  have hs' := hs.trans_eq (congrArg (fun v : ℕ => v*(5+cost)) hn)
  have hw := (scalarHalving_checked x ε hε).2.1
  nlinarith only [hs',hw]

end
end HierarchicalAbsoluteSpectral
