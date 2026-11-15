import HierarchicalAbsoluteSpectral.ThresholdSearchIndexed

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure
variable {cap : ℕ}

/-- The guard keeps every base factorization within its positive-threshold
domain, including random outcomes outside the success event. -/
def positiveThresholdQuery
    (query : Fin cap → {t : ℝ // 0<t} → ArithmeticProgram ThresholdDecision)
    (i : Fin cap) (t : ℝ) : ArithmeticProgram ThresholdDecision :=
  .branch t 0 (fun _ => .pure .below) (fun ht => query i ⟨t,lt_of_not_ge ht⟩)

theorem positiveThresholdQuery_admissible
    (query : Fin cap → {t : ℝ // 0<t} → ArithmeticProgram ThresholdDecision)
    (hquery : ∀ i t, (query i t).admissible) (i : Fin cap) (t : ℝ) :
    (positiveThresholdQuery query i t).admissible := by
  unfold positiveThresholdQuery ArithmeticProgram.admissible
  split_ifs <;> first | trivial | exact hquery _ _

theorem positiveThresholdQuery_eval_pos
    (query : Fin cap → {t : ℝ // 0<t} → ArithmeticProgram ThresholdDecision)
    (i : Fin cap) (t : ℝ) (ht : 0<t) :
    (positiveThresholdQuery query i t).eval = (query i ⟨t,ht⟩).eval := by
  simp only [positiveThresholdQuery,ArithmeticProgram.eval,dif_neg (not_le_of_gt ht)]

theorem positiveThresholdQuery_work_le
    (query : Fin cap → {t : ℝ // 0<t} → ArithmeticProgram ThresholdDecision)
    (cost : ℕ) (hquery : ∀ i t, (query i t).work ≤ cost) (i : Fin cap) (t : ℝ) :
    (positiveThresholdQuery query i t).work ≤ 1+cost := by
  simp only [positiveThresholdQuery,ArithmeticProgram.work]
  split_ifs
  · omega
  · exact Nat.add_le_add_left (hquery _ _) 1

end
end HierarchicalAbsoluteSpectral
