import HierarchicalAbsoluteSpectral.ThresholdSearchCapped
import HierarchicalAbsoluteSpectral.ThresholdMassDecision

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
variable {cap k : ℕ}

def ThresholdSearchResult.selected : ThresholdSearchResult → ℝ
  | .bracket _ upper => upper
  | .near t => t

theorem thresholdSearchIndexedValue_selected_positive
    (query : Fin cap → ℝ → ThresholdDecision) (ε : ℝ)
    (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ)
    (hl : 0 < l) (hlu : l ≤ u) :
    0 < (thresholdSearchIndexedValue query ε fuel offset hcap l u).selected := by
  induction fuel generalizing offset l u with
  | zero => exact hl.trans_le hlu
  | succ fuel ih =>
    simp only [thresholdSearchIndexedValue]
    split_ifs with hstop
    · exact hl.trans_le hlu
    · have hlmid : l ≤ (l+u)/2 := by linarith
      have hmidu : (l+u)/2 ≤ u := by linarith
      have hmid : 0 < (l+u)/2 := hl.trans_le hlmid
      cases query ⟨offset,by omega⟩ ((l+u)/2) with
      | below => exact ih (offset+1) (by omega) _ u hmid hmidu
      | above => exact ih (offset+1) (by omega) l _ hl hlmid
      | near => exact hmid

theorem thresholdSearchCapped_selected_positive (x ε : ℝ) (hε : 0 < ε)
    (query : Fin (leastHalvings x ε hε) → ℝ → ArithmeticProgram ThresholdDecision)
    (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) :
    0 < (thresholdSearchCapped x ε hε query l u).eval.selected := by
  rw [thresholdSearchCapped_eval,thresholdSearchIndexed_eval]
  exact thresholdSearchIndexedValue_selected_positive _ ε _ _ _ l u hl hlu

theorem mass_threshold_above_target_tail (Q R Rb : Core k) (hQ : Q.IsHermitian)
    (hR : IsUnit R.det) (hRb : IsUnit Rb.det) (t : ℝ) (j : Fin k)
    (htarget : orderedEigenvalue (Rbᵀ*Q*Rb) (normalized_isHermitian Rb Q hQ.eq) j ≤ t) :
    orderedEigenvalue (massThresholdOperator Q R Rb t)
      (massThresholdOperator_isHermitian Q R Rb hQ t) j ≤ 1 := by
  by_contra hh
  have hb := (massThresholdOperator_below_iff Q R Rb hQ hR hRb t j).mp (lt_of_not_ge hh)
  exact (not_lt_of_ge htarget) hb

theorem ThresholdSearchConclusion.selected_bound
    (target X : ℝ) (near : ℝ → Prop) (result : ThresholdSearchResult)
    (hgood : ThresholdSearchConclusion target X near result) :
    match result with
    | .near t => 0 < t ∧ near t
    | .bracket _ _ => 0 < result.selected ∧ target ≤ result.selected ∧
        result.selected ≤ (1+X)*target := by
  cases result with
  | near t => exact hgood
  | bracket l u => exact ⟨hgood.1.trans_le (hgood.2.1.trans hgood.2.2.1),hgood.2.2.1,hgood.2.2.2.2⟩

end
end HierarchicalAbsoluteSpectral
