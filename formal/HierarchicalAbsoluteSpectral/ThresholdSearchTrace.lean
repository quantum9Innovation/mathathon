import HierarchicalAbsoluteSpectral.ThresholdSearchCapped

/-! Adaptive correctness requires valid answers only at the thresholds
actually visited. A finite product argument must not be replaced by the
stronger assertion that one Gaussian tape works for every real threshold. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure
variable {cap : ℕ}

def thresholdSearchTraceGood (query : Fin cap → ℝ → ThresholdDecision)
    (target ε : ℝ) (near : ℝ → Prop) :
    (fuel offset : ℕ) → offset+fuel≤cap → ℝ → ℝ → Prop
  | 0, _, _, _, _ => True
  | fuel+1, offset, hcap, l, u =>
    if u-l≤ε*l then True else
      let t := (l+u)/2
      match query ⟨offset,by omega⟩ t with
      | .below => t≤target ∧ thresholdSearchTraceGood query target ε near fuel (offset+1) (by omega) t u
      | .above => target≤t ∧ thresholdSearchTraceGood query target ε near fuel (offset+1) (by omega) l t
      | .near => near t

theorem thresholdSearchIndexedValue_correct_of_trace (query : Fin cap → ℝ → ThresholdDecision)
    (target ε : ℝ) (near : ℝ → Prop) (hε : 0≤ε)
    (fuel offset : ℕ) (hcap : offset+fuel≤cap) (l u : ℝ)
    (hl : 0<l) (hlo : l≤target) (hhi : target≤u)
    (hbudget : u-l≤(2:ℝ)^fuel*ε*l)
    (hgood : thresholdSearchTraceGood query target ε near fuel offset hcap l u) :
    ThresholdSearchConclusion target ε near
      (thresholdSearchIndexedValue query ε fuel offset hcap l u) := by
  have finish (a b : ℝ) (ha : 0<a) (hal : a≤target) (hbu : target≤b)
      (hw : b-a≤ε*a) : ThresholdSearchConclusion target ε near (.bracket a b) := by
    refine ⟨ha,hal,hbu,hw,?_⟩
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hal)]
  induction fuel generalizing offset l u with
  | zero =>
    apply finish l u hl hlo hhi
    simpa only [pow_zero,one_mul] using hbudget
  | succ fuel ih =>
    rw [thresholdSearchIndexedValue]
    simp only [thresholdSearchTraceGood] at hgood
    split_ifs with hstop
    · exact finish l u hl hlo hhi hstop
    · rw [if_neg hstop] at hgood
      let t := (l+u)/2
      have hlt : l≤t := by dsimp [t]; linarith
      have htu : t≤u := by dsimp [t]; linarith
      have ht : 0<t := hl.trans_le hlt
      have hc : u-l≤2*((2:ℝ)^fuel*ε*l) := by
        rw [pow_succ] at hbudget
        nlinarith only [hbudget]
      change ThresholdSearchConclusion target ε near
        (match query ⟨offset,by omega⟩ t with
          | .below => thresholdSearchIndexedValue query ε fuel (offset+1) (by omega) t u
          | .above => thresholdSearchIndexedValue query ε fuel (offset+1) (by omega) l t
          | .near => .near t)
      change (match query ⟨offset,by omega⟩ t with
        | .below => t≤target ∧ thresholdSearchTraceGood query target ε near fuel (offset+1) (by omega) t u
        | .above => target≤t ∧ thresholdSearchTraceGood query target ε near fuel (offset+1) (by omega) l t
        | .near => near t) at hgood
      cases hq : query ⟨offset,by omega⟩ t with
      | below =>
        rw [hq] at hgood
        exact ih (offset+1) (by omega) t u ht hgood.1 hhi (by
          have he := mul_le_mul_of_nonneg_left hlt
            (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) fuel) hε)
          dsimp [t] at *
          nlinarith) hgood.2
      | above =>
        rw [hq] at hgood
        exact ih (offset+1) (by omega) l t hl hlo hgood.1
          (by dsimp [t] at *; nlinarith) hgood.2
      | near =>
        rw [hq] at hgood
        exact ⟨ht,hgood⟩

theorem thresholdSearchIndexed_correct_of_trace
    (query : Fin cap → ℝ → ArithmeticProgram ThresholdDecision)
    (target ε : ℝ) (near : ℝ → Prop) (hε : 0≤ε)
    (fuel offset : ℕ) (hcap : offset+fuel≤cap) (l u : ℝ)
    (hl : 0<l) (hlo : l≤target) (hhi : target≤u)
    (hbudget : u-l≤(2:ℝ)^fuel*ε*l)
    (hgood : thresholdSearchTraceGood (fun i t => (query i t).eval) target ε near fuel offset hcap l u) :
    ThresholdSearchConclusion target ε near
      (thresholdSearchIndexed query ε fuel offset hcap l u).eval := by
  rw [thresholdSearchIndexed_eval]
  exact thresholdSearchIndexedValue_correct_of_trace _ target ε near hε fuel offset hcap l u hl hlo hhi hbudget hgood

/-- Agreement is also required only along the ideal execution path. -/
def thresholdSearchTraceAgree (actual ideal : Fin cap → ℝ → ThresholdDecision) (ε : ℝ) :
    (fuel offset : ℕ) → offset+fuel≤cap → ℝ → ℝ → Prop
  | 0, _, _, _, _ => True
  | fuel+1, offset, hcap, l, u =>
    if u-l≤ε*l then True else
      let t := (l+u)/2
      actual ⟨offset,by omega⟩ t=ideal ⟨offset,by omega⟩ t ∧
      match ideal ⟨offset,by omega⟩ t with
      | .below => thresholdSearchTraceAgree actual ideal ε fuel (offset+1) (by omega) t u
      | .above => thresholdSearchTraceAgree actual ideal ε fuel (offset+1) (by omega) l t
      | .near => True

theorem thresholdSearchIndexedValue_eq_of_trace (actual ideal : Fin cap → ℝ → ThresholdDecision)
    (ε : ℝ) (fuel offset : ℕ) (hcap : offset+fuel≤cap) (l u : ℝ)
    (hagree : thresholdSearchTraceAgree actual ideal ε fuel offset hcap l u) :
    thresholdSearchIndexedValue actual ε fuel offset hcap l u=
      thresholdSearchIndexedValue ideal ε fuel offset hcap l u := by
  induction fuel generalizing offset l u with
  | zero => rfl
  | succ fuel ih =>
    simp only [thresholdSearchIndexedValue,thresholdSearchTraceAgree] at hagree ⊢
    split_ifs with hstop
    · rfl
    · rw [if_neg hstop] at hagree
      rw [hagree.1]
      cases hd : ideal ⟨offset,by omega⟩ ((l+u)/2) with
      | below => rw [hd] at hagree; exact ih _ _ _ _ hagree.2
      | above => rw [hd] at hagree; exact ih _ _ _ _ hagree.2
      | near => rfl

end
end HierarchicalAbsoluteSpectral
