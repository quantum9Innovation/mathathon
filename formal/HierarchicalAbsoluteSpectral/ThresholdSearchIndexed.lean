import HierarchicalAbsoluteSpectral.ThresholdSearchCap

/-! Each threshold call consumes a distinct, bounded query index. This
version is used by the main program with an independent finite Gaussian
tape at each index, including under adaptive threshold selection. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure
variable {cap : ℕ}

def thresholdSearchIndexedValue (query : Fin cap → ℝ → ThresholdDecision) (ε : ℝ) :
    (fuel offset : ℕ) → offset+fuel ≤ cap → ℝ → ℝ → ThresholdSearchResult
  | 0, _, _, l, u => .bracket l u
  | n+1, offset, hcap, l, u =>
    if u-l ≤ ε*l then .bracket l u else
      let t := (l+u)/2
      match query ⟨offset,by omega⟩ t with
      | .below => thresholdSearchIndexedValue query ε n (offset+1) (by omega) t u
      | .above => thresholdSearchIndexedValue query ε n (offset+1) (by omega) l t
      | .near => .near t

def thresholdSearchIndexed (query : Fin cap → ℝ → ArithmeticProgram ThresholdDecision) (ε : ℝ) :
    (fuel offset : ℕ) → offset+fuel ≤ cap → ℝ → ℝ → ArithmeticProgram ThresholdSearchResult
  | 0, _, _, l, u => .pure (.bracket l u)
  | n+1, offset, hcap, l, u => do
    let width ← sub u l
    let tolerance ← mul ε l
    .branch width tolerance
      (fun _ => .pure (.bracket l u))
      (fun _ => do
        let total ← add l u
        let t ← div total 2
        let answer ← query ⟨offset,by omega⟩ t
        match answer with
        | .below => thresholdSearchIndexed query ε n (offset+1) (by omega) t u
        | .above => thresholdSearchIndexed query ε n (offset+1) (by omega) l t
        | .near => .pure (.near t))

theorem thresholdSearchIndexed_eval (query : Fin cap → ℝ → ArithmeticProgram ThresholdDecision)
    (ε : ℝ) (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ) :
    (thresholdSearchIndexed query ε fuel offset hcap l u).eval =
      thresholdSearchIndexedValue (fun i t => (query i t).eval) ε fuel offset hcap l u := by
  induction fuel generalizing offset l u with
  | zero => rfl
  | succ n ih =>
    simp only [thresholdSearchIndexed, eval_bind, eval_sub, eval_mul, ArithmeticProgram.eval,
      thresholdSearchIndexedValue]
    split_ifs
    · rfl
    · simp only [eval_bind, eval_add, eval_div]
      cases (query ⟨offset,by omega⟩ ((l+u)/2)).eval <;> simp only [ih, ArithmeticProgram.eval]

theorem thresholdSearchIndexedValue_correct (query : Fin cap → ℝ → ThresholdDecision)
    (target ε : ℝ) (near : ℝ → Prop)
    (hsound : ∀ i, ThresholdSearchSound (query i) target near) (hε : 0 ≤ ε)
    (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ)
    (hl : 0 < l) (hlo : l ≤ target) (hhi : target ≤ u)
    (hbudget : u-l ≤ (2:ℝ)^fuel*ε*l) :
    ThresholdSearchConclusion target ε near
      (thresholdSearchIndexedValue query ε fuel offset hcap l u) := by
  have finish (a b : ℝ) (ha : 0 < a) (hal : a ≤ target) (hbu : target ≤ b)
      (hw : b-a ≤ ε*a) : ThresholdSearchConclusion target ε near (.bracket a b) := by
    refine ⟨ha,hal,hbu,hw,?_⟩
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hal)]
  induction fuel generalizing offset l u with
  | zero =>
    apply finish l u hl hlo hhi
    simpa only [pow_zero, one_mul] using hbudget
  | succ n ih =>
    rw [thresholdSearchIndexedValue]
    split_ifs with hstop
    · exact finish l u hl hlo hhi hstop
    · let t := (l+u)/2
      have hlt : l ≤ t := by dsimp [t]; linarith
      have htu : t ≤ u := by dsimp [t]; linarith
      have ht : 0 < t := hl.trans_le hlt
      have hc : u-l ≤ 2*((2:ℝ)^n*ε*l) := by
        rw [pow_succ] at hbudget
        nlinarith only [hbudget]
      have hsl := hsound ⟨offset,by omega⟩ t ht
      change ThresholdSearchConclusion target ε near
        (match query ⟨offset,by omega⟩ t with
          | .below => thresholdSearchIndexedValue query ε n (offset+1) (by omega) t u
          | .above => thresholdSearchIndexedValue query ε n (offset+1) (by omega) l t
          | .near => .near t)
      cases hq : query ⟨offset,by omega⟩ t with
      | below =>
        rw [hq] at hsl
        exact ih (offset+1) (by omega) t u ht hsl hhi (by
          have he := mul_le_mul_of_nonneg_left hlt
            (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n) hε)
          dsimp [t] at *
          nlinarith)
      | above =>
        rw [hq] at hsl
        exact ih (offset+1) (by omega) l t hl hlo hsl (by dsimp [t] at *; nlinarith)
      | near =>
        rw [hq] at hsl
        exact ⟨ht,hsl⟩

theorem thresholdSearchIndexed_correct (query : Fin cap → ℝ → ArithmeticProgram ThresholdDecision)
    (target ε : ℝ) (near : ℝ → Prop)
    (hsound : ∀ i, ThresholdSearchSound (fun t => (query i t).eval) target near) (hε : 0 ≤ ε)
    (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ)
    (hl : 0 < l) (hlo : l ≤ target) (hhi : target ≤ u)
    (hbudget : u-l ≤ (2:ℝ)^fuel*ε*l) :
    ThresholdSearchConclusion target ε near
      (thresholdSearchIndexed query ε fuel offset hcap l u).eval := by
  rw [thresholdSearchIndexed_eval]
  exact thresholdSearchIndexedValue_correct _ target ε near hsound hε fuel offset hcap l u hl hlo hhi hbudget

theorem thresholdSearchIndexed_admissible (query : Fin cap → ℝ → ArithmeticProgram ThresholdDecision)
    (hquery : ∀ i t, 0 < t → (query i t).admissible) (ε : ℝ)
    (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) :
    (thresholdSearchIndexed query ε fuel offset hcap l u).admissible := by
  induction fuel generalizing offset l u with
  | zero => trivial
  | succ n ih =>
    simp only [thresholdSearchIndexed, admissible_bind, admissible_sub, admissible_mul,
      eval_sub, eval_mul, true_and, ArithmeticProgram.admissible]
    split_ifs
    simp only [admissible_bind, admissible_add, admissible_div, eval_add, eval_div,
      true_and, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    have hlt : l ≤ (l+u)/2 := by linarith
    have htu : (l+u)/2 ≤ u := by linarith
    have ht : 0 < (l+u)/2 := hl.trans_le hlt
    refine ⟨hquery _ _ ht,?_⟩
    cases (query ⟨offset,by omega⟩ ((l+u)/2)).eval
    · exact ih (offset+1) (by omega) _ _ ht htu
    · exact ih (offset+1) (by omega) _ _ hl hlt
    · trivial

theorem thresholdSearchIndexed_work_le (query : Fin cap → ℝ → ArithmeticProgram ThresholdDecision)
    (cost : ℕ) (hquery : ∀ i t, 0 < t → (query i t).work ≤ cost) (ε : ℝ)
    (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) :
    (thresholdSearchIndexed query ε fuel offset hcap l u).work ≤ fuel*(5+cost) := by
  induction fuel generalizing offset l u with
  | zero => simp [thresholdSearchIndexed]
  | succ n ih =>
    rw [Nat.succ_mul]
    simp only [thresholdSearchIndexed, work_bind, work_sub, work_mul, eval_sub, eval_mul,
      ArithmeticProgram.work]
    split_ifs
    · omega
    · simp only [work_bind, work_add, work_div, eval_add, eval_div]
      have hlt : l ≤ (l+u)/2 := by linarith
      have htu : (l+u)/2 ≤ u := by linarith
      have ht : 0 < (l+u)/2 := hl.trans_le hlt
      have hq := hquery (⟨offset,by omega⟩ : Fin cap) ((l+u)/2) ht
      cases (query ⟨offset,by omega⟩ ((l+u)/2)).eval
      · have hh := ih (offset+1) (by omega) ((l+u)/2) u ht htu
        dsimp only
        omega
      · have hh := ih (offset+1) (by omega) l ((l+u)/2) hl hlt
        dsimp only
        omega
      · simp only [ArithmeticProgram.work]
        omega

end
end HierarchicalAbsoluteSpectral
