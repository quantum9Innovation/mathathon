import HierarchicalAbsoluteSpectral.ThresholdDecision

/-! Capped scalar threshold search, expressed as actual arithmetic programs.
The query program is a parameter at this composition layer; its mathematical
and operation-count contracts must be proved when the concrete query is supplied. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

inductive ThresholdSearchResult where
  | bracket (lower upper : ℝ)
  | near (threshold : ℝ)

def thresholdSearchValue (query : ℝ → ThresholdDecision) (ε : ℝ) :
    ℕ → ℝ → ℝ → ThresholdSearchResult
  | 0, l, u => .bracket l u
  | n+1, l, u =>
    if u-l ≤ ε*l then .bracket l u
    else
      let t := (l+u)/2
      match query t with
      | .below => thresholdSearchValue query ε n t u
      | .above => thresholdSearchValue query ε n l t
      | .near => .near t

def thresholdSearch (query : ℝ → ArithmeticProgram ThresholdDecision) (ε : ℝ) :
    ℕ → ℝ → ℝ → ArithmeticProgram ThresholdSearchResult
  | 0, l, u => .pure (.bracket l u)
  | n+1, l, u => do
    let width ← sub u l
    let tolerance ← mul ε l
    .branch width tolerance
      (fun _ => .pure (.bracket l u))
      (fun _ => do
        let total ← add l u
        let t ← div total 2
        let answer ← query t
        match answer with
        | .below => thresholdSearch query ε n t u
        | .above => thresholdSearch query ε n l t
        | .near => .pure (.near t))

theorem thresholdSearch_eval (query : ℝ → ArithmeticProgram ThresholdDecision)
    (ε : ℝ) (n : ℕ) (l u : ℝ) :
    (thresholdSearch query ε n l u).eval = thresholdSearchValue (fun t => (query t).eval) ε n l u := by
  induction n generalizing l u with
  | zero => rfl
  | succ n ih =>
    simp only [thresholdSearch, eval_bind, eval_sub, eval_mul, ArithmeticProgram.eval,
      thresholdSearchValue]
    split_ifs
    · rfl
    · simp only [eval_bind, eval_add, eval_div]
      cases (query ((l+u)/2)).eval <;> simp only [ih, ArithmeticProgram.eval]

def ThresholdSearchSound (query : ℝ → ThresholdDecision) (target : ℝ) (near : ℝ → Prop) : Prop :=
  ∀ t, 0 < t → match query t with
    | .below => t ≤ target
    | .above => target ≤ t
    | .near => near t

def ThresholdSearchConclusion (target ε : ℝ) (near : ℝ → Prop) : ThresholdSearchResult → Prop
  | .near t => 0 < t ∧ near t
  | .bracket l u => 0 < l ∧ l ≤ target ∧ target ≤ u ∧
      u-l ≤ ε*l ∧ u ≤ (1+ε)*target

theorem thresholdSearchValue_correct (query : ℝ → ThresholdDecision) (target ε : ℝ)
    (near : ℝ → Prop) (hsound : ThresholdSearchSound query target near)
    (hε : 0 ≤ ε) (n : ℕ) (l u : ℝ) (hl : 0 < l)
    (hlo : l ≤ target) (hhi : target ≤ u)
    (hcap : u-l ≤ (2:ℝ)^n*ε*l) :
    ThresholdSearchConclusion target ε near (thresholdSearchValue query ε n l u) := by
  have finish (a b : ℝ) (ha : 0 < a) (hal : a ≤ target) (hbu : target ≤ b)
      (hw : b-a ≤ ε*a) : ThresholdSearchConclusion target ε near (.bracket a b) := by
    refine ⟨ha,hal,hbu,hw,?_⟩
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hal)]
  induction n generalizing l u with
  | zero =>
    apply finish l u hl hlo hhi
    simpa only [pow_zero, one_mul] using hcap
  | succ n ih =>
    rw [thresholdSearchValue]
    split_ifs with hstop
    · exact finish l u hl hlo hhi hstop
    · let t := (l+u)/2
      have hlt : l ≤ t := by dsimp [t]; linarith
      have htu : t ≤ u := by dsimp [t]; linarith
      have ht : 0 < t := hl.trans_le hlt
      have hc : u-l ≤ 2*((2:ℝ)^n*ε*l) := by
        rw [pow_succ] at hcap
        nlinarith only [hcap]
      have hsl := hsound t ht
      change ThresholdSearchConclusion target ε near
        (match query t with
          | .below => thresholdSearchValue query ε n t u
          | .above => thresholdSearchValue query ε n l t
          | .near => .near t)
      cases hq : query t with
      | below =>
        rw [hq] at hsl
        exact ih t u ht hsl hhi (by
          have he := mul_le_mul_of_nonneg_left hlt
            (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n) hε)
          dsimp [t] at *
          nlinarith)
      | above =>
        rw [hq] at hsl
        exact ih l t hl hlo hsl (by dsimp [t] at *; nlinarith)
      | near =>
        rw [hq] at hsl
        exact ⟨ht,hsl⟩

theorem thresholdSearch_correct (query : ℝ → ArithmeticProgram ThresholdDecision)
    (target ε : ℝ) (near : ℝ → Prop)
    (hsound : ThresholdSearchSound (fun t => (query t).eval) target near)
    (hε : 0 ≤ ε) (n : ℕ) (l u : ℝ) (hl : 0 < l)
    (hlo : l ≤ target) (hhi : target ≤ u)
    (hcap : u-l ≤ (2:ℝ)^n*ε*l) :
    ThresholdSearchConclusion target ε near (thresholdSearch query ε n l u).eval := by
  rw [thresholdSearch_eval]
  exact thresholdSearchValue_correct _ target ε near hsound hε n l u hl hlo hhi hcap

theorem thresholdSearch_admissible (query : ℝ → ArithmeticProgram ThresholdDecision)
    (hquery : ∀ t, 0 < t → (query t).admissible) (ε : ℝ) (n : ℕ)
    (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) :
    (thresholdSearch query ε n l u).admissible := by
  induction n generalizing l u with
  | zero => trivial
  | succ n ih =>
    simp only [thresholdSearch, admissible_bind, admissible_sub, admissible_mul,
      eval_sub, eval_mul, true_and, ArithmeticProgram.admissible]
    split_ifs
    simp only [admissible_bind, admissible_add, admissible_div, eval_add, eval_div,
      true_and, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    have hlt : l ≤ (l+u)/2 := by linarith
    have htu : (l+u)/2 ≤ u := by linarith
    have ht : 0 < (l+u)/2 := hl.trans_le hlt
    refine ⟨hquery _ ht,?_⟩
    cases (query ((l+u)/2)).eval
    · exact ih _ _ ht htu
    · exact ih _ _ hl hlt
    · trivial

/-- Every outcome is capped, including unsuccessful query outcomes. Five
scalar instructions are charged for each attempted threshold. -/
theorem thresholdSearch_work_le (query : ℝ → ArithmeticProgram ThresholdDecision)
    (cost : ℕ) (hquery : ∀ t, 0 < t → (query t).work ≤ cost)
    (ε : ℝ) (n : ℕ) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) :
    (thresholdSearch query ε n l u).work ≤ n*(5+cost) := by
  induction n generalizing l u with
  | zero => simp [thresholdSearch]
  | succ n ih =>
    rw [Nat.succ_mul]
    simp only [thresholdSearch, work_bind, work_sub, work_mul, eval_sub, eval_mul,
      ArithmeticProgram.work]
    split_ifs
    · omega
    · simp only [work_bind, work_add, work_div, eval_add, eval_div]
      have hlt : l ≤ (l+u)/2 := by linarith
      have htu : (l+u)/2 ≤ u := by linarith
      have ht : 0 < (l+u)/2 := hl.trans_le hlt
      have hq := hquery ((l+u)/2) ht
      cases (query ((l+u)/2)).eval
      · have hh := ih ((l+u)/2) u ht htu
        dsimp only
        omega
      · have hh := ih l ((l+u)/2) hl hlt
        dsimp only
        omega
      · simp only [ArithmeticProgram.work]
        omega

end
end HierarchicalAbsoluteSpectral
