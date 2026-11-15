import HierarchicalAbsoluteSpectral.ThresholdSearchTrace
import HierarchicalAbsoluteSpectral.ThresholdQueryMeasurable

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory
variable {cap : ℕ}

abbrev ThresholdQueryState := ℝ × ℝ × Bool

def thresholdQueryStep (query : Fin cap → ℝ → ThresholdDecision) (ε : ℝ)
    (i : Fin cap) (state : ThresholdQueryState) : ThresholdQueryState :=
  if state.2.2 then
    if state.2.1-state.1≤ε*state.1 then (state.1,state.2.1,false) else
      let t := (state.1+state.2.1)/2
      if query i t=.below then (t,state.2.1,true)
      else if query i t=.above then (state.1,t,true)
      else (state.1,state.2.1,false)
  else state

def thresholdQueryHistory (query : Fin cap → ℝ → ThresholdDecision) (ε l u : ℝ) :
    (n : ℕ) → n≤cap → ThresholdQueryState
  | 0, _ => (l,u,true)
  | n+1, hn => thresholdQueryStep query ε ⟨n,by omega⟩
      (thresholdQueryHistory query ε l u n (by omega))

theorem thresholdQueryHistory_prefix
    (query query' : Fin cap → ℝ → ThresholdDecision) (ε l u : ℝ)
    (n : ℕ) (hn : n≤cap)
    (heq : ∀ i : Fin cap, i.val<n → ∀ t, query i t=query' i t) :
    thresholdQueryHistory query ε l u n hn=thresholdQueryHistory query' ε l u n hn := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [thresholdQueryHistory]
    have hh := ih (by omega) (fun i hi t => heq i (by omega) t)
    rw [hh]
    simp only [thresholdQueryStep,heq ⟨n,by omega⟩ (by simp)]

/-- Altering the current or a future random block cannot change the state
before that block is consumed. -/
theorem thresholdQueryHistory_update {X : Type*}
    (query : Fin cap → X → ℝ → ThresholdDecision) (samples : Fin cap → X)
    (ε l u : ℝ) (i : Fin cap) (x : X) (n : ℕ) (hn : n ≤ cap) (hni : n ≤ i.val) :
    thresholdQueryHistory (fun j t => query j (Function.update samples i x j) t) ε l u n hn=
      thresholdQueryHistory (fun j t => query j (samples j) t) ε l u n hn := by
  apply thresholdQueryHistory_prefix
  intro j hj t
  have hne : j≠i := by intro heq; have := congrArg Fin.val heq; omega
  simp only [Function.update_of_ne hne]

theorem thresholdQueryHistory_current_update {X : Type*}
    (query : Fin cap → X → ℝ → ThresholdDecision) (samples : Fin cap → X)
    (ε l u : ℝ) (i : Fin cap) (x : X) :
    thresholdQueryHistory (fun j t => query j (Function.update samples i x j) t) ε l u i.val i.isLt.le=
      thresholdQueryHistory (fun j t => query j (samples j) t) ε l u i.val i.isLt.le :=
  thresholdQueryHistory_update query samples ε l u i x i.val i.isLt.le le_rfl

theorem thresholdQueryStep_positive (query : Fin cap → ℝ → ThresholdDecision) (ε : ℝ)
    (i : Fin cap) (state : ThresholdQueryState) (hl : 0<state.1) (hlu : state.1 ≤ state.2.1) :
    0<(thresholdQueryStep query ε i state).1 ∧
      (thresholdQueryStep query ε i state).1≤(thresholdQueryStep query ε i state).2.1 := by
  unfold thresholdQueryStep
  dsimp only
  split_ifs <;> constructor <;> linarith

theorem thresholdQueryHistory_positive (query : Fin cap → ℝ → ThresholdDecision) (ε l u : ℝ)
    (hl : 0<l) (hlu : l≤u) (n : ℕ) (hn : n≤cap) :
    0<(thresholdQueryHistory query ε l u n hn).1 ∧
      (thresholdQueryHistory query ε l u n hn).1≤(thresholdQueryHistory query ε l u n hn).2.1 := by
  induction n with
  | zero => exact ⟨hl,hlu⟩
  | succ n ih =>
    exact thresholdQueryStep_positive query ε ⟨n,by omega⟩ _ (ih (by omega)).1 (ih (by omega)).2

theorem thresholdQueryHistory_midpoint_positive
    (query : Fin cap → ℝ → ThresholdDecision) (ε l u : ℝ)
    (hl : 0<l) (hlu : l≤u) (i : Fin cap) :
    0<((thresholdQueryHistory query ε l u i.val i.isLt.le).1+
      (thresholdQueryHistory query ε l u i.val i.isLt.le).2.1)/2 := by
  have hh := thresholdQueryHistory_positive query ε l u hl hlu i.val i.isLt.le
  linarith

def thresholdQueryHistoryGood (query : Fin cap → ℝ → ThresholdDecision)
    (target ε : ℝ) (near : ℝ → Prop) (l u : ℝ) : Prop :=
  ∀ i : Fin cap,
    let state := thresholdQueryHistory query ε l u i.val i.isLt.le
    state.2.2=true → ¬state.2.1-state.1≤ε*state.1 →
      match query i ((state.1+state.2.1)/2) with
      | .below => (state.1+state.2.1)/2≤target
      | .above => target≤(state.1+state.2.1)/2
      | .near => near ((state.1+state.2.1)/2)

theorem thresholdSearchTraceGood_of_history
    (query : Fin cap → ℝ → ThresholdDecision) (target ε : ℝ) (near : ℝ → Prop)
    (l₀ u₀ : ℝ) (hgood : thresholdQueryHistoryGood query target ε near l₀ u₀)
    (fuel offset : ℕ) (hcap : offset+fuel≤cap) (l u : ℝ)
    (hstate : thresholdQueryHistory query ε l₀ u₀ offset (by omega)=(l,u,true)) :
    thresholdSearchTraceGood query target ε near fuel offset hcap l u := by
  induction fuel generalizing offset l u with
  | zero => trivial
  | succ fuel ih =>
    simp only [thresholdSearchTraceGood]
    by_cases hstop : u-l≤ε*l
    · simp only [if_pos hstop]
    · rw [if_neg hstop]
      let i : Fin cap := ⟨offset,by omega⟩
      let t := (l+u)/2
      have hs : thresholdQueryHistory query ε l₀ u₀ i.val i.isLt.le=(l,u,true) := hstate
      have hg := hgood i
      dsimp only at hg
      rw [hs] at hg
      have hg' := hg rfl hstop
      change (match query i t with
        | .below => t≤target ∧ thresholdSearchTraceGood query target ε near fuel (offset+1) (by omega) t u
        | .above => target≤t ∧ thresholdSearchTraceGood query target ε near fuel (offset+1) (by omega) l t
        | .near => near t)
      change (match query i t with
        | .below => t≤target
        | .above => target≤t
        | .near => near t) at hg'
      cases hd : query i t with
      | below =>
        rw [hd] at hg'
        refine ⟨hg',ih (offset+1) (by omega) t u ?_⟩
        simp only [thresholdQueryHistory]
        rw [hstate]
        simp only [thresholdQueryStep,if_pos rfl,if_neg hstop]
        rw [show query ⟨offset,by omega⟩ ((l+u)/2)=.below from hd]
        simp only [ite_true]
        rfl
      | above =>
        rw [hd] at hg'
        refine ⟨hg',ih (offset+1) (by omega) l t ?_⟩
        simp only [thresholdQueryHistory]
        rw [hstate]
        simp only [thresholdQueryStep,if_pos rfl,if_neg hstop]
        rw [show query ⟨offset,by omega⟩ ((l+u)/2)=.above from hd]
        simp only [reduceCtorEq,ite_false,ite_true]
        rfl
      | near => rw [hd] at hg'; exact hg'

theorem thresholdSearchIndexed_correct_of_history
    (query : Fin cap → ℝ → ArithmeticProgram ThresholdDecision)
    (target ε : ℝ) (near : ℝ → Prop) (hε : 0≤ε)
    (l u : ℝ) (hl : 0<l) (hlo : l≤target) (hhi : target≤u)
    (hbudget : u-l≤(2:ℝ)^cap*ε*l)
    (hgood : thresholdQueryHistoryGood (fun i t => (query i t).eval) target ε near l u) :
    ThresholdSearchConclusion target ε near
      (thresholdSearchIndexed query ε cap 0 (by omega) l u).eval := by
  apply thresholdSearchIndexed_correct_of_trace query target ε near hε cap 0 (by omega) l u hl hlo hhi hbudget
  exact thresholdSearchTraceGood_of_history _ target ε near l u hgood cap 0 (by omega) l u rfl

def thresholdQueryHistoryAgree (actual ideal : Fin cap → ℝ → ThresholdDecision)
    (ε l u : ℝ) : Prop :=
  ∀ i : Fin cap,
    let state := thresholdQueryHistory ideal ε l u i.val i.isLt.le
    state.2.2=true → ¬state.2.1-state.1 ≤ ε*state.1 →
      actual i ((state.1+state.2.1)/2)=ideal i ((state.1+state.2.1)/2)

theorem thresholdSearchTraceAgree_of_history
    (actual ideal : Fin cap → ℝ → ThresholdDecision) (ε l₀ u₀ : ℝ)
    (hagree : thresholdQueryHistoryAgree actual ideal ε l₀ u₀)
    (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ)
    (hstate : thresholdQueryHistory ideal ε l₀ u₀ offset (by omega)=(l,u,true)) :
    thresholdSearchTraceAgree actual ideal ε fuel offset hcap l u := by
  induction fuel generalizing offset l u with
  | zero => trivial
  | succ fuel ih =>
    simp only [thresholdSearchTraceAgree]
    by_cases hstop : u-l ≤ ε*l
    · simp only [if_pos hstop]
    · rw [if_neg hstop]
      let i : Fin cap := ⟨offset,by omega⟩
      let t := (l+u)/2
      have hs : thresholdQueryHistory ideal ε l₀ u₀ i.val i.isLt.le=(l,u,true) := hstate
      have ha := hagree i
      dsimp only at ha
      rw [hs] at ha
      refine ⟨ha rfl hstop,?_⟩
      change (match ideal i t with
        | .below => thresholdSearchTraceAgree actual ideal ε fuel (offset+1) (by omega) t u
        | .above => thresholdSearchTraceAgree actual ideal ε fuel (offset+1) (by omega) l t
        | .near => True)
      cases hd : ideal i t with
      | below =>
        apply ih (offset+1) (by omega) t u
        simp only [thresholdQueryHistory]
        rw [hstate]
        simp only [thresholdQueryStep,if_neg hstop]
        rw [show ideal ⟨offset,by omega⟩ ((l+u)/2)=.below from hd]
        simp only [ite_true]
        rfl
      | above =>
        apply ih (offset+1) (by omega) l t
        simp only [thresholdQueryHistory]
        rw [hstate]
        simp only [thresholdQueryStep,if_neg hstop]
        rw [show ideal ⟨offset,by omega⟩ ((l+u)/2)=.above from hd]
        simp only [reduceCtorEq,ite_false,ite_true]
        rfl
      | near => trivial

theorem thresholdSearchIndexedValue_eq_of_history
    (actual ideal : Fin cap → ℝ → ThresholdDecision) (ε l u : ℝ)
    (hagree : thresholdQueryHistoryAgree actual ideal ε l u) :
    thresholdSearchIndexedValue actual ε cap 0 (by omega) l u=
      thresholdSearchIndexedValue ideal ε cap 0 (by omega) l u :=
  thresholdSearchIndexedValue_eq_of_trace actual ideal ε cap 0 (by omega) l u
    (thresholdSearchTraceAgree_of_history actual ideal ε l u hagree cap 0 (by omega) l u rfl)

end
end HierarchicalAbsoluteSpectral
