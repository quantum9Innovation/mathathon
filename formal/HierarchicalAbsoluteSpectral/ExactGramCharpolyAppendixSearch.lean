import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixSearchCore
import HierarchicalAbsoluteSpectral.ExactGramCharpolyCost
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixSearchCount

/-! The original coefficient initializer followed by exact shifted-inertia
bisection. Every field operation is executed, and failures remain `none`. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix MeasureTheory
open ArithmeticProgram hiding pure

variable {n : ℕ}

def exactGramAppendixSearchCap (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ℕ :=
  leastHalvings ((n : ℝ)^2-1) ε hε

abbrev ExactGramAppendixSearchTape (n : ℕ) (ε : ℝ) (hε : 0 < ε) :=
  Fin (exactGramAppendixSearchCap n ε hε) → Fin (n*n) → ℝ

def exactGramAppendixSearchLaw (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Measure (ExactGramAppendixSearchTape n ε hε) :=
  Measure.pi (fun _ : Fin (exactGramAppendixSearchCap n ε hε) => gaussianVector (n*n))

instance exactGramAppendixSearchLaw_isProbability (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IsProbabilityMeasure (exactGramAppendixSearchLaw n ε hε) := by
  unfold exactGramAppendixSearchLaw
  infer_instance

/-- The tape has a fixed finite budget of independent Gaussian coordinates. -/
def exactGramAppendixSearchGaussianDraws (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ℕ :=
  exactGramAppendixSearchCap n ε hε * (n*n)

def exactGramAppendixEigenvalueQuery (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.IsHermitian) (j : Fin n)
    (g : Fin (n*n) → ℝ) (t : ℝ) : ArithmeticProgram (Option Bool) := do
  let out? ← exactGramAppendixShiftedEigenvalueTestProgram kernels A hA t j g
  .pure (out?.map (fun out => out.answer))

theorem exactGramAppendixEigenvalueQuery_correct
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.IsHermitian) (j : Fin n)
    (g : Fin (n*n) → ℝ) (t : ℝ) (b : Bool)
    (hb : (exactGramAppendixEigenvalueQuery kernels A hA j g t).eval = some b) :
    b = true ↔ t < orderedEigenvalue A hA j := by
  simp only [exactGramAppendixEigenvalueQuery, eval_bind, eval_pure] at hb
  cases htest : (exactGramAppendixShiftedEigenvalueTestProgram kernels A hA t j g).eval with
  | none => simp only [htest, Option.map_none] at hb; cases hb
  | some out =>
      simp only [htest, Option.map_some] at hb
      have heq := Option.some.inj hb
      rw [← heq]
      exact out.correct

theorem exactGramAppendixEigenvalueQuery_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.IsHermitian) (j : Fin n)
    (g : Fin (n*n) → ℝ) (t : ℝ) :
    (exactGramAppendixEigenvalueQuery kernels A hA j g t).admissible := by
  simp only [exactGramAppendixEigenvalueQuery, admissible_bind,
    exactGramAppendixShiftedEigenvalueTestProgram_admissible, admissible_pure, and_self]

theorem exactGramAppendixEigenvalueQuery_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ C*(N : ℝ)^p)
    (A : Core n) (hA : A.IsHermitian) (j : Fin n)
    (g : Fin (n*n) → ℝ) (t : ℝ) :
    ((exactGramAppendixEigenvalueQuery kernels A hA j g t).work : ℝ) ≤
      105*(C+1)*(n : ℝ)^p := by
  simp only [exactGramAppendixEigenvalueQuery, work_bind, work_pure, add_zero]
  exact exactGramAppendixShiftedEigenvalueTestProgram_work_bound kernels C p hC hp hK A hA t j g

/-- The logarithmic cap is found by literal scalar halving, after executing
the two operations forming the relative bracket width `n²-1`. -/
def exactGramAppendixSearchCapProgram (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ArithmeticProgram ℕ := do
  let square ← mul (n : ℝ) (n : ℝ)
  let relative ← sub square 1
  scalarHalving relative ε hε

@[simp] theorem exactGramAppendixSearchCapProgram_eval (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (exactGramAppendixSearchCapProgram n ε hε).eval = exactGramAppendixSearchCap n ε hε := by
  simp only [exactGramAppendixSearchCapProgram, eval_bind, eval_mul, eval_sub,
    exactGramAppendixSearchCap, pow_two, (scalarHalving_checked ((n : ℝ)*(n : ℝ)-1) ε hε).1]

theorem exactGramAppendixSearchCapProgram_work (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (exactGramAppendixSearchCapProgram n ε hε).work =
      2*exactGramAppendixSearchCap n ε hε+3 := by
  simp only [exactGramAppendixSearchCapProgram, work_bind, work_mul, work_sub,
    eval_mul, eval_sub, exactGramAppendixSearchCap, pow_two,
    (scalarHalving_checked ((n : ℝ)*(n : ℝ)-1) ε hε).2.1]
  omega

theorem exactGramAppendixSearchCapProgram_admissible (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (exactGramAppendixSearchCapProgram n ε hε).admissible := by
  simp only [exactGramAppendixSearchCapProgram, admissible_bind, admissible_mul,
    admissible_sub, eval_mul, eval_sub, true_and]
  exact (scalarHalving_checked _ ε hε).2.2

def exactGramAppendixSearchProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε)
    (g : ExactGramAppendixSearchTape n ε hε) : ArithmeticProgram (Option InitializerResult) := do
  let initial ← exactGramCharpolyInitializerProgram kernels A j 1
  match initial with
  | .exact => .pure (some .exact)
  | .bracket l u => do
      let fuel ← (exactGramAppendixSearchCapProgram n ε hε).certify
      have hfuel : fuel.val = exactGramAppendixSearchCap n ε hε :=
        fuel.property.trans (exactGramAppendixSearchCapProgram_eval n ε hε)
      exactGramAppendixSearchIndexed
        (fun i t => exactGramAppendixEigenvalueQuery kernels A hA.isHermitian j (g i) t)
        ε fuel.val 0 (by rw [hfuel]; omega) l u

theorem exactGramAppendixSearchProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε)
    (g : ExactGramAppendixSearchTape n ε hε) :
    (exactGramAppendixSearchProgram kernels A hA j ε hε g).eval =
      match (exactGramCharpolyInitializerProgram kernels A j 1).eval with
      | .exact => some .exact
      | .bracket l u =>
          (exactGramAppendixSearchIndexed
            (fun i t => exactGramAppendixEigenvalueQuery kernels A hA.isHermitian j (g i) t)
            ε (exactGramAppendixSearchCap n ε hε) 0 (by omega) l u).eval := by
  simp only [exactGramAppendixSearchProgram, eval_bind]
  split
  · rfl
  · simp only [eval_bind, certify_eval, exactGramAppendixSearchCapProgram_eval]

theorem exactGramAppendixSearchProgram_correct
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε)
    (g : ExactGramAppendixSearchTape n ε hε) (out : InitializerResult)
    (hout : (exactGramAppendixSearchProgram kernels A hA j ε hε g).eval = some out) :
    ExactGramAppendixSearchConclusion (orderedEigenvalue A hA.isHermitian j) ε out := by
  have hi := exactGramCharpolyInitializerProgram_correct kernels A hA j 1
    (orderedEigenvalue A hA.isHermitian j) le_rfl (by simp)
  rw [exactGramAppendixSearchProgram_eval] at hout
  cases hinitial : (exactGramCharpolyInitializerProgram kernels A j 1).eval with
  | exact =>
      rw [hinitial] at hi hout
      have heq : InitializerResult.exact = out := Option.some.inj hout
      subst out
      exact hi
  | bracket l u =>
      rw [hinitial] at hi hout
      simp only [one_mul] at hi
      rcases hi with ⟨hl, hlo, hhi, hratio⟩
      apply exactGramAppendixSearchIndexed_correct _ _ ε
        (fun i t b hb => exactGramAppendixEigenvalueQuery_correct kernels A hA.isHermitian j
          (g i) t b hb) hε.le _ _ _ l u hl hlo hhi ?_ out hout
      have hu : u = (n : ℝ)^2*l := (div_eq_iff hl.ne').mp hratio
      have hs := leastHalvings_spec ((n : ℝ)^2-1) ε hε
      have hpow : 0 < (2 : ℝ)^exactGramAppendixSearchCap n ε hε := pow_pos (by norm_num) _
      have hb : (n : ℝ)^2-1 ≤ ε*(2 : ℝ)^exactGramAppendixSearchCap n ε hε :=
        (div_le_iff₀ hpow).mp hs
      nlinarith [mul_le_mul_of_nonneg_right hb hl.le]

theorem exactGramAppendixSearchProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε)
    (g : ExactGramAppendixSearchTape n ε hε) :
    (exactGramAppendixSearchProgram kernels A hA j ε hε g).admissible := by
  simp only [exactGramAppendixSearchProgram, admissible_bind,
    exactGramCharpolyInitializerProgram_admissible kernels A hA j 1 (by norm_num), true_and]
  split
  · trivial
  · simp only [admissible_bind, certify_admissible,
      exactGramAppendixSearchCapProgram_admissible, true_and]
    exact exactGramAppendixSearchIndexed_admissible _
      (fun i t => exactGramAppendixEigenvalueQuery_admissible kernels A hA.isHermitian j (g i) t)
      ε _ _ _ _ _

theorem exactGramAppendixSearchProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ C*(N : ℝ)^p)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε)
    (g : ExactGramAppendixSearchTape n ε hε) :
    ((exactGramAppendixSearchProgram kernels A hA j ε hε g).work : ℝ) ≤
      33*(C+1)*(Nat.clog 2 (n+1)+1 : ℕ)*((2*(n+1) : ℕ) : ℝ)^p+7+
      (2*(exactGramAppendixSearchCap n ε hε : ℝ)+3)+
      (exactGramAppendixSearchCap n ε hε : ℝ)*(5+105*(C+1)*(n : ℝ)^p) := by
  let B := 105*(C+1)*(n : ℝ)^p
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hi := exactGramCharpolyInitializerProgram_work_bound kernels C p hC hp
    (fun a b c N _ => hK a b c N) A j 1
  cases hinitial : (exactGramCharpolyInitializerProgram kernels A j 1).eval with
  | exact =>
      simp only [exactGramAppendixSearchProgram, work_bind, hinitial, work_pure, add_zero]
      exact hi.trans (by
        have hc : 0 ≤ (exactGramAppendixSearchCap n ε hε : ℝ) := Nat.cast_nonneg _
        dsimp only [B] at hB
        nlinarith [mul_nonneg hc (show 0 ≤ 5+105*(C+1)*(n : ℝ)^p by linarith)])
  | bracket l u =>
      simp only [exactGramAppendixSearchProgram, work_bind, hinitial, certify_work,
        certify_eval, exactGramAppendixSearchCapProgram_eval, exactGramAppendixSearchCapProgram_work,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      have hs := exactGramAppendixSearchIndexed_work_bound
        (fun i t => exactGramAppendixEigenvalueQuery kernels A hA.isHermitian j (g i) t)
        B hB (fun i t => exactGramAppendixEigenvalueQuery_work_bound kernels C p hC hp hK
          A hA.isHermitian j (g i) t) ε (exactGramAppendixSearchCap n ε hε) 0 (by omega) l u
      dsimp only [B] at hs
      push_cast at hi ⊢
      linarith

/-- The upper endpoint interface used by the appendix's subsequent jitter
and matrix-lift stages. The exact zero branch returns zero. -/
def exactGramAppendixUpperProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε)
    (g : ExactGramAppendixSearchTape n ε hε) : ArithmeticProgram (Option ℝ) := do
  let out? ← exactGramAppendixSearchProgram kernels A hA j ε hε g
  .pure (out?.map (fun out => match out with | .exact => 0 | .bracket _ u => u))

theorem exactGramAppendixUpperProgram_correct
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε)
    (g : ExactGramAppendixSearchTape n ε hε) (u : ℝ)
    (hu : (exactGramAppendixUpperProgram kernels A hA j ε hε g).eval = some u) :
    orderedEigenvalue A hA.isHermitian j ≤ u ∧
      u ≤ (1+ε)*orderedEigenvalue A hA.isHermitian j := by
  simp only [exactGramAppendixUpperProgram, eval_bind, eval_pure] at hu
  cases hs : (exactGramAppendixSearchProgram kernels A hA j ε hε g).eval with
  | none => simp only [hs, Option.map_none] at hu; cases hu
  | some out =>
      have hc := exactGramAppendixSearchProgram_correct kernels A hA j ε hε g out hs
      cases out with
      | exact =>
          simp only [hs, Option.map_some, Option.some.injEq] at hu
          change orderedEigenvalue A hA.isHermitian j = 0 at hc
          simp only [← hu, hc, mul_zero, le_refl, and_self]
      | bracket l v =>
          simp only [hs, Option.map_some, Option.some.injEq] at hu
          rw [← hu]
          exact ⟨hc.2.2.1, hc.2.2.2.2⟩

theorem exactGramAppendixUpperProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε)
    (g : ExactGramAppendixSearchTape n ε hε) :
    (exactGramAppendixUpperProgram kernels A hA j ε hε g).admissible := by
  simp only [exactGramAppendixUpperProgram, admissible_bind,
    exactGramAppendixSearchProgram_admissible, admissible_pure, and_self]

@[simp] theorem exactGramAppendixUpperProgram_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε)
    (g : ExactGramAppendixSearchTape n ε hε) :
    (exactGramAppendixUpperProgram kernels A hA j ε hε g).work =
      (exactGramAppendixSearchProgram kernels A hA j ε hε g).work := by
  simp only [exactGramAppendixUpperProgram, work_bind, work_pure, add_zero]

end
end HierarchicalAbsoluteSpectral
