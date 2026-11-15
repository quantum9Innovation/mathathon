import HierarchicalAbsoluteSpectral.ExactGramCharpolyKrylovBasis
import HierarchicalAbsoluteSpectral.ExactGramCharpolyKrylov
import HierarchicalAbsoluteSpectral.ExactGramCharpolyRankProfileCost
import HierarchicalAbsoluteSpectral.ExactGramCharpolyRankProfileFieldOnly

/-!
The executed Keller--Gehrig doubling loop. Each stage computes two matrix
products and a stable field-only rank profile of an n by at most 2n matrix.
The result carries the complete labelled-prefix invariant used to recover
the companion blocks. This file does not assume a characteristic-polynomial
algorithm as an input.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

def exactGramBranchingStep (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n d : ℕ} {A : Core n} (b : ExactGramKrylovBasis A d) :
    ArithmeticProgram (ExactGramKrylovBasis A (d+d)) := do
  let square ← certify (rankProfileMulProgram kernels b.power b.power)
  let shifted ← certify (rankProfileMulProgram kernels b.power b.basis)
  let W := (Matrix.fromCols b.basis shifted.val).submatrix id b.layout.copy
  have hW : W = b.doubled := by
    dsimp only [W, ExactGramKrylovBasis.doubled]
    rw [shifted.property, rankProfileMulProgram_eval]
  let p ← fieldColumnRankProfileProgram kernels W
  ArithmeticProgram.pure (b.compress W hW square.val
    (square.property.trans (rankProfileMulProgram_eval _ _ _)) p)

theorem exactGramBranchingStep_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n d : ℕ} {A : Core n} (b : ExactGramKrylovBasis A d) :
    (exactGramBranchingStep kernels b).admissible := by
  simp only [exactGramBranchingStep, admissible_bind, certify_admissible,
    rankProfileMulProgram_admissible, fieldColumnRankProfileProgram_admissible,
    admissible_pure, and_self]

theorem exactGramBranchingStep_fieldOnly
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n d : ℕ} {A : Core n} (b : ExactGramKrylovBasis A d) :
    (exactGramBranchingStep kernels b).rankProfileFieldOnly := by
  simp only [exactGramBranchingStep, rankProfileFieldOnly_bind, rankProfileFieldOnly_certify,
    rankProfileMulProgram_fieldOnly, fieldColumnRankProfileProgram_fieldOnly,
    rankProfileFieldOnly_pure, and_self]

theorem exactGramBranchingStep_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N →
      a ≤ N → b ≤ N → c ≤ N → ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    {n d : ℕ} {A : Core n} (b : ExactGramKrylovBasis A d) (hn : 1 ≤ n) :
    ((exactGramBranchingStep kernels b).work:ℝ) ≤ 22*(C+1)*((2*n:ℕ):ℝ)^p := by
  have hN : 1 ≤ 2*n := by omega
  have hnN : n ≤ 2*n := by omega
  have hwN : b.width ≤ 2*n := b.width_le.trans hnN
  have hwwN : b.width+b.width ≤ 2*n := by have hw := b.width_le; omega
  have hE := kernelEnvelope_bound kernels C p hC hK (2*n) hN
  have hfirst : ((rankProfileMulProgram kernels b.power b.power).work:ℝ) ≤
      C*((2*n:ℕ):ℝ)^p := by
    apply le_trans _ hE
    exact_mod_cast rankProfileMulProgram_work_le kernels b.power b.power (2*n) hnN hnN hnN
  have hsecond : ((rankProfileMulProgram kernels b.power b.basis).work:ℝ) ≤
      C*((2*n:ℕ):ℝ)^p := by
    apply le_trans _ hE
    exact_mod_cast rankProfileMulProgram_work_le kernels b.power b.basis (2*n) hnN hnN hwN
  have hprofile (W : Matrix (Fin n) (Fin (b.width+b.width)) ℝ) :=
    fieldColumnRankProfileProgram_work_bound kernels C p hC hp hK W (2*n) hN hnN hwwN
  simp only [exactGramBranchingStep, work_bind, certify_work, work_pure, add_zero,
    Nat.cast_add]
  calc
    _ ≤ C*((2*n:ℕ):ℝ)^p + (C*((2*n:ℕ):ℝ)^p +
        20*(C+1)*((2*n:ℕ):ℝ)^p) := add_le_add hfirst (add_le_add hsecond (hprofile _))
    _ ≤ _ := by
      have hpow : 0 ≤ ((2*n:ℕ):ℝ)^p := Real.rpow_nonneg (by positivity) _
      nlinarith

def exactGramBranchingProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) :
    (t : ℕ) → ArithmeticProgram (ExactGramKrylovBasis A (exactGramKrylovWidth t))
  | 0 => .pure (exactGramKrylovBasis_initial A)
  | t+1 => do
      let b ← exactGramBranchingProgram kernels A t
      exactGramBranchingStep kernels b

theorem exactGramBranchingProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) (t : ℕ) : (exactGramBranchingProgram kernels A t).admissible := by
  induction t with
  | zero => trivial
  | succ t ih =>
      rw [exactGramBranchingProgram, admissible_bind]
      exact ⟨ih, exactGramBranchingStep_admissible kernels _⟩

theorem exactGramBranchingProgram_fieldOnly
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) (t : ℕ) :
    (exactGramBranchingProgram kernels A t).rankProfileFieldOnly := by
  induction t with
  | zero => trivial
  | succ t ih =>
      rw [exactGramBranchingProgram, rankProfileFieldOnly_bind]
      exact ⟨ih, exactGramBranchingStep_fieldOnly kernels _⟩

theorem exactGramBranchingProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N →
      a ≤ N → b ≤ N → c ≤ N → ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    {n : ℕ} (A : Core n) (t : ℕ) (hn : 1 ≤ n) :
    ((exactGramBranchingProgram kernels A t).work:ℝ) ≤ 22*t*(C+1)*((2*n:ℕ):ℝ)^p := by
  induction t with
  | zero => simp [exactGramBranchingProgram]
  | succ t ih =>
      rw [exactGramBranchingProgram, work_bind, Nat.cast_add]
      have hs := exactGramBranchingStep_work_bound kernels C p hC hp hK
        (exactGramBranchingProgram kernels A t).eval hn
      push_cast at ih hs ⊢
      nlinarith

end
end HierarchicalAbsoluteSpectral
