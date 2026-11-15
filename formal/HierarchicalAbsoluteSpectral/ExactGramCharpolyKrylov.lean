import HierarchicalAbsoluteSpectral.ArithmeticKernel
import HierarchicalAbsoluteSpectral.CoarseAlgebraPSDCost
import Mathlib.Data.Nat.Log

/-!
Executed repeated squaring and Krylov doubling for the fast exact-field
characteristic-polynomial computation. Matrix entries are only copied or
computed by the supplied verified multiplication circuits. In particular,
the analytical formula involving powers is not returned by `pure`.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

def exactGramKrylovWidth : ℕ → ℕ
  | 0 => 1
  | t+1 => exactGramKrylovWidth t + exactGramKrylovWidth t

theorem exactGramKrylovWidth_eq (t : ℕ) : exactGramKrylovWidth t = 2^t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [exactGramKrylovWidth, ih, pow_succ]; omega

theorem exactGramKrylovWidth_pos (t : ℕ) : 0 < exactGramKrylovWidth t := by
  rw [exactGramKrylovWidth_eq]
  positivity

def exactGramKrylovColumns {n : ℕ} (A : Core n) (v : Fin n → ℝ) (d : ℕ) :
    Matrix (Fin n) (Fin d) ℝ := fun i j => ((A^j.val) *ᵥ v) i

theorem exactGramKrylovColumns_double {n : ℕ} (A : Core n) (v : Fin n → ℝ) (d : ℕ) :
    (Matrix.fromCols (exactGramKrylovColumns A v d)
      ((A^d) * exactGramKrylovColumns A v d)).submatrix id finSumFinEquiv.symm =
        exactGramKrylovColumns A v (d+d) := by
  ext i j
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp [Matrix.submatrix_apply, exactGramKrylovColumns]
  · intro k
    simp only [Matrix.submatrix_apply, id_eq, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromCols_apply_inr, exactGramKrylovColumns, Fin.val_natAdd]
    change ((A^d) *ᵥ ((A^k.val) *ᵥ v)) i = ((A^(d+k.val)) *ᵥ v) i
    rw [Matrix.mulVec_mulVec, ← pow_add]

def exactGramKrylovProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) (v : Fin n → ℝ) :
    (t : ℕ) → ArithmeticProgram (Core n × Matrix (Fin n) (Fin (exactGramKrylovWidth t)) ℝ)
  | 0 => .pure (A, fun i _ => v i)
  | t+1 => do
      let previous ← exactGramKrylovProgram kernels A v t
      let square ← (kernels n n n).program previous.1 previous.1
      let shifted ← (kernels n n (exactGramKrylovWidth t)).program previous.1 previous.2
      ArithmeticProgram.pure (square,
        (Matrix.fromCols previous.2 shifted).submatrix id finSumFinEquiv.symm)

@[simp] theorem exactGramKrylovProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) (v : Fin n → ℝ) (t : ℕ) :
    (exactGramKrylovProgram kernels A v t).eval =
      (A^(exactGramKrylovWidth t), exactGramKrylovColumns A v (exactGramKrylovWidth t)) := by
  induction t with
  | zero =>
      simp only [exactGramKrylovProgram, eval_pure, exactGramKrylovWidth, pow_one,
        Prod.mk.injEq, true_and]
      ext i j
      have hj : j.val = 0 := by omega
      simp [exactGramKrylovColumns, hj]
  | succ t ih =>
      simp only [exactGramKrylovProgram, eval_bind, eval_pure, ih,
        ArithmeticKernel.program_eval, exactGramKrylovWidth, pow_add,
        exactGramKrylovColumns_double]

theorem exactGramKrylovProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) (v : Fin n → ℝ) (t : ℕ) :
    (exactGramKrylovProgram kernels A v t).admissible := by
  induction t with
  | zero => trivial
  | succ t ih =>
      simp only [exactGramKrylovProgram, admissible_bind, ih,
        ArithmeticKernel.program_admissible, admissible_pure, and_self]

def exactGramKrylovCost (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => exactGramKrylovCost kernels n t + (kernels n n n).cost +
      (kernels n n (exactGramKrylovWidth t)).cost

@[simp] theorem exactGramKrylovProgram_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) (v : Fin n → ℝ) (t : ℕ) :
    (exactGramKrylovProgram kernels A v t).work = exactGramKrylovCost kernels n t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [exactGramKrylovProgram, work_bind, ih, ArithmeticKernel.program_work,
        work_pure, add_zero, exactGramKrylovCost, Nat.add_assoc]

theorem exactGramKrylovCost_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n t N : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (htN : exactGramKrylovWidth t ≤ N) :
    exactGramKrylovCost kernels n t ≤ 2*t*kernelEnvelope kernels N := by
  induction t with
  | zero => simp [exactGramKrylovCost]
  | succ t ih =>
      have hprev : exactGramKrylovWidth t ≤ N := by
        simp only [exactGramKrylovWidth] at htN
        omega
      have hi := ih hprev
      have hs := kernelEnvelope_le kernels N n n n hnN hnN hnN (by omega)
      have hk := kernelEnvelope_le kernels N n n (exactGramKrylovWidth t)
        hnN hnN hprev (by omega)
      rw [exactGramKrylovCost]
      nlinarith

theorem exactGramKrylovProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N →
      a ≤ N → b ≤ N → c ≤ N → ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    {n : ℕ} (A : Core n) (v : Fin n → ℝ) (t N : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (htN : exactGramKrylovWidth t ≤ N) :
    ((exactGramKrylovProgram kernels A v t).work:ℝ) ≤ 2*t*C*(N:ℝ)^p := by
  rw [exactGramKrylovProgram_work]
  have hc : (exactGramKrylovCost kernels n t:ℝ) ≤
      2*t*(kernelEnvelope kernels N:ℝ) := by
    exact_mod_cast exactGramKrylovCost_le kernels n t N hn hnN htN
  have hk := kernelEnvelope_bound kernels C p hC hK N (hn.trans hnN)
  nlinarith

theorem exactGramKrylovWidth_clog (n : ℕ) (hn : 1 ≤ n) :
    n+1 ≤ exactGramKrylovWidth (Nat.clog 2 (n+1)) ∧
      exactGramKrylovWidth (Nat.clog 2 (n+1)) ≤ 4*n := by
  rw [exactGramKrylovWidth_eq]
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  have hpos : 0 < Nat.clog 2 (n+1) :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by simp; omega)
  have hprev := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (by omega : 1 < n+1)
  simp only [Nat.pred_eq_sub_one] at hprev
  have hpow : 2^(Nat.clog 2 (n+1)) = 2^(Nat.clog 2 (n+1)-1)*2 := by
    nth_rw 1 [← Nat.sub_add_cancel hpos]
    exact pow_succ _ _
  rw [hpow]
  omega

end
end HierarchicalAbsoluteSpectral
