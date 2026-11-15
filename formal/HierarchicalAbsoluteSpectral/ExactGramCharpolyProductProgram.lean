import HierarchicalAbsoluteSpectral.ExactGramCharpolyProductConvolution

/-!
Products of degree-bounded coefficient arrays. The work bound uses the
combined degree and factor count, including factors of degree zero.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Polynomial
open ArithmeticProgram hiding pure
open scoped BigOperators

def exactGramDenseProductAuxProgram : (t : ℕ) → (degree : Fin t → ℕ) →
    (∀ j, ExactGramDensePolynomial (degree j) ℝ) →
      ArithmeticProgram (ExactGramDensePolynomial (∑ j, degree j) ℝ)
  | 0, _, _ => ArithmeticProgram.pure (fun _ => 1)
  | t+1, degree, factors => do
    let tail ← exactGramDenseProductAuxProgram t (fun j => degree j.succ) (fun j => factors j.succ)
    let out ← exactGramConvolutionProgram (factors 0) tail
    ArithmeticProgram.pure (exactGramDenseCast (Fin.sum_univ_succ degree).symm out)

def exactGramDenseProductProgram {t : ℕ} (degree : Fin t → ℕ)
    (factors : ∀ j, ExactGramDensePolynomial (degree j) ℝ) :
    ArithmeticProgram (ExactGramDensePolynomial (∑ j, degree j) ℝ) :=
  exactGramDenseProductAuxProgram t degree factors

def exactGramDenseProductCost : (t : ℕ) → (Fin t → ℕ) → ℕ
  | 0, _ => 0
  | t+1, degree => exactGramDenseProductCost t (fun j => degree j.succ) +
    2*(degree 0+1)*((∑ j : Fin t, degree j.succ)+1)

theorem exactGramDenseProductAuxProgram_eval (t : ℕ) (degree : Fin t → ℕ)
    (factors : ∀ j, ExactGramDensePolynomial (degree j) ℝ) :
    exactGramDenseToPolynomial (exactGramDenseProductAuxProgram t degree factors).eval =
      ∏ j, exactGramDenseToPolynomial (factors j) := by
  induction t with
  | zero => simp [exactGramDenseProductAuxProgram, exactGramDenseToPolynomial]
  | succ t ih =>
    simp only [exactGramDenseProductAuxProgram, eval_bind, eval_pure,
      exactGramDenseToPolynomial_cast, exactGramConvolutionProgram_eval,
      Fin.prod_univ_succ, ih]

theorem exactGramDenseProductProgram_eval {t : ℕ} (degree : Fin t → ℕ)
    (factors : ∀ j, ExactGramDensePolynomial (degree j) ℝ) :
    exactGramDenseToPolynomial (exactGramDenseProductProgram degree factors).eval =
      ∏ j, exactGramDenseToPolynomial (factors j) :=
  exactGramDenseProductAuxProgram_eval t degree factors

theorem exactGramDenseProductAuxProgram_work (t : ℕ) (degree : Fin t → ℕ)
    (factors : ∀ j, ExactGramDensePolynomial (degree j) ℝ) :
    (exactGramDenseProductAuxProgram t degree factors).work = exactGramDenseProductCost t degree := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [exactGramDenseProductAuxProgram, exactGramDenseProductCost, work_bind,
      exactGramConvolutionProgram_work, work_pure, add_zero, ih]

theorem exactGramDenseProductProgram_work {t : ℕ} (degree : Fin t → ℕ)
    (factors : ∀ j, ExactGramDensePolynomial (degree j) ℝ) :
    (exactGramDenseProductProgram degree factors).work = exactGramDenseProductCost t degree :=
  exactGramDenseProductAuxProgram_work t degree factors

theorem exactGramDenseProductAuxProgram_admissible (t : ℕ) (degree : Fin t → ℕ)
    (factors : ∀ j, ExactGramDensePolynomial (degree j) ℝ) :
    (exactGramDenseProductAuxProgram t degree factors).admissible := by
  induction t with
  | zero => trivial
  | succ t ih =>
    simp only [exactGramDenseProductAuxProgram, admissible_bind, exactGramConvolutionProgram_admissible,
      admissible_pure, and_true, ih]

theorem exactGramDenseProductProgram_admissible {t : ℕ} (degree : Fin t → ℕ)
    (factors : ∀ j, ExactGramDensePolynomial (degree j) ℝ) :
    (exactGramDenseProductProgram degree factors).admissible :=
  exactGramDenseProductAuxProgram_admissible t degree factors

theorem exactGramDenseProductAuxProgram_fieldOnly (t : ℕ) (degree : Fin t → ℕ)
    (factors : ∀ j, ExactGramDensePolynomial (degree j) ℝ) :
    (exactGramDenseProductAuxProgram t degree factors).rankProfileFieldOnly := by
  induction t with
  | zero => trivial
  | succ t ih =>
    simp only [exactGramDenseProductAuxProgram, rankProfileFieldOnly_bind,
      exactGramConvolutionProgram_fieldOnly, rankProfileFieldOnly_pure, and_true, ih]

theorem exactGramDenseProductProgram_fieldOnly {t : ℕ} (degree : Fin t → ℕ)
    (factors : ∀ j, ExactGramDensePolynomial (degree j) ℝ) :
    (exactGramDenseProductProgram degree factors).rankProfileFieldOnly :=
  exactGramDenseProductAuxProgram_fieldOnly t degree factors

theorem exactGramDenseProductCost_bound (t : ℕ) (degree : Fin t → ℕ) :
    exactGramDenseProductCost t degree ≤ 2*((∑ j, degree j)+t)^2 := by
  induction t with
  | zero => simp [exactGramDenseProductCost]
  | succ t ih =>
    have hh := ih (fun j => degree j.succ)
    rw [exactGramDenseProductCost, Fin.sum_univ_succ]
    let a := degree 0
    let b := ∑ j : Fin t, degree j.succ
    change exactGramDenseProductCost t (fun j => degree j.succ) + 2*(a+1)*(b+1) ≤
      2*(a+b+(t+1))^2
    change exactGramDenseProductCost t (fun j => degree j.succ) ≤ 2*(b+t)^2 at hh
    have hpos : 0 ≤ (a+1)*(a+b+2*t) := Nat.zero_le _
    nlinarith

theorem exactGramDenseProductProgram_work_bound {t : ℕ} (degree : Fin t → ℕ)
    (factors : ∀ j, ExactGramDensePolynomial (degree j) ℝ)
    (n : ℕ) (ht : t ≤ n) (hd : (∑ j, degree j) ≤ n) :
    (exactGramDenseProductProgram degree factors).work ≤ 8*n^2 := by
  rw [exactGramDenseProductProgram_work]
  calc
    _ ≤ 2*((∑ j, degree j)+t)^2 := exactGramDenseProductCost_bound t degree
    _ ≤ 2*(n+n)^2 := by gcongr
    _ = _ := by ring

end
end HierarchicalAbsoluteSpectral
