import HierarchicalAbsoluteSpectral.ExactGramCharpolyProductProgram
import HierarchicalAbsoluteSpectral.ExactGramCharpolyCompanion

/-! Materialize the signs in companion factors, then multiply their arrays. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Polynomial
open ArithmeticProgram hiding pure
open scoped BigOperators

def exactGramCompanionDense {R : Type*} [CommRing R] {d : ℕ}
    (c : Fin d → R) : ExactGramDensePolynomial d R := Fin.snoc (fun i => -c i) 1

theorem exactGramCompanionDense_toPolynomial {R : Type*} [CommRing R] {d : ℕ}
    (c : Fin d → R) :
    exactGramDenseToPolynomial (exactGramCompanionDense c) = exactGramCompanionPolynomial c := by
  simp only [exactGramCompanionDense, exactGramDenseToPolynomial, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, map_neg,
    Finset.sum_neg_distrib, Polynomial.monomial_one_right_eq_X_pow]
  simp only [exactGramCompanionPolynomial, Polynomial.C_mul_X_pow_eq_monomial, sub_eq_add_neg]
  exact add_comm _ _

def exactGramCompanionFactorProgram {d : ℕ} (c : Fin d → ℝ) :
    ArithmeticProgram (ExactGramDensePolynomial d ℝ) := do
  let lower ← tabulate d (fun i => ArithmeticProgram.sub 0 (c i))
  ArithmeticProgram.pure (Fin.snoc lower 1)

@[simp] theorem exactGramCompanionFactorProgram_eval {d : ℕ} (c : Fin d → ℝ) :
    (exactGramCompanionFactorProgram c).eval = exactGramCompanionDense c := by
  simp [exactGramCompanionFactorProgram, exactGramCompanionDense]

theorem exactGramCompanionFactorProgram_toPolynomial {d : ℕ} (c : Fin d → ℝ) :
    exactGramDenseToPolynomial (exactGramCompanionFactorProgram c).eval =
      exactGramCompanionPolynomial c := by
  rw [exactGramCompanionFactorProgram_eval, exactGramCompanionDense_toPolynomial]

@[simp] theorem exactGramCompanionFactorProgram_work {d : ℕ} (c : Fin d → ℝ) :
    (exactGramCompanionFactorProgram c).work = d := by
  simp [exactGramCompanionFactorProgram]

theorem exactGramCompanionFactorProgram_admissible {d : ℕ} (c : Fin d → ℝ) :
    (exactGramCompanionFactorProgram c).admissible := by
  simp [exactGramCompanionFactorProgram]

theorem exactGramCompanionFactorProgram_fieldOnly {d : ℕ} (c : Fin d → ℝ) :
    (exactGramCompanionFactorProgram c).rankProfileFieldOnly := by
  simp [exactGramCompanionFactorProgram]

def exactGramCompanionProductAuxProgram : (t : ℕ) → (degree : Fin t → ℕ) →
    (∀ j, Fin (degree j) → ℝ) →
      ArithmeticProgram (ExactGramDensePolynomial (∑ j, degree j) ℝ)
  | 0, _, _ => ArithmeticProgram.pure (fun _ => 1)
  | t+1, degree, c => do
    let head ← exactGramCompanionFactorProgram (c 0)
    let tail ← exactGramCompanionProductAuxProgram t (fun j => degree j.succ) (fun j => c j.succ)
    let out ← exactGramConvolutionProgram head tail
    ArithmeticProgram.pure (exactGramDenseCast (Fin.sum_univ_succ degree).symm out)

def exactGramCompanionProductProgram {t : ℕ} (degree : Fin t → ℕ)
    (c : ∀ j, Fin (degree j) → ℝ) :
    ArithmeticProgram (ExactGramDensePolynomial (∑ j, degree j) ℝ) :=
  exactGramCompanionProductAuxProgram t degree c

theorem exactGramCompanionProductAuxProgram_eval (t : ℕ) (degree : Fin t → ℕ)
    (c : ∀ j, Fin (degree j) → ℝ) :
    exactGramDenseToPolynomial (exactGramCompanionProductAuxProgram t degree c).eval =
      ∏ j, exactGramCompanionPolynomial (c j) := by
  induction t with
  | zero => simp [exactGramCompanionProductAuxProgram, exactGramDenseToPolynomial]
  | succ t ih =>
    simp only [exactGramCompanionProductAuxProgram, eval_bind, eval_pure,
      exactGramDenseToPolynomial_cast, exactGramConvolutionProgram_eval,
      exactGramCompanionFactorProgram_toPolynomial, Fin.prod_univ_succ, ih]

theorem exactGramCompanionProductProgram_eval {t : ℕ} (degree : Fin t → ℕ)
    (c : ∀ j, Fin (degree j) → ℝ) :
    exactGramDenseToPolynomial (exactGramCompanionProductProgram degree c).eval =
      ∏ j, exactGramCompanionPolynomial (c j) :=
  exactGramCompanionProductAuxProgram_eval t degree c

theorem exactGramCompanionProductAuxProgram_work (t : ℕ) (degree : Fin t → ℕ)
    (c : ∀ j, Fin (degree j) → ℝ) :
    (exactGramCompanionProductAuxProgram t degree c).work =
      (∑ j, degree j) + exactGramDenseProductCost t degree := by
  induction t with
  | zero => simp [exactGramCompanionProductAuxProgram, exactGramDenseProductCost]
  | succ t ih =>
    simp only [exactGramCompanionProductAuxProgram, exactGramDenseProductCost, work_bind,
      exactGramCompanionFactorProgram_work, exactGramConvolutionProgram_work, work_pure,
      add_zero, ih, Fin.sum_univ_succ]
    omega

theorem exactGramCompanionProductProgram_work {t : ℕ} (degree : Fin t → ℕ)
    (c : ∀ j, Fin (degree j) → ℝ) :
    (exactGramCompanionProductProgram degree c).work =
      (∑ j, degree j) + exactGramDenseProductCost t degree :=
  exactGramCompanionProductAuxProgram_work t degree c

theorem exactGramCompanionProductAuxProgram_admissible (t : ℕ) (degree : Fin t → ℕ)
    (c : ∀ j, Fin (degree j) → ℝ) :
    (exactGramCompanionProductAuxProgram t degree c).admissible := by
  induction t with
  | zero => trivial
  | succ t ih =>
    simp only [exactGramCompanionProductAuxProgram, admissible_bind,
      exactGramCompanionFactorProgram_admissible, exactGramConvolutionProgram_admissible,
      admissible_pure, ih, and_self]

theorem exactGramCompanionProductProgram_admissible {t : ℕ} (degree : Fin t → ℕ)
    (c : ∀ j, Fin (degree j) → ℝ) :
    (exactGramCompanionProductProgram degree c).admissible :=
  exactGramCompanionProductAuxProgram_admissible t degree c

theorem exactGramCompanionProductAuxProgram_fieldOnly (t : ℕ) (degree : Fin t → ℕ)
    (c : ∀ j, Fin (degree j) → ℝ) :
    (exactGramCompanionProductAuxProgram t degree c).rankProfileFieldOnly := by
  induction t with
  | zero => trivial
  | succ t ih =>
    simp only [exactGramCompanionProductAuxProgram, rankProfileFieldOnly_bind,
      exactGramCompanionFactorProgram_fieldOnly, exactGramConvolutionProgram_fieldOnly,
      rankProfileFieldOnly_pure, ih, and_self]

theorem exactGramCompanionProductProgram_fieldOnly {t : ℕ} (degree : Fin t → ℕ)
    (c : ∀ j, Fin (degree j) → ℝ) :
    (exactGramCompanionProductProgram degree c).rankProfileFieldOnly :=
  exactGramCompanionProductAuxProgram_fieldOnly t degree c

theorem exactGramCompanionProductProgram_work_bound {t : ℕ} (degree : Fin t → ℕ)
    (c : ∀ j, Fin (degree j) → ℝ)
    (n : ℕ) (ht : t ≤ n) (hd : (∑ j, degree j) ≤ n) :
    (exactGramCompanionProductProgram degree c).work ≤ 9*(n+1)^2 := by
  rw [exactGramCompanionProductProgram_work]
  have hc : exactGramDenseProductCost t degree ≤ 8*n^2 := by
    calc
      _ ≤ 2*((∑ j, degree j)+t)^2 := exactGramDenseProductCost_bound t degree
      _ ≤ 2*(n+n)^2 := by gcongr
      _ = _ := by ring
  nlinarith

end
end HierarchicalAbsoluteSpectral
