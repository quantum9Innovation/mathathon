import HierarchicalAbsoluteSpectral.ExactGramCharpolyProduct
import HierarchicalAbsoluteSpectral.ExactGramCharpolyRankProfileFieldOnly

/-! Schoolbook convolution with two counted field instructions per pair. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Polynomial
open ArithmeticProgram hiding pure

def exactGramConvolutionAux {d e : ℕ}
    (a : ExactGramDensePolynomial d ℝ) (b : ExactGramDensePolynomial e ℝ) :
    List (Fin (d+1) × Fin (e+1)) → ExactGramDensePolynomial (d+e) ℝ →
      ArithmeticProgram (ExactGramDensePolynomial (d+e) ℝ)
  | [], acc => ArithmeticProgram.pure acc
  | ij :: rest, acc => do
    let x ← ArithmeticProgram.mul (a ij.1) (b ij.2)
    let y ← ArithmeticProgram.add (acc (exactGramConvolutionIndex ij)) x
    exactGramConvolutionAux a b rest (Function.update acc (exactGramConvolutionIndex ij) y)

theorem exactGramConvolutionAux_eval {d e : ℕ}
    (a : ExactGramDensePolynomial d ℝ) (b : ExactGramDensePolynomial e ℝ)
    (todo : List (Fin (d+1) × Fin (e+1))) (acc : ExactGramDensePolynomial (d+e) ℝ) :
    exactGramDenseToPolynomial (exactGramConvolutionAux a b todo acc).eval =
      exactGramDenseToPolynomial acc +
        (todo.map (fun ij => monomial (ij.1.val+ij.2.val) (a ij.1*b ij.2))).sum := by
  induction todo generalizing acc with
  | nil => simp [exactGramConvolutionAux]
  | cons ij rest ih =>
    simp only [exactGramConvolutionAux, eval_bind, eval_mul, eval_add]
    rw [ih, exactGramDenseToPolynomial_update]
    simp only [List.map_cons, List.sum_cons, exactGramConvolutionIndex, add_assoc]

theorem exactGramConvolutionAux_work {d e : ℕ}
    (a : ExactGramDensePolynomial d ℝ) (b : ExactGramDensePolynomial e ℝ)
    (todo : List (Fin (d+1) × Fin (e+1))) (acc : ExactGramDensePolynomial (d+e) ℝ) :
    (exactGramConvolutionAux a b todo acc).work = 2*todo.length := by
  induction todo generalizing acc with
  | nil => rfl
  | cons ij rest ih =>
    simp only [exactGramConvolutionAux, work_bind, work_mul, work_add, ih, List.length_cons]
    omega

theorem exactGramConvolutionAux_admissible {d e : ℕ}
    (a : ExactGramDensePolynomial d ℝ) (b : ExactGramDensePolynomial e ℝ)
    (todo : List (Fin (d+1) × Fin (e+1))) (acc : ExactGramDensePolynomial (d+e) ℝ) :
    (exactGramConvolutionAux a b todo acc).admissible := by
  induction todo generalizing acc with
  | nil => trivial
  | cons ij rest ih =>
    simp [exactGramConvolutionAux, ArithmeticProgram.mul, ArithmeticProgram.add,
      ArithmeticOp.admissible, ih]

theorem exactGramConvolutionAux_fieldOnly {d e : ℕ}
    (a : ExactGramDensePolynomial d ℝ) (b : ExactGramDensePolynomial e ℝ)
    (todo : List (Fin (d+1) × Fin (e+1))) (acc : ExactGramDensePolynomial (d+e) ℝ) :
    (exactGramConvolutionAux a b todo acc).rankProfileFieldOnly := by
  induction todo generalizing acc with
  | nil => trivial
  | cons ij rest ih =>
    simp only [exactGramConvolutionAux, rankProfileFieldOnly_bind,
      rankProfileFieldOnly_mul, rankProfileFieldOnly_add, ih, and_self]

def exactGramConvolutionProgram {d e : ℕ}
    (a : ExactGramDensePolynomial d ℝ) (b : ExactGramDensePolynomial e ℝ) :
    ArithmeticProgram (ExactGramDensePolynomial (d+e) ℝ) :=
  exactGramConvolutionAux a b (exactGramConvolutionPairs d e) 0

theorem exactGramConvolutionProgram_eval {d e : ℕ}
    (a : ExactGramDensePolynomial d ℝ) (b : ExactGramDensePolynomial e ℝ) :
    exactGramDenseToPolynomial (exactGramConvolutionProgram a b).eval =
      exactGramDenseToPolynomial a * exactGramDenseToPolynomial b := by
  rw [exactGramConvolutionProgram, exactGramConvolutionAux_eval,
    exactGramDenseToPolynomial_zero, zero_add, exactGramConvolutionPairs_sum]

theorem exactGramConvolutionProgram_work {d e : ℕ}
    (a : ExactGramDensePolynomial d ℝ) (b : ExactGramDensePolynomial e ℝ) :
    (exactGramConvolutionProgram a b).work = 2*(d+1)*(e+1) := by
  rw [exactGramConvolutionProgram, exactGramConvolutionAux_work, exactGramConvolutionPairs_length]
  ring

theorem exactGramConvolutionProgram_admissible {d e : ℕ}
    (a : ExactGramDensePolynomial d ℝ) (b : ExactGramDensePolynomial e ℝ) :
    (exactGramConvolutionProgram a b).admissible := exactGramConvolutionAux_admissible _ _ _ _

theorem exactGramConvolutionProgram_fieldOnly {d e : ℕ}
    (a : ExactGramDensePolynomial d ℝ) (b : ExactGramDensePolynomial e ℝ) :
    (exactGramConvolutionProgram a b).rankProfileFieldOnly := exactGramConvolutionAux_fieldOnly _ _ _ _

end
end HierarchicalAbsoluteSpectral
