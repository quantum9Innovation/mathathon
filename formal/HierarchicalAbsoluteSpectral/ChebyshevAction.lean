import HierarchicalAbsoluteSpectral.BlockPrograms
import HierarchicalAbsoluteSpectral.PolynomialConstruction

/-! Applying a Chebyshev coefficient table without changing basis or
forming polynomial matrix powers. The supplied matrix-action program
is reused once per recurrence step; its operation bound is explicit. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure
open Polynomial Polynomial.Chebyshev
variable {k b : ℕ}

def chebyshevBlock (A : Core k) (V : Matrix (Fin k) (Fin b) ℝ) (i : ℤ) :
    Matrix (Fin k) (Fin b) ℝ := aeval A (T ℝ i)*V

theorem chebyshevBlock_next (A : Core k) (V : Matrix (Fin k) (Fin b) ℝ) (i : ℤ) :
    chebyshevBlock A V (i+1) = (2:ℝ) • (A*chebyshevBlock A V i)-chebyshevBlock A V (i-1) := by
  unfold chebyshevBlock
  rw [T_add_one, ← C_ofNat, map_sub, map_mul, map_mul, Polynomial.aeval_C, aeval_X,
    Algebra.algebraMap_eq_smul_one]
  simp only [Matrix.sub_mul, Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul]

def chebyshevActionLoop (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)) (a : ℤ → ℝ) :
    ℕ → ℤ → Matrix (Fin k) (Fin b) ℝ → Matrix (Fin k) (Fin b) ℝ →
      Matrix (Fin k) (Fin b) ℝ → ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)
  | 0, _, _, _, acc => .pure acc
  | m+1, i, prev, curr, acc => do
      let q ← action curr
      let twice ← blockScaleProgram 2 q
      let next ← blockSubProgram twice prev
      let term ← blockScaleProgram (a (i+1)) next
      let total ← blockAddProgram acc term
      chebyshevActionLoop action a m (i+1) curr next total

theorem chebyshevActionLoop_eval (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)) (A : Core k)
    (hact : ∀ X, (action X).eval = A*X) (a : ℤ → ℝ) (m : ℕ) (i : ℤ)
    (V acc : Matrix (Fin k) (Fin b) ℝ) :
    (chebyshevActionLoop action a m i (chebyshevBlock A V (i-1)) (chebyshevBlock A V i) acc).eval =
      acc+∑ j ∈ Finset.range m, a (i+(j : ℤ)+1) • chebyshevBlock A V (i+(j : ℤ)+1) := by
  induction m generalizing i acc with
  | zero => simp [chebyshevActionLoop]
  | succ m ih =>
    simp only [chebyshevActionLoop, eval_bind, hact, blockScaleProgram_eval,
      blockSubProgram_eval, blockAddProgram_eval, ← chebyshevBlock_next]
    have hprev : i = (i+1)-1 := by omega
    conv_lhs => arg 1; arg 5; rw [hprev]
    rw [ih]
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
    have hs : (∑ j ∈ Finset.range m, a (i+1+(j : ℤ)+1) • chebyshevBlock A V (i+1+(j : ℤ)+1)) =
        ∑ j ∈ Finset.range m, a (i+((j : ℤ)+1)+1) • chebyshevBlock A V (i+((j : ℤ)+1)+1) := by
      apply Finset.sum_congr rfl
      intro j hj
      have he : i+1+(j : ℤ)+1 = i+((j : ℤ)+1)+1 := by omega
      rw [he]
    rw [hs]
    module

theorem chebyshevActionLoop_work (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)) (T : ℕ)
    (hwork : ∀ X, (action X).work ≤ T) (a : ℤ → ℝ) (m : ℕ) (i : ℤ)
    (prev curr acc : Matrix (Fin k) (Fin b) ℝ) :
    (chebyshevActionLoop action a m i prev curr acc).work ≤ m*(T+4*k*b) := by
  induction m generalizing i prev curr acc with
  | zero => simp [chebyshevActionLoop]
  | succ m ih =>
    simp only [chebyshevActionLoop, work_bind, blockScaleProgram_work,
      blockSubProgram_work, blockAddProgram_work]
    have hi := ih (i+1) curr
      (blockSubProgram (blockScaleProgram 2 (action curr).eval).eval prev).eval
      (blockAddProgram acc (blockScaleProgram (a (i+1))
        (blockSubProgram (blockScaleProgram 2 (action curr).eval).eval prev).eval).eval).eval
    have h := hwork curr
    nlinarith

theorem chebyshevActionLoop_admissible (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ))
    (hvalid : ∀ X, (action X).admissible) (a : ℤ → ℝ) (m : ℕ) (i : ℤ)
    (prev curr acc : Matrix (Fin k) (Fin b) ℝ) :
    (chebyshevActionLoop action a m i prev curr acc).admissible := by
  induction m generalizing i prev curr acc with
  | zero => trivial
  | succ m ih => simp [chebyshevActionLoop, ih, hvalid]

def chebyshevActionProgram (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)) (a : ℤ → ℝ) :
    ℕ → Matrix (Fin k) (Fin b) ℝ → ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)
  | 0, _ => .pure 0
  | n+1, V => do
      let prev ← action V
      let acc ← blockScaleProgram (a 0) V
      chebyshevActionLoop action a n 0 prev V acc

theorem chebyshevActionProgram_eval (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)) (A : Core k)
    (hact : ∀ X, (action X).eval = A*X) (a : ℤ → ℝ) (n : ℕ)
    (V : Matrix (Fin k) (Fin b) ℝ) :
    (chebyshevActionProgram action a n V).eval =
      aeval A (∑ j ∈ Finset.range n, a (j : ℤ) • T ℝ (j : ℤ))*V := by
  cases n with
  | zero => simp [chebyshevActionProgram]
  | succ n =>
    simp only [chebyshevActionProgram, eval_bind, hact, blockScaleProgram_eval]
    have hl := chebyshevActionLoop_eval action A hact a n 0 V (a 0 • V)
    simp only [zero_sub, zero_add, chebyshevBlock, T_neg_one, T_zero,
      aeval_X, map_one, Matrix.one_mul] at hl
    rw [Finset.sum_range_succ']
    simp only [map_add, map_sum, map_smul, Matrix.add_mul, Matrix.sum_mul,
      Matrix.smul_mul, Nat.cast_zero, Nat.cast_add, Nat.cast_one, T_zero,
      map_one, Matrix.one_mul]
    exact hl.trans (add_comm _ _)

theorem chebyshevActionProgram_work (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)) (T : ℕ)
    (hwork : ∀ X, (action X).work ≤ T) (a : ℤ → ℝ) (n : ℕ)
    (V : Matrix (Fin k) (Fin b) ℝ) :
    (chebyshevActionProgram action a n V).work ≤ n*(T+4*k*b) := by
  cases n with
  | zero => simp [chebyshevActionProgram]
  | succ n =>
    simp only [chebyshevActionProgram, work_bind, blockScaleProgram_work, blockScaleProgram_eval]
    have hl := chebyshevActionLoop_work action T hwork a n 0 (action V).eval V (a 0 • V)
    have h := hwork V
    nlinarith

theorem chebyshevActionProgram_admissible (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ))
    (hvalid : ∀ X, (action X).admissible) (a : ℤ → ℝ) (n : ℕ)
    (V : Matrix (Fin k) (Fin b) ℝ) : (chebyshevActionProgram action a n V).admissible := by
  cases n with
  | zero => trivial
  | succ n => simp [chebyshevActionProgram, hvalid, chebyshevActionLoop_admissible]

def integerCoefficient (n : ℕ) (a : Fin n → ℝ) (i : ℤ) : ℝ :=
  if hi : 0 ≤ i ∧ i < n then a ⟨i.toNat, by omega⟩ else 0

theorem integerCoefficient_at_fin (n : ℕ) (a : Fin n → ℝ) (i : Fin n) :
    integerCoefficient n a (i.val : ℤ) = a i := by
  unfold integerCoefficient
  rw [dif_pos (by exact_mod_cast (show 0 ≤ i.val ∧ i.val < n from ⟨Nat.zero_le _, i.isLt⟩))]
  rfl

theorem polynomialFromChebyshevCoefficients_eq_sum (s : ℕ) (a : Fin (2^s) → ℝ) :
    polynomialFromChebyshevCoefficients s a =
      ∑ j ∈ Finset.range (2^s), integerCoefficient (2^s) a (j : ℤ) • T ℝ (j : ℤ) := by
  rw [polynomialFromChebyshevCoefficients]
  calc
    _ = ∑ j : Fin (2^s), integerCoefficient (2^s) a (j.val : ℤ) • T ℝ (j.val : ℤ) := by
      simp only [integerCoefficient_at_fin]
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun j : ℕ => integerCoefficient (2^s) a (j : ℤ) • T ℝ (j : ℤ)) (2^s)

/-- Applying the table produced by the coefficient algorithm takes at most
n operator calls and 4nkb additional real operations on a k-by-b block. -/
theorem chebyshevTableAction_specification (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)) (A : Core k) (T s : ℕ)
    (hact : ∀ X, (action X).eval = A*X) (hwork : ∀ X, (action X).work ≤ T)
    (hvalid : ∀ X, (action X).admissible) (a : Fin (2^s) → ℝ)
    (V : Matrix (Fin k) (Fin b) ℝ) :
    let P := chebyshevActionProgram action (integerCoefficient (2^s) a) (2^s) V
    P.admissible ∧ P.eval = aeval A (polynomialFromChebyshevCoefficients s a)*V ∧
      P.work ≤ (2^s)*(T+4*k*b) := by
  refine ⟨chebyshevActionProgram_admissible action hvalid _ _ V, ?_,
    chebyshevActionProgram_work action T hwork _ _ V⟩
  rw [chebyshevActionProgram_eval action A hact, polynomialFromChebyshevCoefficients_eq_sum]

end
end HierarchicalAbsoluteSpectral
