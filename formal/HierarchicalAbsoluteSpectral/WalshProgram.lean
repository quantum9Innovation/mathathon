import HierarchicalAbsoluteSpectral.CircuitProgram
import HierarchicalAbsoluteSpectral.ScalarConstruction
import SRHT.Walsh

/-!
The actual fast Walsh transform used by the fast embedding. Its butterfly
recursion materializes both half transforms and charges every addition and
subtraction. The unnormalized transform uses exactly `k*2^k` field operations.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open SRHT
open ArithmeticProgram hiding pure
open scoped BigOperators

def walshSum (k : ℕ) (v : WalshIndex k → ℝ) (a : WalshIndex k) : ℝ :=
  ∑ b, walshChar a b*v b

theorem walshChar_cons {k : ℕ} (a : WalshIndex (k+1)) (b : ZMod 2) (z : WalshIndex k) :
    walshChar a (Fin.cons b z) = bitSign (a 0*b)*walshChar (Fin.tail a) z := by
  simp [walshChar, Fin.prod_univ_succ, Fin.tail]

theorem walshSum_succ (k : ℕ) (v : WalshIndex (k+1) → ℝ) (a : WalshIndex (k+1)) :
    walshSum (k+1) v a =
      walshSum k (fun z => v (Fin.cons 0 z)) (Fin.tail a)+
        bitSign (a 0)*walshSum k (fun z => v (Fin.cons 1 z)) (Fin.tail a) := by
  unfold walshSum
  rw [← (Fin.consEquiv (fun _ : Fin (k+1) => ZMod 2)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ b : ZMod 2, ∑ z : WalshIndex k,
    walshChar a (Fin.cons b z)*v (Fin.cons b z)) = _
  rw [show (Finset.univ : Finset (ZMod 2)) = {0,1} from by decide]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton, walshChar_cons, mul_zero, mul_one, bitSign_zero, one_mul]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  ring

def walshButterflyProgram : (k : ℕ) → (WalshIndex k → ℝ) → ArithmeticProgram (WalshIndex k → ℝ)
  | 0, v => .pure v
  | k+1, v => do
      let u ← walshButterflyProgram k (fun z => v (Fin.cons 0 z))
      let w ← walshButterflyProgram k (fun z => v (Fin.cons 1 z))
      let lo ← finiteTabulateProgram (fun a => add (u a) (w a))
      let hi ← finiteTabulateProgram (fun a => sub (u a) (w a))
      ArithmeticProgram.pure (fun a => if a 0=0 then lo (Fin.tail a) else hi (Fin.tail a))

theorem walshButterflyProgram_eval (k : ℕ) (v : WalshIndex k → ℝ) :
    (walshButterflyProgram k v).eval = walshSum k v := by
  induction k with
  | zero =>
      funext a
      simp only [walshButterflyProgram, eval_pure, walshSum, walshChar,
        Finset.univ_eq_empty, Finset.prod_empty, Fintype.sum_unique, one_mul]
      exact congrArg v (Subsingleton.elim _ _)
  | succ k ih =>
      simp only [walshButterflyProgram, eval_bind, eval_pure, finiteTabulateProgram_eval,
        eval_add, eval_sub]
      funext a
      rw [walshSum_succ, ih, ih]
      by_cases ha : a 0=0 <;> simp [ha, bitSign, sub_eq_add_neg]

@[simp] theorem walshButterflyProgram_work (k : ℕ) (v : WalshIndex k → ℝ) :
    (walshButterflyProgram k v).work = k*2^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [walshButterflyProgram, work_bind, work_pure, add_zero,
        finiteTabulateProgram_work, work_add, work_sub, Finset.sum_const,
        Finset.card_univ, walshIndex_card, smul_eq_mul, mul_one, ih, pow_succ]
      ring

theorem walshButterflyProgram_admissible (k : ℕ) (v : WalshIndex k → ℝ) :
    (walshButterflyProgram k v).admissible := by
  induction k with
  | zero => trivial
  | succ k ih =>
      simp [walshButterflyProgram, ih]

def normalizedWalshProgram (k : ℕ) (v : WalshIndex k → ℝ) : ArithmeticProgram (WalshIndex k → ℝ) := do
  let u ← walshButterflyProgram k v
  let n ← dyadicScaleProgram k
  let c ← sqrt n
  finiteTabulateProgram (fun a => mul c (u a))

theorem normalizedWalshProgram_eval (k : ℕ) (v : WalshIndex k → ℝ) (a : WalshIndex k) :
    (normalizedWalshProgram k v).eval a = (walshMatrix k).mulVec v a := by
  simp only [normalizedWalshProgram, eval_bind, finiteTabulateProgram_eval, eval_mul,
    eval_sqrt, walshButterflyProgram_eval, dyadicScaleProgram_eval]
  rw [one_div, Real.sqrt_inv]
  simp only [Matrix.mulVec, dotProduct, walshMatrix_apply, walshSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem normalizedWalshProgram_work (k : ℕ) (v : WalshIndex k → ℝ) :
    (normalizedWalshProgram k v).work = k*2^k+k+1+2^k := by
  simp [normalizedWalshProgram]
  omega

theorem normalizedWalshProgram_admissible (k : ℕ) (v : WalshIndex k → ℝ) :
    (normalizedWalshProgram k v).admissible := by
  simp [normalizedWalshProgram, walshButterflyProgram_admissible]

end
end HierarchicalAbsoluteSpectral
