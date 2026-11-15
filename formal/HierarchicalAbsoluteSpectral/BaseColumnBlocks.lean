import HierarchicalAbsoluteSpectral.CoarseAlgebraBlockedKernels
import Mathlib.Algebra.Order.Floor.Div

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Matmul.UniversalPaddedAlgorithm
open ArithmeticProgram hiding pure
open scoped BigOperators

def actionColumnBlockCount (w b : ℕ) : ℕ := w ⌈/⌉ b

theorem actionColumnBlockCount_fits (w b : ℕ) (hb : 0 < b) :
    w ≤ actionColumnBlockCount w b*b := by
  simpa only [actionColumnBlockCount,smul_eq_mul,Nat.mul_comm] using
    (le_smul_ceilDiv hb : w ≤ b • (w ⌈/⌉ b))

theorem actionColumnBlockCount_le (w b : ℕ) (hb : 0 < b) :
    actionColumnBlockCount w b ≤ w/b+1 := by
  apply (ceilDiv_le_iff_le_mul hb).mpr
  simpa only [multiplicationBlockCount,Nat.mul_comm] using multiplicationBlockCount_fits w b hb

def actionColumnInput {m : ℕ} (b w : ℕ) (hb : 0 < b)
    (V : Matrix (Fin m) (Fin w) ℝ) (s : Fin (actionColumnBlockCount w b)) :
    Matrix (Fin m) (Fin b) ℝ :=
  (pad (Function.Embedding.refl (Fin m))
    (Fin.castLEEmb (actionColumnBlockCount_fits w b hb)) V).submatrix id
      (fun i => finProdFinEquiv (s,i))

def MatrixAction.columnBlocks {n m b : ℕ} {A : Matrix (Fin n) (Fin m) ℝ}
    (P : MatrixAction A b) (hb : 0 < b) (w : ℕ) : MatrixAction A w where
  program V := do
    let out ← tabulate (actionColumnBlockCount w b) (fun s => P.program (actionColumnInput b w hb V s))
    .pure (Matrix.of (fun i j =>
      let e := Fin.castLEEmb (actionColumnBlockCount_fits w b hb)
      let sb := finProdFinEquiv.symm (e j)
      out sb.1 i sb.2))
  correct V := by
    simp only [eval_bind,eval_tabulate,eval_pure,P.correct]
    ext i j
    change (A*actionColumnInput b w hb V
      (finProdFinEquiv.symm (Fin.castLEEmb (actionColumnBlockCount_fits w b hb) j)).1) i
        (finProdFinEquiv.symm (Fin.castLEEmb (actionColumnBlockCount_fits w b hb) j)).2 = (A*V) i j
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    change pad (Function.Embedding.refl (Fin m))
      (Fin.castLEEmb (actionColumnBlockCount_fits w b hb)) V a
      (finProdFinEquiv (finProdFinEquiv.symm
        (Fin.castLEEmb (actionColumnBlockCount_fits w b hb) j))) = V a j
    rw [Equiv.apply_symm_apply]
    exact pad_apply (Function.Embedding.refl (Fin m))
      (Fin.castLEEmb (actionColumnBlockCount_fits w b hb)) V a j
  valid V := by
    simp only [admissible_bind,admissible_tabulate,P.valid,admissible_pure,and_self,implies_true]
  cost := actionColumnBlockCount w b*P.cost
  work_le V := by
    simp only [work_bind,work_tabulate,work_pure,add_zero]
    calc
      _ ≤ ∑ _s : Fin (actionColumnBlockCount w b), P.cost := Finset.sum_le_sum (fun _ _ => P.work_le _)
      _ = _ := by simp

@[simp] theorem MatrixAction.columnBlocks_cost {n m b : ℕ} {A : Matrix (Fin n) (Fin m) ℝ}
    (P : MatrixAction A b) (hb : 0 < b) (w : ℕ) :
    (P.columnBlocks hb w).cost = actionColumnBlockCount w b*P.cost := rfl

theorem MatrixAction.columnBlocks_cost_le {n m b : ℕ} {A : Matrix (Fin n) (Fin m) ℝ}
    (P : MatrixAction A b) (hb : 0 < b) (w : ℕ) :
    (P.columnBlocks hb w).cost ≤ (w/b+1)*P.cost :=
  Nat.mul_le_mul_right _ (actionColumnBlockCount_le w b hb)

@[simp] theorem MatrixAction.columnBlocks_zero_cost {n m b : ℕ} {A : Matrix (Fin n) (Fin m) ℝ}
    (P : MatrixAction A b) (hb : 0 < b) : (P.columnBlocks hb 0).cost = 0 := by
  simp [MatrixAction.columnBlocks_cost,actionColumnBlockCount]

end
end HierarchicalAbsoluteSpectral
