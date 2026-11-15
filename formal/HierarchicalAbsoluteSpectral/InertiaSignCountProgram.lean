import HierarchicalAbsoluteSpectral.ArithmeticProgram
import HierarchicalAbsoluteSpectral.CoarseAlgebraInertia

/-! Executed pivot-sign counts. Every input entry incurs a comparison;
every counted sign incurs a real addition, including its counter update. -/
namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open ArithmeticProgram hiding pure

def positiveDiagonalCountProgram : {n : ℕ} → (Fin n → ℝ) → ArithmeticProgram ℝ
  | 0, _ => .pure 0
  | n+1, d => do
      let tail ← positiveDiagonalCountProgram (fun i : Fin n => d i.succ)
      .branch (d 0) 0 (fun _ => .pure tail) (fun _ => add tail 1)

@[simp] theorem positiveDiagonalCountProgram_eval {n : ℕ} (d : Fin n → ℝ) :
    (positiveDiagonalCountProgram d).eval=((Finset.univ.filter (fun i => 0 < d i)).card:ℝ) := by
  induction n with
  | zero => simp [positiveDiagonalCountProgram]
  | succ n ih =>
    rw [Fin.card_filter_univ_succ']
    simp only [positiveDiagonalCountProgram,eval_bind,ih,ArithmeticProgram.eval,eval_add]
    by_cases hd : d 0 ≤ 0
    · simp only [dif_pos hd,if_neg (not_lt_of_ge hd),zero_add,Nat.cast_add,Nat.cast_zero]
    · simp only [dif_neg hd,if_pos (lt_of_not_ge hd),Nat.cast_add,Nat.cast_one]
      ring

theorem positiveDiagonalCountProgram_admissible {n : ℕ} (d : Fin n → ℝ) :
    (positiveDiagonalCountProgram d).admissible := by
  induction n with
  | zero => trivial
  | succ n ih =>
    simp only [positiveDiagonalCountProgram,admissible_bind,ih,true_and,ArithmeticProgram.admissible]
    split_ifs <;> trivial

theorem positiveDiagonalCountProgram_work {n : ℕ} (d : Fin n → ℝ) :
    (positiveDiagonalCountProgram d).work=n+(Finset.univ.filter (fun i => 0 < d i)).card := by
  induction n with
  | zero => simp [positiveDiagonalCountProgram]
  | succ n ih =>
    rw [Fin.card_filter_univ_succ']
    simp only [positiveDiagonalCountProgram,work_bind,ih,ArithmeticProgram.work,work_add]
    by_cases hd : d 0 ≤ 0
    · simp only [dif_pos hd,if_neg (not_lt_of_ge hd)]
      omega
    · simp only [dif_neg hd,if_pos (lt_of_not_ge hd)]
      omega

theorem positiveDiagonalCountProgram_work_le {n : ℕ} (d : Fin n → ℝ) :
    (positiveDiagonalCountProgram d).work ≤ 2*n := by
  rw [positiveDiagonalCountProgram_work]
  have hh := Finset.card_filter_le (s := (Finset.univ : Finset (Fin n))) (p := fun i => 0 < d i)
  simp only [Finset.card_univ,Fintype.card_fin] at hh
  omega

def negativeDiagonalCountProgram : {n : ℕ} → (Fin n → ℝ) → ArithmeticProgram ℝ
  | 0, _ => .pure 0
  | n+1, d => do
      let tail ← negativeDiagonalCountProgram (fun i : Fin n => d i.succ)
      .branch 0 (d 0) (fun _ => .pure tail) (fun _ => add tail 1)

@[simp] theorem negativeDiagonalCountProgram_eval {n : ℕ} (d : Fin n → ℝ) :
    (negativeDiagonalCountProgram d).eval=((Finset.univ.filter (fun i => d i < 0)).card:ℝ) := by
  induction n with
  | zero => simp [negativeDiagonalCountProgram]
  | succ n ih =>
    rw [Fin.card_filter_univ_succ']
    simp only [negativeDiagonalCountProgram,eval_bind,ih,ArithmeticProgram.eval,eval_add]
    by_cases hd : 0 ≤ d 0
    · simp only [dif_pos hd,if_neg (not_lt_of_ge hd),zero_add,Nat.cast_add,Nat.cast_zero]
    · simp only [dif_neg hd,if_pos (lt_of_not_ge hd),Nat.cast_add,Nat.cast_one]
      ring

theorem negativeDiagonalCountProgram_admissible {n : ℕ} (d : Fin n → ℝ) :
    (negativeDiagonalCountProgram d).admissible := by
  induction n with
  | zero => trivial
  | succ n ih =>
    simp only [negativeDiagonalCountProgram,admissible_bind,ih,true_and,ArithmeticProgram.admissible]
    split_ifs <;> trivial

theorem negativeDiagonalCountProgram_work {n : ℕ} (d : Fin n → ℝ) :
    (negativeDiagonalCountProgram d).work=n+(Finset.univ.filter (fun i => d i < 0)).card := by
  induction n with
  | zero => simp [negativeDiagonalCountProgram]
  | succ n ih =>
    rw [Fin.card_filter_univ_succ']
    simp only [negativeDiagonalCountProgram,work_bind,ih,ArithmeticProgram.work,work_add]
    by_cases hd : 0 ≤ d 0
    · simp only [dif_pos hd,if_neg (not_lt_of_ge hd)]
      omega
    · simp only [dif_neg hd,if_pos (lt_of_not_ge hd)]
      omega

theorem negativeDiagonalCountProgram_work_le {n : ℕ} (d : Fin n → ℝ) :
    (negativeDiagonalCountProgram d).work ≤ 2*n := by
  rw [negativeDiagonalCountProgram_work]
  have hh := Finset.card_filter_le (s := (Finset.univ : Finset (Fin n))) (p := fun i => d i < 0)
  simp only [Finset.card_univ,Fintype.card_fin] at hh
  omega

namespace FiniteCongruenceDiagonal

@[simp] theorem positiveCountProgram_eval {n : ℕ} {D : Core n} (out : FiniteCongruenceDiagonal D) :
    (positiveDiagonalCountProgram out.diagonal).eval=(out.positiveCount:ℝ) :=
  positiveDiagonalCountProgram_eval out.diagonal

@[simp] theorem negativeCountProgram_eval {n : ℕ} {D : Core n} (out : FiniteCongruenceDiagonal D) :
    (negativeDiagonalCountProgram out.diagonal).eval=(out.negativeCount:ℝ) :=
  negativeDiagonalCountProgram_eval out.diagonal

end FiniteCongruenceDiagonal
end
end HierarchicalAbsoluteSpectral
