import HierarchicalAbsoluteSpectral.WalshProgram
import SRHT.Main

/-!
Operational two-round Walsh embedding, with explicit sampled rows. The input
signs and row set are the random data of `SRHT.sketchLaw`; producing these data
from Gaussian instructions is a separate sampler obligation.
-/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open SRHT
open ArithmeticProgram hiding pure
open scoped BigOperators

def walshBlockProgram {k b : ℕ} (V : Matrix (WalshIndex k) (Fin b) ℝ) :
    ArithmeticProgram (Matrix (WalshIndex k) (Fin b) ℝ) := do
  let cols ← tabulate b (fun j => normalizedWalshProgram k (fun i => V i j))
  ArithmeticProgram.pure (Matrix.of (fun i j => cols j i))

@[simp] theorem walshBlockProgram_eval {k b : ℕ} (V : Matrix (WalshIndex k) (Fin b) ℝ) :
    (walshBlockProgram V).eval = walshMatrix k*V := by
  simp only [walshBlockProgram, eval_bind, eval_tabulate, eval_pure]
  ext i j
  exact normalizedWalshProgram_eval k (fun i => V i j) i

@[simp] theorem walshBlockProgram_work {k b : ℕ} (V : Matrix (WalshIndex k) (Fin b) ℝ) :
    (walshBlockProgram V).work = b*(k*2^k+k+1+2^k) := by
  simp [walshBlockProgram, normalizedWalshProgram_work]

theorem walshBlockProgram_admissible {k b : ℕ} (V : Matrix (WalshIndex k) (Fin b) ℝ) :
    (walshBlockProgram V).admissible := by
  simp [walshBlockProgram, normalizedWalshProgram_admissible]

def signBlockProgram {k b : ℕ} (x : SignAssignment k) (V : Matrix (WalshIndex k) (Fin b) ℝ) :
    ArithmeticProgram (Matrix (WalshIndex k) (Fin b) ℝ) := do
  let rows ← finiteTabulateProgram (fun i : WalshIndex k =>
    tabulate b (fun j => mul (bitSign (x i)) (V i j)))
  ArithmeticProgram.pure (Matrix.of rows)

@[simp] theorem signBlockProgram_eval {k b : ℕ} (x : SignAssignment k)
    (V : Matrix (WalshIndex k) (Fin b) ℝ) : (signBlockProgram x V).eval = signDiagonal x*V := by
  simp only [signBlockProgram, eval_bind, finiteTabulateProgram_eval, eval_tabulate,
    eval_mul, eval_pure]
  ext i j
  simp [signDiagonal, Matrix.diagonal_mul]

@[simp] theorem signBlockProgram_work {k b : ℕ} (x : SignAssignment k)
    (V : Matrix (WalshIndex k) (Fin b) ℝ) : (signBlockProgram x V).work = 2^k*b := by
  simp [signBlockProgram]

theorem signBlockProgram_admissible {k b : ℕ} (x : SignAssignment k)
    (V : Matrix (WalshIndex k) (Fin b) ℝ) : (signBlockProgram x V).admissible := by
  simp [signBlockProgram]

def sampleBlockProgram {k b : ℕ} (T : Finset (WalshIndex k))
    (V : Matrix (WalshIndex k) (Fin b) ℝ) : ArithmeticProgram (Matrix T (Fin b) ℝ) := do
  let nInv ← dyadicScaleProgram k
  let d ← mul nInv (T.card:ℝ)
  let r ← div 1 d
  let c ← sqrt r
  let rows ← finiteTabulateProgram (fun i : T => tabulate b (fun j => mul c (V i.val j)))
  ArithmeticProgram.pure (Matrix.of rows)

@[simp] theorem sampleBlockProgram_eval {k b : ℕ} (T : Finset (WalshIndex k))
    (V : Matrix (WalshIndex k) (Fin b) ℝ) :
    (sampleBlockProgram T V).eval = Matrix.of (fun i j => Real.sqrt ((2^k:ℝ)/T.card)*V i.val j) := by
  have hr : (1:ℝ)/((1/(2^k:ℝ))*(T.card:ℝ)) = (2^k:ℝ)/T.card := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
    ring
  simp only [sampleBlockProgram, eval_bind, dyadicScaleProgram_eval, eval_mul, eval_div,
    eval_sqrt, finiteTabulateProgram_eval, eval_tabulate, eval_pure, hr]

@[simp] theorem sampleBlockProgram_work {k b : ℕ} (T : Finset (WalshIndex k))
    (V : Matrix (WalshIndex k) (Fin b) ℝ) : (sampleBlockProgram T V).work = k+3+T.card*b := by
  simp [sampleBlockProgram]
  omega

theorem sampleBlockProgram_admissible {k b : ℕ} (T : Finset (WalshIndex k))
    (hT : 0<T.card) (V : Matrix (WalshIndex k) (Fin b) ℝ) :
    (sampleBlockProgram T V).admissible := by
  have hd : 0 < (1/(2^k:ℝ))*(T.card:ℝ) := by positivity
  simp [sampleBlockProgram, (Finset.card_pos.mp hT).ne_empty]

def embeddingProgram {k b : ℕ} (x y : SignAssignment k) (T : Finset (WalshIndex k))
    (V : Matrix (WalshIndex k) (Fin b) ℝ) : ArithmeticProgram (Matrix T (Fin b) ℝ) := do
  let V₁ ← signBlockProgram x V
  let V₂ ← walshBlockProgram V₁
  let V₃ ← signBlockProgram y V₂
  let V₄ ← walshBlockProgram V₃
  sampleBlockProgram T V₄

@[simp] theorem embeddingProgram_eval {k b : ℕ} (x y : SignAssignment k)
    (T : Finset (WalshIndex k)) (V : Matrix (WalshIndex k) (Fin b) ℝ) :
    (embeddingProgram x y T V).eval = sampledFrame V x y T := by
  simp only [embeddingProgram, eval_bind, signBlockProgram_eval, walshBlockProgram_eval,
    sampleBlockProgram_eval]
  ext i j
  simp only [Matrix.of_apply, sampledFrame, transformedFrame, twoRoundMatrix,
    Matrix.mul_assoc, walshIndex_card, Nat.cast_pow, Nat.cast_ofNat]

theorem embeddingProgram_work {k b : ℕ} (x y : SignAssignment k)
    (T : Finset (WalshIndex k)) (V : Matrix (WalshIndex k) (Fin b) ℝ) :
    (embeddingProgram x y T V).work =
      2*b*(k*2^k+k+1+2^k)+2*2^k*b+k+3+T.card*b := by
  simp only [embeddingProgram, work_bind, signBlockProgram_work, walshBlockProgram_work,
    sampleBlockProgram_work]
  ring

theorem embeddingProgram_admissible {k b : ℕ} (x y : SignAssignment k)
    (T : Finset (WalshIndex k)) (hT : 0<T.card) (V : Matrix (WalshIndex k) (Fin b) ℝ) :
    (embeddingProgram x y T V).admissible := by
  simp only [embeddingProgram, admissible_bind, signBlockProgram_admissible,
    walshBlockProgram_admissible, sampleBlockProgram_admissible T hT, and_self]

end
end HierarchicalAbsoluteSpectral
