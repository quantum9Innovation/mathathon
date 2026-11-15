import HierarchicalAbsoluteSpectral.ArithmeticProgram
import HierarchicalAbsoluteSpectral.RadixTwoDFT

/-!
A materialized radix-two Fourier transform in the exact-arithmetic program
model. Recursive transform tuples and twiddle factors are each evaluated
once and reused. In particular, no exponentiation is hidden in a butterfly.
The count includes the real additions and products implementing complex
arithmetic, the twiddle table, and the squared root for each recursive call.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

def powerTableProgram : (n : ℕ) → ℂ → ℂ → ArithmeticProgram (Fin n → ℂ)
  | 0, _, _ => ArithmeticProgram.pure Fin.elim0
  | n+1, w, z => do
      let next ← complexMul z w
      let rest ← powerTableProgram n w next
      ArithmeticProgram.pure (Fin.cons z rest)

@[simp] theorem powerTableProgram_eval (n : ℕ) (w z : ℂ) (i : Fin n) :
    (powerTableProgram n w z).eval i = z*w^i.val := by
  induction n generalizing z with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [powerTableProgram, eval_bind, eval_complexMul, eval_pure]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.cons_succ, ih, Fin.val_succ, pow_succ]
      ring

@[simp] theorem powerTableProgram_work (n : ℕ) (w z : ℂ) :
    (powerTableProgram n w z).work = 6*n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [powerTableProgram, work_bind, eval_complexMul, work_complexMul, work_pure,
      ih, add_zero]
    omega

@[simp] theorem powerTableProgram_admissible (n : ℕ) (w z : ℂ) :
    (powerTableProgram n w z).admissible := by
  induction n generalizing z with
  | zero => trivial
  | succ n ih => simp [powerTableProgram, ih]

def butterflyProgram (a b t : ℂ) : ArithmeticProgram (ℂ × ℂ) := do
  let c ← complexMul t b
  let u ← complexAdd a c
  let v ← complexSub a c
  ArithmeticProgram.pure (u,v)

@[simp] theorem butterflyProgram_eval (a b t : ℂ) :
    (butterflyProgram a b t).eval = (a+t*b,a-t*b) := by simp [butterflyProgram]

@[simp] theorem butterflyProgram_work (a b t : ℂ) :
    (butterflyProgram a b t).work = 10 := by simp [butterflyProgram]

@[simp] theorem butterflyProgram_admissible (a b t : ℂ) :
    (butterflyProgram a b t).admissible := by simp [butterflyProgram]

def butterflyTableProgram (n : ℕ) (a b t : Fin n → ℂ) :
    ArithmeticProgram (Fin n → ℂ × ℂ) :=
  tabulate n (fun i => butterflyProgram (a i) (b i) (t i))

@[simp] theorem butterflyTableProgram_eval (n : ℕ) (a b t : Fin n → ℂ) (i : Fin n) :
    (butterflyTableProgram n a b t).eval i = (a i+t i*b i,a i-t i*b i) := by
  simp only [butterflyTableProgram, eval_tabulate, butterflyProgram_eval]

@[simp] theorem butterflyTableProgram_work (n : ℕ) (a b t : Fin n → ℂ) :
    (butterflyTableProgram n a b t).work = 10*n := by
  simp [butterflyTableProgram, Nat.mul_comm]

@[simp] theorem butterflyTableProgram_admissible (n : ℕ) (a b t : Fin n → ℂ) :
    (butterflyTableProgram n a b t).admissible := by simp [butterflyTableProgram]

def joinButterflyTable (s : ℕ) (b : Fin (2^s) → ℂ × ℂ) (i : Fin (2^(s+1))) : ℂ :=
  if hi : i.val < 2^s then (b ⟨i.val, hi⟩).1
  else (b ⟨i.val-2^s, by
    have h : i.val < 2^s*2 := by simpa only [pow_succ] using i.isLt
    omega⟩).2

def fftProgram : (s : ℕ) → ℂ → (ℕ → ℂ) → ArithmeticProgram (Fin (2^s) → ℂ)
  | 0, _, v => ArithmeticProgram.pure (fun _ => v 0)
  | s+1, w, v => do
      let w2 ← complexMul w w
      let a ← fftProgram s w2 (fun j => v (2*j))
      let b ← fftProgram s w2 (fun j => v (2*j+1))
      let t ← powerTableProgram (2^s) w 1
      let c ← butterflyTableProgram (2^s) a b t
      ArithmeticProgram.pure (joinButterflyTable s c)

theorem fftProgram_eval_radixTwo (s : ℕ) (w : ℂ) (v : ℕ → ℂ) (i : Fin (2^s)) :
    (fftProgram s w v).eval i = radixTwoDFT s w v i.val := by
  induction s generalizing w v with
  | zero => rfl
  | succ s ih =>
    simp only [fftProgram, eval_bind, eval_complexMul, eval_pure]
    unfold joinButterflyTable
    rw [radixTwoDFT]
    split_ifs with hi
    · rw [butterflyTableProgram_eval, powerTableProgram_eval, one_mul, ih, ih]
      simp only [pow_two]
    · rw [butterflyTableProgram_eval, powerTableProgram_eval, one_mul, ih, ih]
      simp only [pow_two]

def fftWork : ℕ → ℕ
  | 0 => 0
  | s+1 => 2*fftWork s + 16*2^s+6

theorem fftProgram_work (s : ℕ) (w : ℂ) (v : ℕ → ℂ) :
    (fftProgram s w v).work = fftWork s := by
  induction s generalizing w v with
  | zero => rfl
  | succ s ih =>
    simp only [fftProgram, work_bind, work_complexMul, eval_complexMul,
      powerTableProgram_work, butterflyTableProgram_work, work_pure, ih, add_zero, fftWork]
    ring

theorem fftWork_exact (s : ℕ) : fftWork s + 6 = (8*s+6)*2^s := by
  induction s with
  | zero => norm_num [fftWork]
  | succ s ih =>
    rw [fftWork, pow_succ]
    nlinarith

theorem fftProgram_work_bound (s : ℕ) (w : ℂ) (v : ℕ → ℂ) :
    (fftProgram s w v).work ≤ 8*(s+1)*2^s := by
  rw [fftProgram_work]
  have h := fftWork_exact s
  nlinarith [show 0 < 2^s by positivity]

theorem fftProgram_admissible (s : ℕ) (w : ℂ) (v : ℕ → ℂ) :
    (fftProgram s w v).admissible := by
  induction s generalizing w v with
  | zero => trivial
  | succ s ih => simp [fftProgram, ih]

/-- Correctness and operation count for the same operational program. -/
theorem fftProgram_specification (s : ℕ) (w : ℂ) (v : ℕ → ℂ) (hw : IsDyadicRoot w s) :
    (fftProgram s w v).admissible ∧
      (∀ i : Fin (2^s), (fftProgram s w v).eval i = finiteDFT (2^s) w v i.val) ∧
      (fftProgram s w v).work ≤ 8*(s+1)*2^s := by
  exact ⟨fftProgram_admissible s w v, fun i => (fftProgram_eval_radixTwo s w v i).trans
    (radixTwoDFT_correct s w v hw i.val i.isLt), fftProgram_work_bound s w v⟩

end
end HierarchicalAbsoluteSpectral
