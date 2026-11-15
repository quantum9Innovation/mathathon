import HierarchicalAbsoluteSpectral.ThresholdRitz
import HierarchicalAbsoluteSpectral.ArithmeticProgram

/-! The actual finite block-Krylov span and its counted action program.
Every degree-at-most-q polynomial graph is proved to lie in this span. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open ArithmeticProgram hiding pure
variable {k r h : ℕ}

def blockKrylov (T : Core k) (Ω : Matrix (Fin k) (Fin r) ℝ) (q : ℕ) :
    Matrix (Fin k) (Fin (q+1) × Fin r) ℝ :=
  fun i sb => (T^sb.1.val*Ω) i sb.2

def blockKrylovCoefficients (p : ℝ[X]) (q : ℕ) (W : Matrix (Fin r) (Fin h) ℝ) :
    Matrix (Fin (q+1) × Fin r) (Fin h) ℝ :=
  fun sb c => p.coeff sb.1.val*W sb.2 c

theorem blockKrylov_polynomial_identity (T : Core k) (Ω : Matrix (Fin k) (Fin r) ℝ)
    (p : ℝ[X]) (q : ℕ) (hq : p.natDegree ≤ q) (W : Matrix (Fin r) (Fin h) ℝ) :
    blockKrylov T Ω q*blockKrylovCoefficients p q W = (aeval T p*Ω)*W := by
  rw [Polynomial.aeval_eq_sum_range' (show p.natDegree < q+1 by omega)]
  simp only [Matrix.sum_mul, Matrix.smul_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  ext i c
  simp only [Matrix.mul_apply, blockKrylov, blockKrylovCoefficients,
    Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

def krylovBlocksProgram
    (action : Matrix (Fin k) (Fin r) ℝ → ArithmeticProgram (Matrix (Fin k) (Fin r) ℝ)) :
    (q : ℕ) → Matrix (Fin k) (Fin r) ℝ → ArithmeticProgram (Fin (q+1) → Matrix (Fin k) (Fin r) ℝ)
  | 0, Ω => .pure (fun _ => Ω)
  | q+1, Ω => do
      let next ← action Ω
      let tail ← krylovBlocksProgram action q next
      .pure (Fin.cons Ω tail)

theorem krylovBlocksProgram_eval
    (T : Core k)
    (action : Matrix (Fin k) (Fin r) ℝ → ArithmeticProgram (Matrix (Fin k) (Fin r) ℝ))
    (haction : ∀ Ω, (action Ω).eval = T*Ω) (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    (krylovBlocksProgram action q Ω).eval = fun s => T^s.val*Ω := by
  induction q generalizing Ω with
  | zero =>
    funext s
    have hs : s.val = 0 := by omega
    simp [krylovBlocksProgram, hs]
  | succ q ih =>
    simp only [krylovBlocksProgram, eval_bind, haction, ih, eval_pure]
    funext s
    refine Fin.cases ?_ (fun i => ?_) s
    · simp
    · simp [pow_succ, Matrix.mul_assoc]

theorem krylovBlocksProgram_work_le
    (action : Matrix (Fin k) (Fin r) ℝ → ArithmeticProgram (Matrix (Fin k) (Fin r) ℝ))
    (cost : ℕ) (haction : ∀ Ω, (action Ω).work ≤ cost)
    (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    (krylovBlocksProgram action q Ω).work ≤ q*cost := by
  induction q generalizing Ω with
  | zero => simp [krylovBlocksProgram]
  | succ q ih =>
    simp only [krylovBlocksProgram, work_bind, work_pure, add_zero]
    have h₁ := haction Ω
    have h₂ := ih (action Ω).eval
    rw [Nat.succ_mul]
    omega

theorem krylovBlocksProgram_admissible
    (action : Matrix (Fin k) (Fin r) ℝ → ArithmeticProgram (Matrix (Fin k) (Fin r) ℝ))
    (haction : ∀ Ω, (action Ω).admissible)
    (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    (krylovBlocksProgram action q Ω).admissible := by
  induction q generalizing Ω with
  | zero => trivial
  | succ q ih =>
    simp only [krylovBlocksProgram, admissible_bind, admissible_pure, and_true]
    exact ⟨haction Ω, ih _⟩

end
end HierarchicalAbsoluteSpectral
