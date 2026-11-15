import HierarchicalAbsoluteSpectral.BlockPrograms
import HierarchicalAbsoluteSpectral.NeumannMass

/-!
Matrix-free application of the finite Neumann mass. This is a compiler
from an actual Gram-action program; correctness, admissibility and its
real-operation bound are carried through from that supplied program.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure
variable {k b : ℕ}

def neumannActionProgram (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)) :
    ℕ → Matrix (Fin k) (Fin b) ℝ → ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)
  | 0, V => .pure V
  | l+1, V => do
      let X ← neumannActionProgram action l V
      let GX ← action X
      let D ← blockSubProgram X GX
      blockAddProgram V D

theorem neumann_sum_action_step (G : Core k) (V : Matrix (Fin k) (Fin b) ℝ) (l : ℕ) :
    (∑ i ∈ Finset.range (l+2), (1-G)^i)*V =
      V+(∑ i ∈ Finset.range (l+1), (1-G)^i)*V-
        G*((∑ i ∈ Finset.range (l+1), (1-G)^i)*V) := by
  rw [show l+2 = (l+1)+1 by omega, geom_sum_succ]
  simp only [Matrix.add_mul, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
  module

theorem neumannActionProgram_eval (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)) (G : Core k)
    (hact : ∀ X, (action X).eval = G*X) (l : ℕ) (V : Matrix (Fin k) (Fin b) ℝ) :
    (neumannActionProgram action l V).eval = (∑ i ∈ Finset.range (l+1), (1-G)^i)*V := by
  induction l with
  | zero => simp [neumannActionProgram]
  | succ l ih =>
    simp only [neumannActionProgram, eval_bind, hact, blockSubProgram_eval, blockAddProgram_eval, ih]
    simpa only [add_sub_assoc, Nat.add_assoc] using (neumann_sum_action_step G V l).symm

theorem neumannActionProgram_work (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)) (T : ℕ)
    (hwork : ∀ X, (action X).work ≤ T) (l : ℕ) (V : Matrix (Fin k) (Fin b) ℝ) :
    (neumannActionProgram action l V).work ≤ l*(T+2*k*b) := by
  induction l with
  | zero => simp [neumannActionProgram]
  | succ l ih =>
    simp only [neumannActionProgram, work_bind, blockSubProgram_work, blockAddProgram_work]
    have h := hwork (neumannActionProgram action l V).eval
    nlinarith

theorem neumannActionProgram_admissible (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ))
    (hvalid : ∀ X, (action X).admissible) (l : ℕ) (V : Matrix (Fin k) (Fin b) ℝ) :
    (neumannActionProgram action l V).admissible := by
  induction l with
  | zero => trivial
  | succ l ih => simp [neumannActionProgram, ih, hvalid]

theorem evenNeumannAction_specification (action : Matrix (Fin k) (Fin b) ℝ →
    ArithmeticProgram (Matrix (Fin k) (Fin b) ℝ)) (G : Core k) (T q : ℕ)
    (hact : ∀ X, (action X).eval = G*X) (hwork : ∀ X, (action X).work ≤ T)
    (hvalid : ∀ X, (action X).admissible) (V : Matrix (Fin k) (Fin b) ℝ) :
    (neumannActionProgram action (2*q) V).admissible ∧
      (neumannActionProgram action (2*q) V).eval = evenNeumannMass G q*V ∧
      (neumannActionProgram action (2*q) V).work ≤ (2*q)*(T+2*k*b) := by
  refine ⟨neumannActionProgram_admissible action hvalid _ V, ?_,
    neumannActionProgram_work action T hwork _ V⟩
  rw [neumannActionProgram_eval action G hact, evenNeumannMass_eq_sum]

end
end HierarchicalAbsoluteSpectral
