import HierarchicalAbsoluteSpectral.InertiaSignCountProgram
import HierarchicalAbsoluteSpectral.ExactGramCharpolyRankProfileFieldOnly

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

theorem positiveDiagonalCountProgram_fieldOnly {n : ℕ} (d : Fin n → ℝ) :
    (positiveDiagonalCountProgram d).rankProfileFieldOnly := by
  induction n with
  | zero => trivial
  | succ n ih =>
    simp only [positiveDiagonalCountProgram,rankProfileFieldOnly_bind,ih,true_and,
      ArithmeticProgram.rankProfileFieldOnly]
    split_ifs <;> trivial

theorem negativeDiagonalCountProgram_fieldOnly {n : ℕ} (d : Fin n → ℝ) :
    (negativeDiagonalCountProgram d).rankProfileFieldOnly := by
  induction n with
  | zero => trivial
  | succ n ih =>
    simp only [negativeDiagonalCountProgram,rankProfileFieldOnly_bind,ih,true_and,
      ArithmeticProgram.rankProfileFieldOnly]
    split_ifs <;> trivial

end
end HierarchicalAbsoluteSpectral
