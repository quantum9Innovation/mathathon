import HierarchicalAbsoluteSpectral.ExactGramCharpolyRankProfileProgram

/-! The rank-profile program executes no square-root instructions. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

def ArithmeticOp.rankProfileFieldOnly : ArithmeticOp → Prop
  | .sqrt _ => False
  | _ => True

def ArithmeticProgram.rankProfileFieldOnly {α : Type} : ArithmeticProgram α → Prop
  | .pure _ => True
  | .step op next => op.rankProfileFieldOnly ∧ (next op.eval).rankProfileFieldOnly
  | .compare x y next => (next (decide (x ≤ y))).rankProfileFieldOnly
  | .certifiedStep op next => op.rankProfileFieldOnly ∧
      (next ⟨op.eval, rfl⟩).rankProfileFieldOnly
  | .branch x y yes no => if h : x ≤ y then (yes h).rankProfileFieldOnly else (no h).rankProfileFieldOnly

namespace ArithmeticProgram

@[simp] theorem rankProfileFieldOnly_pure {α : Type} (a : α) :
    (ArithmeticProgram.pure a).rankProfileFieldOnly := trivial

@[simp] theorem rankProfileFieldOnly_bind {α β : Type}
    (p : ArithmeticProgram α) (f : α → ArithmeticProgram β) :
    (p >>= f).rankProfileFieldOnly ↔ p.rankProfileFieldOnly ∧ (f p.eval).rankProfileFieldOnly := by
  induction p with
  | pure a => simp [rankProfileFieldOnly, eval, Bind.bind, bind]
  | step op next ih =>
    change (op.rankProfileFieldOnly ∧ (next op.eval >>= f).rankProfileFieldOnly) ↔
      (op.rankProfileFieldOnly ∧ (next op.eval).rankProfileFieldOnly) ∧
        (f (next op.eval).eval).rankProfileFieldOnly
    rw [ih]
    exact and_assoc.symm
  | compare x y next ih => exact ih (decide (x ≤ y))
  | certifiedStep op next ih =>
    change (op.rankProfileFieldOnly ∧ (next ⟨op.eval, rfl⟩ >>= f).rankProfileFieldOnly) ↔
      (op.rankProfileFieldOnly ∧ (next ⟨op.eval, rfl⟩).rankProfileFieldOnly) ∧
        (f (next ⟨op.eval, rfl⟩).eval).rankProfileFieldOnly
    rw [ih]
    exact and_assoc.symm
  | branch x y yes no ihyes ihno =>
    by_cases h : x ≤ y
    · simpa only [Bind.bind, bind, rankProfileFieldOnly, eval, dif_pos h] using ihyes h
    · simpa only [Bind.bind, bind, rankProfileFieldOnly, eval, dif_neg h] using ihno h

@[simp] theorem rankProfileFieldOnly_add (x y : ℝ) : (add x y).rankProfileFieldOnly := by trivial
@[simp] theorem rankProfileFieldOnly_sub (x y : ℝ) : (sub x y).rankProfileFieldOnly := by trivial
@[simp] theorem rankProfileFieldOnly_mul (x y : ℝ) : (mul x y).rankProfileFieldOnly := by trivial
@[simp] theorem rankProfileFieldOnly_div (x y : ℝ) : (div x y).rankProfileFieldOnly := by trivial

@[simp] theorem rankProfileFieldOnly_tabulate {α : Type} (n : ℕ)
    (f : Fin n → ArithmeticProgram α) :
    (tabulate n f).rankProfileFieldOnly ↔ ∀ i, (f i).rankProfileFieldOnly := by
  induction n with
  | zero => simp [tabulate]
  | succ n ih =>
    simp only [tabulate, rankProfileFieldOnly_bind, rankProfileFieldOnly_pure, and_true,
      ih, Fin.forall_fin_succ]

@[simp] theorem rankProfileFieldOnly_certify {α : Type} (p : ArithmeticProgram α) :
    (certify p).rankProfileFieldOnly ↔ p.rankProfileFieldOnly := by
  induction p with
  | pure a => rfl
  | step op next ih => simp only [certify, rankProfileFieldOnly, rankProfileFieldOnly_bind,
      rankProfileFieldOnly_pure, and_true, ih]
  | compare x y next ih =>
    by_cases h : x ≤ y <;> simp [certify, rankProfileFieldOnly, h, ih]
  | certifiedStep op next ih => simp only [certify, rankProfileFieldOnly,
      rankProfileFieldOnly_bind, rankProfileFieldOnly_pure, and_true, ih]
  | branch x y yes no ihyes ihno =>
    by_cases h : x ≤ y <;> simp [certify, rankProfileFieldOnly, h, ihyes, ihno]

end ArithmeticProgram

@[simp] theorem finiteTabulateProgram_rankProfileFieldOnly {I α : Type} [Fintype I]
    (f : I → ArithmeticProgram α) :
    (finiteTabulateProgram f).rankProfileFieldOnly ↔ ∀ i, (f i).rankProfileFieldOnly := by
  simp only [finiteTabulateProgram, rankProfileFieldOnly_bind, rankProfileFieldOnly_pure,
    and_true, rankProfileFieldOnly_tabulate]
  constructor
  · intro h i
    simpa using h ((Fintype.equivFin I) i)
  · intro h i
    exact h _

theorem circuitProgram_rankProfileFieldOnly {I O : Type} (c : Matmul.UniversalProgram.Circuit I O) :
    ∀ input, (circuitProgram c input).rankProfileFieldOnly := by
  induction c with
  | wire select => intro input; trivial
  | zero => intro input; trivial
  | add => intro input; simp [circuitProgram]
  | neg => intro input; simp [circuitProgram]
  | mul => intro input; simp [circuitProgram]
  | comp first second ihfirst ihsecond => intro input; simp [circuitProgram, ihfirst, ihsecond]
  | pair left right ihleft ihright => intro input; simp [circuitProgram, ihleft, ihright]
  | bundle branches ih => intro input; simp [circuitProgram, ih]

theorem ArithmeticKernel.program_rankProfileFieldOnly {a b c : ℕ}
    (K : ArithmeticKernel a b c) (A : Matrix (Fin a) (Fin b) ℝ)
    (B : Matrix (Fin b) (Fin c) ℝ) : (K.program A B).rankProfileFieldOnly := by
  simp only [ArithmeticKernel.program, matrixCircuitProgram, rankProfileFieldOnly_bind,
    circuitProgram_rankProfileFieldOnly, rankProfileFieldOnly_pure, and_self]

@[simp] theorem rankProfileMulProgram_fieldOnly
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin c) ℝ) :
    (rankProfileMulProgram kernels A B).rankProfileFieldOnly := by
  unfold rankProfileMulProgram
  split_ifs <;> simp only [rankProfileFieldOnly_pure, ArithmeticKernel.program_rankProfileFieldOnly]

@[simp] theorem blockScaleProgram_rankProfileFieldOnly {a b : ℕ}
    (x : ℝ) (A : Matrix (Fin a) (Fin b) ℝ) : (blockScaleProgram x A).rankProfileFieldOnly := by
  simp only [blockScaleProgram, rankProfileFieldOnly_bind, rankProfileFieldOnly_tabulate,
    rankProfileFieldOnly_mul, rankProfileFieldOnly_pure, and_self, implies_true]

@[simp] theorem blockSubProgram_rankProfileFieldOnly {a b : ℕ}
    (A B : Matrix (Fin a) (Fin b) ℝ) : (blockSubProgram A B).rankProfileFieldOnly := by
  simp only [blockSubProgram, rankProfileFieldOnly_bind, rankProfileFieldOnly_tabulate,
    rankProfileFieldOnly_sub, rankProfileFieldOnly_pure, and_self, implies_true]

theorem fieldPrincipalSingleProgram_fieldOnly (D : Core 1) (hD : D.PosSemidef) :
    (fieldPrincipalSingleProgram D hD).rankProfileFieldOnly := by
  by_cases hz : D 0 0 ≤ 0
  · simp only [fieldPrincipalSingleProgram, rankProfileFieldOnly, dif_pos hz]
  · simp only [fieldPrincipalSingleProgram, rankProfileFieldOnly, dif_neg hz,
      rankProfileFieldOnly_bind, rankProfileFieldOnly_certify,
      rankProfileFieldOnly_div, rankProfileFieldOnly_pure, and_self]

theorem fieldPrincipalAssembleProgram_fieldOnly (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {l r : ℕ} {A : Core l} {S : Core r} (p : FieldOrderedPSDPrincipalData A)
    (B : Matrix (Fin l) (Fin r) ℝ) (C : Core r)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef)
    (q : FieldOrderedPSDPrincipalData S) (hS : S = p.schur B C)
    (H : Matrix (Fin p.dimension) (Fin r) ℝ) (hH : H = p.inverse * B.submatrix p.selected id) :
    (fieldPrincipalAssembleProgram kernels p B C hD q hS H hH).rankProfileFieldOnly := by
  simp only [fieldPrincipalAssembleProgram, rankProfileFieldOnly_bind, rankProfileFieldOnly_certify,
    blockScaleProgram_rankProfileFieldOnly, rankProfileMulProgram_fieldOnly,
    rankProfileFieldOnly_pure, and_self]

theorem fieldPrincipalProgram_fieldOnly (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (w : ℕ) (D : Core w) (hD : D.PosSemidef) :
    (fieldPrincipalProgram kernels w D hD).rankProfileFieldOnly := by
  induction w using Nat.strong_induction_on with
  | h w ih =>
    rcases w with _ | _ | w
    · rw [fieldPrincipalProgram]; trivial
    · rw [fieldPrincipalProgram]; exact fieldPrincipalSingleProgram_fieldOnly D hD
    · have hl : (w+2)/2 < w+2 := by omega
      have hr : w+2-(w+2)/2 < w+2 := by omega
      have ihl := ih _ hl
      have ihr := ih _ hr
      rw [fieldPrincipalProgram]
      simp only [rankProfileFieldOnly_bind, rankProfileFieldOnly_certify,
        rankProfileMulProgram_fieldOnly, blockSubProgram_rankProfileFieldOnly,
        fieldPrincipalAssembleProgram_fieldOnly, rankProfileFieldOnly_pure, ihl, ihr, and_self]

theorem fieldColumnRankProfileProgram_fieldOnly
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n w : ℕ} (V : Matrix (Fin n) (Fin w) ℝ) :
    (fieldColumnRankProfileProgram kernels V).rankProfileFieldOnly := by
  simp only [fieldColumnRankProfileProgram, rankProfileFieldOnly_bind, rankProfileFieldOnly_certify,
    rankProfileMulProgram_fieldOnly, fieldPrincipalProgram_fieldOnly,
    rankProfileFieldOnly_pure, and_self]

end
end HierarchicalAbsoluteSpectral
