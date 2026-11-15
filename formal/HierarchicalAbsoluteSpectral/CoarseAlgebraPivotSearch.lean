import HierarchicalAbsoluteSpectral.ArithmeticProgram
import HierarchicalAbsoluteSpectral.CoarseAlgebraInertia

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open ArithmeticProgram hiding pure
open Matrix

inductive NonzeroSearchResult {ι : Type} (f : ι → ℝ) where
  | found (i : ι) (nonzero : f i ≠ 0)
  | zero (all_zero : ∀ i, f i = 0)

def nonzeroSearchProgram : (n : ℕ) → (f : Fin n → ℝ) → ArithmeticProgram (NonzeroSearchResult f)
  | 0, _ => ArithmeticProgram.pure (.zero (fun i => i.elim0))
  | n+1, f =>
    .branch (f 0) 0
      (fun hle => .branch 0 (f 0)
        (fun hge => do
          let tail ← nonzeroSearchProgram n (fun i => f i.succ)
          ArithmeticProgram.pure (match tail with
            | .found i hi => .found i.succ hi
            | .zero hz => .zero (Fin.cases (le_antisymm hle hge) hz)))
        (fun hneg => ArithmeticProgram.pure (.found 0 (lt_of_not_ge hneg).ne)))
      (fun hpos => ArithmeticProgram.pure (.found 0 (lt_of_not_ge hpos).ne'))

theorem nonzeroSearchProgram_work (n : ℕ) (f : Fin n → ℝ) :
    (nonzeroSearchProgram n f).work ≤ 2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht := ih (fun i => f i.succ)
    by_cases hl : f 0 ≤ 0
    · by_cases hg : 0 ≤ f 0
      · simp only [nonzeroSearchProgram, work, dif_pos hl, dif_pos hg, work_bind, work_pure, add_zero]
        omega
      · simp only [nonzeroSearchProgram, work, dif_pos hl, dif_neg hg]
        omega
    · simp only [nonzeroSearchProgram, work, dif_neg hl]
      omega

theorem nonzeroSearchProgram_admissible (n : ℕ) (f : Fin n → ℝ) :
    (nonzeroSearchProgram n f).admissible := by
  induction n with
  | zero => trivial
  | succ n ih =>
    by_cases hl : f 0 ≤ 0
    · by_cases hg : 0 ≤ f 0
      · simp only [nonzeroSearchProgram, admissible, dif_pos hl, dif_pos hg, admissible_bind, ih,
          admissible_pure, and_self]
      · simp only [nonzeroSearchProgram, admissible, dif_pos hl, dif_neg hg]
    · simp only [nonzeroSearchProgram, admissible, dif_neg hl]

def finiteNonzeroSearchProgram {ι : Type} [Fintype ι] (f : ι → ℝ) :
    ArithmeticProgram (NonzeroSearchResult f) := do
  let result ← nonzeroSearchProgram (Fintype.card ι) (fun i => f ((Fintype.equivFin ι).symm i))
  ArithmeticProgram.pure (match result with
    | .found i hi => .found ((Fintype.equivFin ι).symm i) hi
    | .zero hz => .zero (fun i => by simpa using hz ((Fintype.equivFin ι) i)))

theorem finiteNonzeroSearchProgram_work {ι : Type} [Fintype ι] (f : ι → ℝ) :
    (finiteNonzeroSearchProgram f).work ≤ 2*Fintype.card ι := by
  simp only [finiteNonzeroSearchProgram, work_bind, work_pure, add_zero]
  exact nonzeroSearchProgram_work _ _

theorem finiteNonzeroSearchProgram_admissible {ι : Type} [Fintype ι] (f : ι → ℝ) :
    (finiteNonzeroSearchProgram f).admissible := by
  simp only [finiteNonzeroSearchProgram, admissible_bind, admissible_pure, and_true]
  exact nonzeroSearchProgram_admissible _ _

inductive SymmetricPivotChoice {n : ℕ} (D : Core n) where
  | zero (all_zero : D = 0)
  | diagonal (i : Fin n) (nonzero : D i i ≠ 0)
  | offDiagonal (i j : Fin n) (different : i ≠ j)
      (zero_i : D i i = 0) (zero_j : D j j = 0) (nonzero : D i j ≠ 0)

def symmetricPivotChoiceProgram {n : ℕ} (D : Core n) : ArithmeticProgram (SymmetricPivotChoice D) := do
  let diagonal ← finiteNonzeroSearchProgram (fun i => D i i)
  match diagonal with
  | .found i hi => ArithmeticProgram.pure (.diagonal i hi)
  | .zero hz => do
    let entry ← finiteNonzeroSearchProgram (fun i : Fin n × Fin n => D i.1 i.2)
    ArithmeticProgram.pure (match entry with
      | .found ij hij => .offDiagonal ij.1 ij.2
          (by intro he; exact hij (by rw [he]; exact hz _)) (hz _) (hz _) hij
      | .zero hall => .zero (by ext i j; exact hall (i,j)))

theorem symmetricPivotChoiceProgram_admissible {n : ℕ} (D : Core n) :
    (symmetricPivotChoiceProgram D).admissible := by
  simp only [symmetricPivotChoiceProgram, admissible_bind, finiteNonzeroSearchProgram_admissible, true_and]
  cases (finiteNonzeroSearchProgram (fun i => D i i)).eval with
  | found i hi => trivial
  | zero h => simp only [admissible_bind, finiteNonzeroSearchProgram_admissible, admissible_pure, and_self]

theorem symmetricPivotChoiceProgram_work {n : ℕ} (D : Core n) :
    (symmetricPivotChoiceProgram D).work ≤ 2*n+2*n*n := by
  have hd := finiteNonzeroSearchProgram_work (fun i => D i i)
  have he := finiteNonzeroSearchProgram_work (fun i : Fin n × Fin n => D i.1 i.2)
  simp only [Fintype.card_fin, Fintype.card_prod] at hd he
  simp only [symmetricPivotChoiceProgram, work_bind]
  cases (finiteNonzeroSearchProgram (fun i => D i i)).eval with
  | found i hi => simp only [work_pure]; omega
  | zero h => simp only [work_bind, work_pure]; nlinarith

end
end HierarchicalAbsoluteSpectral
