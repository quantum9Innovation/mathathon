import HierarchicalAbsoluteSpectral.ExactGramCharpolyRankProfile
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Sort

/-!
Stable rank compression preserves every labelled prefix span. This is
the invariant needed to compress a doubled Krylov matrix without ever
forming the full matrix of all powers and all standard basis vectors.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators

def exactGramColumn {n w : ℕ} (V : Matrix (Fin n) (Fin w) ℝ) (j : Fin w) :
    Fin n → ℝ := fun i => V i j

def exactGramPrefixSpan {n w : ℕ} {β : Type*} [Preorder β]
    (V : Matrix (Fin n) (Fin w) ℝ) (label : Fin w → β) (cut : β) :
    Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ {x | ∃ j, label j ≤ cut ∧ x = exactGramColumn V j}

theorem exactGramColumn_mem_prefix {n w : ℕ} {β : Type*} [Preorder β]
    (V : Matrix (Fin n) (Fin w) ℝ) (label : Fin w → β) (cut : β)
    (j : Fin w) (hj : label j ≤ cut) :
    exactGramColumn V j ∈ exactGramPrefixSpan V label cut :=
  Submodule.subset_span ⟨j, hj, rfl⟩

theorem exactGramPrefixSpan_le_of_columns {n w : ℕ} {β : Type*} [Preorder β]
    (V : Matrix (Fin n) (Fin w) ℝ) (label : Fin w → β) (cut : β)
    (P : Submodule ℝ (Fin n → ℝ))
    (h : ∀ j, label j ≤ cut → exactGramColumn V j ∈ P) :
    exactGramPrefixSpan V label cut ≤ P := by
  apply Submodule.span_le.mpr
  rintro x ⟨j, hj, rfl⟩
  exact h j hj

theorem exactGramPrefixSpan_weighted {n w : ℕ} {β : Type*} [LinearOrder β]
    (V : Matrix (Fin n) (Fin w) ℝ) (label : Fin w → β) (cut : β)
    (c : Fin w → ℝ) (hc : ∀ j, cut < label j → c j = 0) :
    V *ᵥ c ∈ exactGramPrefixSpan V label cut := by
  have heq : V *ᵥ c = ∑ j, c j • exactGramColumn V j := by
    ext i
    simp [Matrix.mulVec, dotProduct, exactGramColumn, mul_comm]
  rw [heq]
  apply Submodule.sum_mem
  intro j hj
  by_cases hcut : label j ≤ cut
  · exact Submodule.smul_mem _ _ (exactGramColumn_mem_prefix V label cut j hcut)
  · rw [hc j (lt_of_not_ge hcut), zero_smul]
    exact Submodule.zero_mem _

/-- Exact equality of all labelled prefix spans after stable compression. -/
theorem exactGramPrefixSpan_rankProfile {n w : ℕ} {β : Type*} [LinearOrder β]
    (V : Matrix (Fin n) (Fin w) ℝ) (label : Fin w → β) (hlabel : StrictMono label)
    (p : FieldColumnRankProfile V) (cut : β) :
    exactGramPrefixSpan p.basis (fun i => label (p.selected i)) cut =
      exactGramPrefixSpan V label cut := by
  apply le_antisymm
  · apply exactGramPrefixSpan_le_of_columns
    intro i hi
    exact exactGramColumn_mem_prefix V label cut (p.selected i) hi
  · apply exactGramPrefixSpan_le_of_columns
    intro j hj
    have heq : exactGramColumn V j = p.basis *ᵥ (fun i => p.coefficients i j) := by
      ext i
      exact (congrArg (fun M => M i j) p.spans).symm
    rw [heq]
    apply exactGramPrefixSpan_weighted
    intro i hi
    exact p.prefix_zero i j (hlabel.lt_iff_lt.mp (lt_of_le_of_lt hj hi))

theorem exactGramRankProfile_dimension {n w : ℕ}
    (V : Matrix (Fin n) (Fin w) ℝ) (p : FieldColumnRankProfile V)
    (old : Fin n → Fin w) (U : Core n)
    (hU : U * V.submatrix id old = 1) : p.dimension = n := by
  have hB : n ≤ (V.submatrix id old).rank := by
    calc
      n = (1 : Core n).rank := by simp [Matrix.rank_one]
      _ = (U * V.submatrix id old).rank := congrArg Matrix.rank hU.symm
      _ ≤ (V.submatrix id old).rank := Matrix.rank_mul_le_right _ _
  apply le_antisymm p.dimension_le_rows
  rw [p.dimension_eq_rank]
  exact hB.trans (Matrix.rank_submatrix_le V id old)

end
end HierarchicalAbsoluteSpectral
