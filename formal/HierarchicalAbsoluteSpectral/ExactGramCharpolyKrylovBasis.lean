import HierarchicalAbsoluteSpectral.ExactGramCharpolyCompression

/-!
A compressed Krylov basis with a labelled prefix-span invariant. Each
doubling retains at most n columns. The invariant refers to all truncated
Krylov columns only in proofs, so those n*d columns are never materialized.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators

abbrev ExactGramKrylovLabel (n : ℕ) := Fin n ×ₗ ℕ

def exactGramShiftLabel {n : ℕ} (d : ℕ) :
    ExactGramKrylovLabel n ↪o ExactGramKrylovLabel n where
  toFun x := toLex ((ofLex x).1, (ofLex x).2+d)
  inj' := by
    intro x y h
    apply ofLex.injective
    apply Prod.ext
    · exact congrArg (fun z => (ofLex z).1) h
    · have hh := congrArg (fun z => (ofLex z).2) h
      exact Nat.add_right_cancel hh
  map_rel_iff' := by
    intro x y
    change toLex ((ofLex x).1, (ofLex x).2+d) ≤
      toLex ((ofLex y).1, (ofLex y).2+d) ↔ x ≤ y
    simp only [Prod.Lex.le_iff, ofLex_toLex, Nat.add_le_add_iff_right]

@[simp] theorem exactGramShiftLabel_apply {n : ℕ} (d : ℕ) (x : ExactGramKrylovLabel n) :
    exactGramShiftLabel d x = toLex ((ofLex x).1, (ofLex x).2+d) := rfl

def exactGramExpandedLabel {n w : ℕ} (label : Fin w → ExactGramKrylovLabel n)
    (d : ℕ) : Fin w ⊕ Fin w → ExactGramKrylovLabel n :=
  Sum.elim label (fun i => exactGramShiftLabel d (label i))

theorem exactGramExpandedLabel_injective {n w : ℕ}
    (label : Fin w ↪o ExactGramKrylovLabel n) (d : ℕ)
    (hbound : ∀ i, (ofLex (label i)).2 < d) :
    Function.Injective (exactGramExpandedLabel label d) := by
  intro x y h
  rcases x with i | i <;> rcases y with j | j
  · exact congrArg Sum.inl (label.injective h)
  · have hh := congrArg (fun z => (ofLex z).2) h
    have hi := hbound i
    change (ofLex (label i)).2 = (ofLex (label j)).2+d at hh
    omega
  · have hh := congrArg (fun z => (ofLex z).2) h
    have hj := hbound j
    change (ofLex (label i)).2+d = (ofLex (label j)).2 at hh
    omega
  · apply congrArg Sum.inr
    apply label.injective
    exact (exactGramShiftLabel d).injective h

structure ExactGramDoubledLayout {n w : ℕ}
    (label : Fin w ↪o ExactGramKrylovLabel n) (d : ℕ) where
  copy : Fin (w+w) ≃ Fin w ⊕ Fin w
  labels : Fin (w+w) ↪o ExactGramKrylovLabel n
  labels_eq : ∀ j, labels j = exactGramExpandedLabel label d (copy j)

/-- Sorting labels is discrete rewiring; it does not inspect field entries. -/
def exactGramDoubledLayout {n w : ℕ}
    (label : Fin w ↪o ExactGramKrylovLabel n) (d : ℕ)
    (hbound : ∀ i, (ofLex (label i)).2 < d) : ExactGramDoubledLayout label d := by
  let f := exactGramExpandedLabel label d
  have hf : Function.Injective f := exactGramExpandedLabel_injective label d hbound
  let order : LinearOrder (Fin w ⊕ Fin w) := LinearOrder.lift' f hf
  letI : LE (Fin w ⊕ Fin w) := order.toLE
  letI : LT (Fin w ⊕ Fin w) := order.toLT
  letI : LinearOrder (Fin w ⊕ Fin w) := order
  let e : Fin (w+w) ≃o Fin w ⊕ Fin w :=
    monoEquivOfFin (Fin w ⊕ Fin w) (k := w+w)
      (by simp only [Fintype.card_sum, Fintype.card_fin])
  let emb : (Fin w ⊕ Fin w) ↪o ExactGramKrylovLabel n := {
    toFun := f
    inj' := hf
    map_rel_iff' := by intro x y; rfl }
  exact ⟨e.toEquiv, e.toOrderEmbedding.comp emb, fun _ => rfl⟩

structure ExactGramKrylovBasis {n : ℕ} (A : Core n) (d : ℕ) where
  width : ℕ
  width_le : width ≤ n
  basis : Matrix (Fin n) (Fin width) ℝ
  inverse : Matrix (Fin width) (Fin n) ℝ
  left_inverse : inverse*basis = 1
  right_inverse : basis*inverse = 1
  power : Core n
  power_eq : power = A^d
  labels : Fin width ↪o ExactGramKrylovLabel n
  exponent_lt : ∀ i, (ofLex (labels i)).2 < d
  column_eq : ∀ i,
    exactGramColumn basis i =
      (A^(ofLex (labels i)).2) *ᵥ Pi.single (ofLex (labels i)).1 1
  complete : ∀ (j : Fin n) (e : ℕ), e < d →
    (A^e) *ᵥ Pi.single j 1 ∈ exactGramPrefixSpan basis labels (toLex (j,e))

def exactGramKrylovBasis_initial {n : ℕ} (A : Core n) : ExactGramKrylovBasis A 1 where
  width := n
  width_le := le_rfl
  basis := 1
  inverse := 1
  left_inverse := by simp
  right_inverse := by simp
  power := A
  power_eq := by simp
  labels := {
    toFun := fun i => toLex (i,0)
    inj' := by intro i j h; exact congrArg (fun z => (ofLex z).1) h
    map_rel_iff' := by
      intro i j
      change toLex (i,0) ≤ toLex (j,0) ↔ i ≤ j
      rw [Prod.Lex.toLex_le_toLex]
      simp only [le_refl, and_true]
      exact le_iff_lt_or_eq.symm }
  exponent_lt := by intro i; simp
  column_eq := by intro i; ext j; simp [exactGramColumn, Matrix.one_apply, Pi.single_apply, eq_comm]
  complete := by
    intro j e he
    have hz : e = 0 := by omega
    subst e
    simp only [pow_zero, Matrix.one_mulVec]
    have hcol : Pi.single j (1:ℝ) = exactGramColumn (1 : Core n) j := by
      ext i
      simp [exactGramColumn, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [hcol]
    exact exactGramColumn_mem_prefix _ _ _ j le_rfl

namespace ExactGramKrylovBasis

variable {n d : ℕ} {A : Core n}

def layout (b : ExactGramKrylovBasis A d) : ExactGramDoubledLayout b.labels d :=
  exactGramDoubledLayout b.labels d b.exponent_lt

def doubled (b : ExactGramKrylovBasis A d) : Matrix (Fin n) (Fin (b.width+b.width)) ℝ :=
  (Matrix.fromCols b.basis (b.power*b.basis)).submatrix id b.layout.copy

theorem doubled_old_column (b : ExactGramKrylovBasis A d) (i : Fin b.width) :
    exactGramColumn b.doubled (b.layout.copy.symm (Sum.inl i)) =
      exactGramColumn b.basis i := by
  ext r
  simp [doubled, exactGramColumn]

theorem doubled_new_column (b : ExactGramKrylovBasis A d) (i : Fin b.width) :
    exactGramColumn b.doubled (b.layout.copy.symm (Sum.inr i)) =
      b.power *ᵥ exactGramColumn b.basis i := by
  ext r
  simp [doubled, exactGramColumn, Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem layout_old_label (b : ExactGramKrylovBasis A d) (i : Fin b.width) :
    b.layout.labels (b.layout.copy.symm (Sum.inl i)) = b.labels i := by
  rw [b.layout.labels_eq]
  simp [exactGramExpandedLabel]

theorem layout_new_label (b : ExactGramKrylovBasis A d) (i : Fin b.width) :
    b.layout.labels (b.layout.copy.symm (Sum.inr i)) = exactGramShiftLabel d (b.labels i) := by
  rw [b.layout.labels_eq]
  simp [exactGramExpandedLabel]

theorem doubled_bound (b : ExactGramKrylovBasis A d) (i : Fin (b.width+b.width)) :
    (ofLex (b.layout.labels i)).2 < d+d := by
  rw [b.layout.labels_eq]
  cases h : b.layout.copy i with
  | inl j => simpa only [exactGramExpandedLabel, Sum.elim_inl] using
      lt_of_lt_of_le (b.exponent_lt j) (Nat.le_add_right d d)
  | inr j =>
      change (ofLex (b.labels j)).2+d < d+d
      exact Nat.add_lt_add_right (b.exponent_lt j) d

theorem doubled_column_eq (b : ExactGramKrylovBasis A d) (i : Fin (b.width+b.width)) :
    exactGramColumn b.doubled i =
      (A^(ofLex (b.layout.labels i)).2) *ᵥ Pi.single (ofLex (b.layout.labels i)).1 1 := by
  have h := b.layout.labels_eq i
  cases hi : b.layout.copy i with
  | inl j =>
      have he : i = b.layout.copy.symm (Sum.inl j) := by rw [← hi]; simp
      rw [he, b.doubled_old_column, b.layout_old_label]
      exact b.column_eq j
  | inr j =>
      have he : i = b.layout.copy.symm (Sum.inr j) := by rw [← hi]; simp
      rw [he, b.doubled_new_column, b.layout_new_label, b.column_eq, b.power_eq,
        Matrix.mulVec_mulVec, ← pow_add]
      simp only [exactGramShiftLabel_apply, ofLex_toLex]
      rw [Nat.add_comm]

theorem old_prefix_le (b : ExactGramKrylovBasis A d) (cut : ExactGramKrylovLabel n) :
    exactGramPrefixSpan b.basis b.labels cut ≤
      exactGramPrefixSpan b.doubled b.layout.labels cut := by
  apply exactGramPrefixSpan_le_of_columns
  intro i hi
  rw [← b.doubled_old_column i]
  apply exactGramColumn_mem_prefix
  simpa only [b.layout_old_label] using hi

theorem shifted_prefix_mem (b : ExactGramKrylovBasis A d) (cut : ExactGramKrylovLabel n)
    (x : Fin n → ℝ) (hx : x ∈ exactGramPrefixSpan b.basis b.labels cut) :
    b.power *ᵥ x ∈ exactGramPrefixSpan b.doubled b.layout.labels (exactGramShiftLabel d cut) := by
  have hle : exactGramPrefixSpan b.basis b.labels cut ≤
      (exactGramPrefixSpan b.doubled b.layout.labels (exactGramShiftLabel d cut)).comap
        b.power.mulVecLin := by
    apply exactGramPrefixSpan_le_of_columns
    intro i hi
    change b.power *ᵥ exactGramColumn b.basis i ∈
      exactGramPrefixSpan b.doubled b.layout.labels (exactGramShiftLabel d cut)
    rw [← b.doubled_new_column i]
    apply exactGramColumn_mem_prefix
    rw [b.layout_new_label]
    exact (exactGramShiftLabel d).monotone hi
  exact hle hx

theorem doubled_complete (b : ExactGramKrylovBasis A d) (j : Fin n) (e : ℕ)
    (he : e < d+d) :
    (A^e) *ᵥ Pi.single j 1 ∈ exactGramPrefixSpan b.doubled b.layout.labels (toLex (j,e)) := by
  by_cases hsmall : e < d
  · exact b.old_prefix_le _ (b.complete j e hsmall)
  · have hde : d ≤ e := Nat.le_of_not_gt hsmall
    have hq : e-d < d := by omega
    have hmem := b.shifted_prefix_mem (toLex (j,e-d)) _ (b.complete j (e-d) hq)
    rw [b.power_eq, Matrix.mulVec_mulVec, ← pow_add] at hmem
    have heq : d+(e-d) = e := Nat.add_sub_of_le hde
    have heq' : e-d+d = e := Nat.sub_add_cancel hde
    simpa only [heq, exactGramShiftLabel_apply, ofLex_toLex, heq'] using hmem

/-- Compress the computed doubled matrix. All field values in the new
state are supplied by the actual multiplication/rank-profile programs. -/
def compress (b : ExactGramKrylovBasis A d)
    (W : Matrix (Fin n) (Fin (b.width+b.width)) ℝ) (hW : W = b.doubled)
    (power : Core n) (hpower : power = b.power*b.power)
    (p : FieldColumnRankProfile W) : ExactGramKrylovBasis A (d+d) where
  width := p.dimension
  width_le := p.dimension_le_rows
  basis := p.basis
  inverse := p.leftInverse
  left_inverse := p.left_inverse
  right_inverse := by
    let old : Fin b.width → Fin (b.width+b.width) := fun i => b.layout.copy.symm (Sum.inl i)
    have hOld : W.submatrix id old = b.basis := by
      rw [hW]
      ext i j
      exact congrFun (b.doubled_old_column j) i
    have hh := congrArg (fun M => M.submatrix id old) p.spans
    have hB : p.basis*p.leftInverse*b.basis = b.basis := by
      simpa only [rankProfile_submatrix_mul, Matrix.submatrix_id_id, hOld,
        Matrix.mul_assoc, FieldColumnRankProfile.basis] using hh
    have hright := congrArg (fun M => M*b.inverse) hB
    simpa only [Matrix.mul_assoc, b.right_inverse, Matrix.mul_one] using hright
  power := power
  power_eq := by rw [hpower, b.power_eq, ← pow_add]
  labels := p.selected.comp b.layout.labels
  exponent_lt := fun i => b.doubled_bound (p.selected i)
  column_eq := by
    intro i
    change exactGramColumn W (p.selected i) = _
    exact (congrArg (fun M => exactGramColumn M (p.selected i)) hW).trans
      (b.doubled_column_eq _)
  complete := by
    intro j e he
    change (A^e) *ᵥ Pi.single j 1 ∈
      exactGramPrefixSpan p.basis (fun i => b.layout.labels (p.selected i)) (toLex (j,e))
    rw [exactGramPrefixSpan_rankProfile W b.layout.labels b.layout.labels.strictMono p]
    rw [hW]
    exact b.doubled_complete j e he

end ExactGramKrylovBasis

end
end HierarchicalAbsoluteSpectral
