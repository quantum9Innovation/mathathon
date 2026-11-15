import HierarchicalAbsoluteSpectral.ExactGramCharpolyRankProfileAssembly

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix

def rankProfileAppendSelected {a b l r : ℕ}
    (s : Fin a → Fin l) (t : Fin b → Fin r) : Fin (a+b) → Fin (l+r) :=
  fun i => finSumFinEquiv (Sum.map s t (finSumFinEquiv.symm i))

theorem rankProfileAppendSelected_strictMono {a b l r : ℕ}
    (s : Fin a → Fin l) (t : Fin b → Fin r) (hs : StrictMono s) (ht : StrictMono t) :
    StrictMono (rankProfileAppendSelected s t) := by
  intro i j hij
  cases i using Fin.addCases with
  | left i => cases j using Fin.addCases with
    | left j =>
      simp only [rankProfileAppendSelected, finSumFinEquiv_symm_apply_castAdd,
        Sum.map_inl, finSumFinEquiv_apply_left]
      exact hs hij
    | right j =>
      simp only [rankProfileAppendSelected, finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd, Sum.map_inl, Sum.map_inr,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
      change (s i).val < l + (t j).val
      omega
  | right i => cases j using Fin.addCases with
    | left j =>
      have hi := i.isLt
      have hj := j.isLt
      change a + i.val < j.val at hij
      omega
    | right j =>
      change a + i.val < a + j.val at hij
      have hh := ht (show i < j by omega)
      simp only [rankProfileAppendSelected, finSumFinEquiv_symm_apply_natAdd,
        Sum.map_inr, finSumFinEquiv_apply_right]
      change l + (t i).val < l + (t j).val
      exact Nat.add_lt_add_left hh l

namespace FieldOrderedPSDPrincipalData

variable {l r : ℕ} {A : Core l}

def block {S : Core r} (p : FieldOrderedPSDPrincipalData A)
    (B : Matrix (Fin l) (Fin r) ℝ) (C : Core r)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef)
    (q : FieldOrderedPSDPrincipalData S) (hS : S = p.schur B C) :
    FieldOrderedPSDPrincipalData ((Matrix.fromBlocks A B Bᵀ C).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm) := by
  let raw := p.toFieldPSDPrincipalData.block B C hD q.toFieldPSDPrincipalData hS
  let out := raw.reindex (finSumFinEquiv.symm : Fin (l+r) ≃ Fin l ⊕ Fin r)
  have hm : StrictMono out.selected :=
    rankProfileAppendSelected_strictMono p.selected q.selected p.selected_strictMono q.selected_strictMono
  refine { out with selected_strictMono := hm, prefix_zero := ?_ }
  intro i j hj
  let H := p.inverse * B.submatrix p.selected id
  let h := H.submatrix id q.selected
  have hc : out.coordinates =
      (Matrix.fromBlocks p.coordinates (H - h * q.coordinates) 0 q.coordinates).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    change ((Matrix.fromBlocks 1 (-h) 0 1 *
      Matrix.fromBlocks p.coordinates H 0 q.coordinates).submatrix finSumFinEquiv.symm id).submatrix
        id finSumFinEquiv.symm = _
    rw [Matrix.submatrix_submatrix, Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.neg_mul, sub_eq_add_neg, Function.comp_id, Function.id_comp]
  rw [hc]
  change j < rankProfileAppendSelected p.selected q.selected i at hj
  cases i using Fin.addCases with
  | left i => cases j using Fin.addCases with
    | left j =>
      simp only [rankProfileAppendSelected, finSumFinEquiv_symm_apply_castAdd,
        Sum.map_inl, finSumFinEquiv_apply_left] at hj
      simpa only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
        Matrix.fromBlocks_apply₁₁] using p.prefix_zero i j hj
    | right j =>
      simp only [rankProfileAppendSelected, finSumFinEquiv_symm_apply_castAdd,
        Sum.map_inl, finSumFinEquiv_apply_left] at hj
      change l + j.val < (p.selected i).val at hj
      have hi := (p.selected i).isLt
      omega
  | right i => cases j using Fin.addCases with
    | left j =>
      simp only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
        finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    | right j =>
      simp only [rankProfileAppendSelected, finSumFinEquiv_symm_apply_natAdd,
        Sum.map_inr, finSumFinEquiv_apply_right] at hj
      change l + j.val < l + (q.selected i).val at hj
      have hj' : j < q.selected i := by omega
      simpa only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
        Matrix.fromBlocks_apply₂₂] using q.prefix_zero i j hj'

def cast {w : ℕ} {D E : Core w} (p : FieldOrderedPSDPrincipalData D) (h : D = E) :
    FieldOrderedPSDPrincipalData E := h ▸ p

def reindexSize {a b : ℕ} {D : Core a} (p : FieldOrderedPSDPrincipalData D) (h : a = b) :
    FieldOrderedPSDPrincipalData (D.submatrix (finCongr h.symm) (finCongr h.symm)) where
  toFieldPSDPrincipalData := p.toFieldPSDPrincipalData.reindex (finCongr h.symm)
  selected_strictMono := by
    intro i j hij
    change (p.selected i).val < (p.selected j).val
    exact p.selected_strictMono hij
  prefix_zero := by
    intro i j hj
    change p.coordinates i (Fin.cast h.symm j) = 0
    apply p.prefix_zero
    exact hj

def replace {w : ℕ} {D : Core w} (p : FieldOrderedPSDPrincipalData D)
    (R : Matrix (Fin p.dimension) (Fin w) ℝ) (J : Core p.dimension)
    (hR : R = p.coordinates) (hJ : J = p.inverse) : FieldOrderedPSDPrincipalData D where
  toFieldPSDPrincipalData := p.toFieldPSDPrincipalData.replace R J hR hJ
  selected_strictMono := p.selected_strictMono
  prefix_zero := by
    intro i j hj
    change R i j = 0
    rw [hR]
    exact p.prefix_zero i j hj

end FieldOrderedPSDPrincipalData
end
end HierarchicalAbsoluteSpectral
