import HierarchicalAbsoluteSpectral.CoarseAlgebraPSD
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
Principal-column interpolation data for a field-arithmetic rank profile.
The coordinates and the inverse of the selected principal minor are stored
explicitly, so no choice of an inverse is part of the algorithm.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix

theorem rankProfile_submatrix_mul {a b c d e : Type} [Fintype b]
    (A : Matrix a b ℝ) (B : Matrix b c ℝ) (f : d → a) (g : e → c) :
    (A * B).submatrix f g = A.submatrix f id * B.submatrix id g :=
  (Matrix.submatrix_mul_equiv A B f (Equiv.refl _) g).symm

structure FieldPSDPrincipalData {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) where
  dimension : ℕ
  selected : Fin dimension → ι
  selected_injective : Function.Injective selected
  coordinates : Matrix (Fin dimension) ι ℝ
  inverse : Matrix (Fin dimension) (Fin dimension) ℝ
  interpolation : coordinates.submatrix id selected = 1
  left_inverse : inverse * D.submatrix selected selected = 1
  right_inverse : D.submatrix selected selected * inverse = 1
  decomposition : coordinatesᵀ * D.submatrix selected selected * coordinates = D

namespace FieldPSDPrincipalData

variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {D E : Matrix ι ι ℝ}

def gram (p : FieldPSDPrincipalData D) : Matrix (Fin p.dimension) (Fin p.dimension) ℝ :=
  D.submatrix p.selected p.selected

@[simp] theorem inverse_gram (p : FieldPSDPrincipalData D) : p.inverse * p.gram = 1 :=
  p.left_inverse

@[simp] theorem gram_inverse (p : FieldPSDPrincipalData D) : p.gram * p.inverse = 1 :=
  p.right_inverse

theorem dimension_le (p : FieldPSDPrincipalData D) : p.dimension ≤ Fintype.card ι := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ p.selected_injective

theorem selected_rows (p : FieldPSDPrincipalData D) :
    D.submatrix p.selected id = p.gram * p.coordinates := by
  have ht : p.coordinatesᵀ.submatrix p.selected id = 1 := by
    simpa only [Matrix.transpose_submatrix, Matrix.transpose_one] using
      congrArg Matrix.transpose p.interpolation
  calc
    _ = (p.coordinatesᵀ * p.gram * p.coordinates).submatrix p.selected id :=
      congrArg (fun M => M.submatrix p.selected id) p.decomposition.symm
    _ = _ := by
      rw [Matrix.mul_assoc, rankProfile_submatrix_mul]
      simp only [ht, Matrix.submatrix_id_id, Matrix.one_mul]

theorem coordinates_eq (p : FieldPSDPrincipalData D) :
    p.coordinates = p.inverse * D.submatrix p.selected id := by
  rw [p.selected_rows, ← Matrix.mul_assoc, p.inverse_gram, Matrix.one_mul]

def cast (p : FieldPSDPrincipalData D) (h : D = E) : FieldPSDPrincipalData E := h ▸ p

def reindex (p : FieldPSDPrincipalData D) (e : κ ≃ ι) :
    FieldPSDPrincipalData (D.submatrix e e) where
  dimension := p.dimension
  selected := e.symm ∘ p.selected
  selected_injective := e.symm.injective.comp p.selected_injective
  coordinates := p.coordinates.submatrix id e
  inverse := p.inverse
  interpolation := by simpa [Matrix.submatrix_submatrix, Function.comp_def] using p.interpolation
  left_inverse := by simpa [Matrix.submatrix_submatrix, Function.comp_def] using p.left_inverse
  right_inverse := by simpa [Matrix.submatrix_submatrix, Function.comp_def] using p.right_inverse
  decomposition := by
    have h := congrArg (fun M => M.submatrix e e) p.decomposition
    simpa only [rankProfile_submatrix_mul, Matrix.submatrix_submatrix, Matrix.transpose_submatrix,
      Function.comp_def, Equiv.apply_symm_apply, Matrix.submatrix_id_id] using h

def replace (p : FieldPSDPrincipalData D)
    (R : Matrix (Fin p.dimension) ι ℝ)
    (J : Matrix (Fin p.dimension) (Fin p.dimension) ℝ)
    (hR : R = p.coordinates) (hJ : J = p.inverse) : FieldPSDPrincipalData D where
  dimension := p.dimension
  selected := p.selected
  selected_injective := p.selected_injective
  coordinates := R
  inverse := J
  interpolation := by rw [hR]; exact p.interpolation
  left_inverse := by rw [hJ]; exact p.left_inverse
  right_inverse := by rw [hJ]; exact p.right_inverse
  decomposition := by rw [hR]; exact p.decomposition

end FieldPSDPrincipalData

structure FieldOrderedPSDPrincipalData {w : ℕ} (D : Core w)
    extends FieldPSDPrincipalData D where
  selected_strictMono : StrictMono selected
  prefix_zero : ∀ (i : Fin dimension) (j : Fin w), j < selected i → coordinates i j = 0

structure FieldColumnRankProfile {n w : ℕ} (V : Matrix (Fin n) (Fin w) ℝ) where
  dimension : ℕ
  dimension_le : dimension ≤ min n w
  selected : Fin dimension ↪o Fin w
  leftInverse : Matrix (Fin dimension) (Fin n) ℝ
  left_inverse : leftInverse * V.submatrix id selected = 1
  spans : V.submatrix id selected * (leftInverse * V) = V
  prefix_zero : ∀ (i : Fin dimension) (j : Fin w),
    j < selected i → (leftInverse * V) i j = 0

namespace FieldColumnRankProfile

variable {n w : ℕ} {V : Matrix (Fin n) (Fin w) ℝ}

def basis (p : FieldColumnRankProfile V) : Matrix (Fin n) (Fin p.dimension) ℝ :=
  V.submatrix id p.selected

def coefficients (p : FieldColumnRankProfile V) :
    Matrix (Fin p.dimension) (Fin w) ℝ := p.leftInverse * V

theorem dimension_le_rows (p : FieldColumnRankProfile V) : p.dimension ≤ n :=
  p.dimension_le.trans (min_le_left _ _)

theorem dimension_le_cols (p : FieldColumnRankProfile V) : p.dimension ≤ w :=
  p.dimension_le.trans (min_le_right _ _)

theorem dimension_eq_rank (p : FieldColumnRankProfile V) : p.dimension = V.rank := by
  have hb : p.basis.rank = p.dimension := by
    apply le_antisymm
    · simpa only [Fintype.card_fin] using Matrix.rank_le_card_width p.basis
    · calc
        _ = (1 : Core p.dimension).rank := by simp [Matrix.rank_one]
        _ = (p.leftInverse * p.basis).rank := congrArg Matrix.rank p.left_inverse.symm
        _ ≤ p.basis.rank := Matrix.rank_mul_le_right _ _
  apply le_antisymm
  · rw [← hb]
    exact Matrix.rank_submatrix_le V id p.selected
  · calc
      _ = (p.basis * (p.leftInverse * V)).rank := congrArg Matrix.rank p.spans.symm
      _ ≤ p.basis.rank := Matrix.rank_mul_le_left _ _
      _ = _ := hb

end FieldColumnRankProfile

def fieldColumnRankProfileOfGram {n w : ℕ} (V : Matrix (Fin n) (Fin w) ℝ)
    {D : Core w} (p : FieldOrderedPSDPrincipalData D) (hD : D = Vᵀ * V)
    (U : Matrix (Fin p.dimension) (Fin n) ℝ)
    (hU : U = p.inverse * (V.submatrix id p.selected)ᵀ) : FieldColumnRankProfile V := by
  let L := V.submatrix id p.selected
  let R := p.coordinates
  have hG : Lᵀ * L = p.gram := by
    calc
      _ = (Vᵀ * V).submatrix p.selected p.selected :=
        (rankProfile_submatrix_mul Vᵀ V p.selected p.selected).symm
      _ = _ := congrArg (fun M => M.submatrix p.selected p.selected) hD.symm
  have hLV : Lᵀ * V = p.gram * R := by
    calc
      _ = (Vᵀ * V).submatrix p.selected id :=
        (rankProfile_submatrix_mul Vᵀ V p.selected id).symm
      _ = D.submatrix p.selected id := congrArg (fun M => M.submatrix p.selected id) hD.symm
      _ = _ := p.selected_rows
  have hUV : U * V = R := by
    rw [hU, Matrix.mul_assoc, hLV, ← Matrix.mul_assoc, p.inverse_gram, Matrix.one_mul]
  have hUL : U * L = 1 := by
    rw [hU, Matrix.mul_assoc, hG]
    exact p.left_inverse
  have hVL : Vᵀ * L = Rᵀ * p.gram := by
    have hsym : p.gramᵀ = p.gram := by
      rw [← hG, Matrix.transpose_mul, Matrix.transpose_transpose]
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hsym] using
      congrArg Matrix.transpose hLV
  have hsquare : (V - L * R)ᵀ * (V - L * R) = 0 := by
    calc
      _ = Vᵀ * V - (Vᵀ * L) * R - Rᵀ * (Lᵀ * V) + Rᵀ * (Lᵀ * L) * R := by
        simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.mul_assoc]
        module
      _ = 0 := by
        rw [hVL, hLV, hG]
        have hd : Rᵀ * p.gram * R = Vᵀ * V := p.decomposition.trans hD
        simp only [← Matrix.mul_assoc, hd]
        module
  have hspan : L * R = V := by
    have hz : V - L * R = 0 := (Matrix.conjTranspose_mul_self_eq_zero).mp (by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hsquare)
    exact (sub_eq_zero.mp hz).symm
  have hrows : p.dimension ≤ n := by
    calc
      _ = (1 : Core p.dimension).rank := by simp [Matrix.rank_one]
      _ = (U * L).rank := congrArg Matrix.rank hUL.symm
      _ ≤ L.rank := Matrix.rank_mul_le_right _ _
      _ ≤ n := by simpa only [Fintype.card_fin] using Matrix.rank_le_card_height L
  refine ⟨p.dimension, le_min hrows ?_,
    OrderEmbedding.ofStrictMono p.selected p.selected_strictMono, U, hUL, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using p.dimension_le
  · change L * (U * V) = V
    rw [hUV]
    exact hspan
  · intro i j hj
    rw [hUV]
    exact p.prefix_zero i j hj

end
end HierarchicalAbsoluteSpectral
