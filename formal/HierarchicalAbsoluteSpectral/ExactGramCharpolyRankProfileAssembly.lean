import HierarchicalAbsoluteSpectral.ExactGramCharpolyRankProfileBlock

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix

namespace FieldPSDPrincipalData

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {A : Matrix m m ℝ}

def block {S : Matrix n n ℝ} (p : FieldPSDPrincipalData A)
    (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef)
    (q : FieldPSDPrincipalData S) (hS : S = p.schur B C) :
    FieldPSDPrincipalData (Matrix.fromBlocks A B Bᵀ C) := by
  let H := p.inverse * B.submatrix p.selected id
  let h := H.submatrix id q.selected
  let G := Matrix.fromBlocks p.gram 0 0 q.gram
  let J := Matrix.fromBlocks p.inverse 0 0 q.inverse
  let F := Matrix.fromBlocks p.coordinates H 0 q.coordinates
  let T : Matrix (Fin p.dimension ⊕ Fin q.dimension) (Fin p.dimension ⊕ Fin q.dimension) ℝ :=
    Matrix.fromBlocks 1 h 0 1
  let P : Matrix (Fin p.dimension ⊕ Fin q.dimension) (Fin p.dimension ⊕ Fin q.dimension) ℝ :=
    Matrix.fromBlocks 1 (-h) 0 1
  let s := Sum.map p.selected q.selected
  let e : Fin (p.dimension + q.dimension) ≃ Fin p.dimension ⊕ Fin q.dimension := finSumFinEquiv.symm
  have hA : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (show Aᴴ = A from (hD.submatrix Sum.inl).isHermitian.eq)
  have hGs : p.gramᵀ = p.gram := p.gram_symmetric hA
  have hGH : p.gram * H = B.submatrix p.selected id := by
    simp only [H, ← Matrix.mul_assoc, p.gram_inverse, Matrix.one_mul]
  have hGh : p.gram * h = B.submatrix p.selected q.selected := by
    have hh := congrArg (fun M => M.submatrix id q.selected) hGH
    simpa only [rankProfile_submatrix_mul, Matrix.submatrix_id_id,
      Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp, h] using hh
  have hqG : q.gram = C.submatrix q.selected q.selected - hᵀ * p.gram * h := by
    calc
      _ = (p.schur B C).submatrix q.selected q.selected :=
        congrArg (fun M => M.submatrix q.selected q.selected) hS
      _ = C.submatrix q.selected q.selected -
          (B.submatrix p.selected q.selected)ᵀ * h := by
        change C.submatrix q.selected q.selected -
          ((B.submatrix p.selected id)ᵀ * H).submatrix q.selected q.selected = _
        rw [rankProfile_submatrix_mul]
        rfl
      _ = _ := by rw [← hGh, Matrix.transpose_mul, hGs, Matrix.mul_assoc]
  have hPT : P * T = 1 := by
    dsimp only [P, T]
    simp [Matrix.fromBlocks_multiply]
  have hTP : T * P = 1 := by
    dsimp only [P, T]
    simp [Matrix.fromBlocks_multiply]
  have hJG : J * G = 1 := by
    dsimp only [J, G]
    simp [Matrix.fromBlocks_multiply]
  have hGJ : G * J = 1 := by
    dsimp only [J, G]
    simp [Matrix.fromBlocks_multiply]
  have hselected : (Matrix.fromBlocks A B Bᵀ C).submatrix s s = Tᵀ * G * T := by
    have hs : (Matrix.fromBlocks A B Bᵀ C).submatrix s s =
        Matrix.fromBlocks p.gram (B.submatrix p.selected q.selected)
          (B.submatrix p.selected q.selected)ᵀ (C.submatrix q.selected q.selected) := by
      ext i j
      cases i <;> cases j <;> rfl
    rw [hs]
    dsimp only [T, G]
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_one, Matrix.transpose_zero, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [hGh]
    have hb : hᵀ * p.gram = (B.submatrix p.selected q.selected)ᵀ := by
      simpa only [Matrix.transpose_mul, hGs] using congrArg Matrix.transpose hGh
    rw [hb, hqG]
    simp only [← Matrix.mul_assoc, ← hb]
    congr 1
    module
  have hFsel : F.submatrix id s = T := by
    have hp := p.interpolation
    have hq := q.interpolation
    dsimp only [F, T, s]
    ext i j
    cases i with
    | inl i => cases j with
      | inl j => exact congrArg (fun M => M i j) hp
      | inr j => rfl
    | inr i => cases j with
      | inl j => rfl
      | inr j => exact congrArg (fun M => M i j) hq
  have hF : Fᵀ * G * F = Matrix.fromBlocks A B Bᵀ C := by
    dsimp only [F, G]
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    have hB : p.coordinatesᵀ * (p.gram * H) = B := by
      rw [hGH]
      exact p.offDiagonal_range B C hD
    have hBt : Hᵀ * p.gram * p.coordinates = Bᵀ := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hGs,
        Matrix.mul_assoc] using congrArg Matrix.transpose hB
    have hQ : q.coordinatesᵀ * q.gram * q.coordinates = p.schur B C :=
      q.decomposition.trans hS
    rw [(show p.coordinatesᵀ * p.gram * p.coordinates = A from p.decomposition),
      Matrix.mul_assoc p.coordinatesᵀ p.gram H, hB, hBt, hQ]
    have hHH : Hᵀ * p.gram * H = (B.submatrix p.selected id)ᵀ * H := by
      have ht : Hᵀ * p.gram = (B.submatrix p.selected id)ᵀ := by
        simpa only [Matrix.transpose_mul, hGs] using congrArg Matrix.transpose hGH
      rw [ht]
    rw [hHH]
    dsimp only [schur, H]
    congr 1
    module
  refine {
    dimension := p.dimension + q.dimension
    selected := s ∘ e
    selected_injective := ?_
    coordinates := (P * F).submatrix e id
    inverse := (P * J * Pᵀ).submatrix e e
    interpolation := ?_
    left_inverse := ?_
    right_inverse := ?_
    decomposition := ?_
  }
  · exact ((Sum.map_injective.mpr ⟨p.selected_injective, q.selected_injective⟩).comp e.injective)
  · have hi : (P * F).submatrix id s = 1 := by
      rw [rankProfile_submatrix_mul, Matrix.submatrix_id_id, hFsel, hPT]
    have hi' := congrArg (fun M => M.submatrix e e) hi
    simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp,
      Matrix.submatrix_one_equiv] using hi'
  · have hi : (P * J * Pᵀ) * (Matrix.fromBlocks A B Bᵀ C).submatrix s s = 1 := by
      rw [hselected]
      have ht : Pᵀ * Tᵀ = 1 := by
        rw [← Matrix.transpose_mul, hTP, Matrix.transpose_one]
      calc
        _ = P * J * (Pᵀ * Tᵀ) * G * T := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [ht, Matrix.mul_one, Matrix.mul_assoc P J G, hJG, Matrix.mul_one, hPT]
    change (P * J * Pᵀ).submatrix e e *
      ((Matrix.fromBlocks A B Bᵀ C).submatrix s s).submatrix e e = 1
    rw [Matrix.submatrix_mul_equiv, hi, Matrix.submatrix_one_equiv]
  · have hi : (Matrix.fromBlocks A B Bᵀ C).submatrix s s * (P * J * Pᵀ) = 1 := by
      rw [hselected]
      have ht : Tᵀ * Pᵀ = 1 := by
        rw [← Matrix.transpose_mul, hPT, Matrix.transpose_one]
      calc
        _ = Tᵀ * G * (T * P) * J * Pᵀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hTP, Matrix.mul_one, Matrix.mul_assoc Tᵀ G J, hGJ, Matrix.mul_one, ht]
    change ((Matrix.fromBlocks A B Bᵀ C).submatrix s s).submatrix e e *
      (P * J * Pᵀ).submatrix e e = 1
    rw [Matrix.submatrix_mul_equiv, hi, Matrix.submatrix_one_equiv]
  · change (P * F)ᵀ.submatrix id e * _ * (P * F).submatrix e id = _
    have hg : (Matrix.fromBlocks A B Bᵀ C).submatrix (s ∘ e) (s ∘ e) =
        ((Matrix.fromBlocks A B Bᵀ C).submatrix s s).submatrix e e := rfl
    rw [hg, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rw [Matrix.submatrix_id_id]
    have ht : Pᵀ * Tᵀ = 1 := by rw [← Matrix.transpose_mul, hTP, Matrix.transpose_one]
    rw [hselected, Matrix.transpose_mul]
    calc
      _ = Fᵀ * (Pᵀ * Tᵀ) * G * (T * P) * F := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [ht, hTP, Matrix.mul_one, Matrix.mul_one, hF]

end FieldPSDPrincipalData
end
end HierarchicalAbsoluteSpectral
