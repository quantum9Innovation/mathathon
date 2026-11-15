import HierarchicalAbsoluteSpectral.StrongFilterDiagonal

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open scoped MatrixOrder Matrix.Norms.L2Operator

def leadingEmbedding {r k : ℕ} (hr : r ≤ k) : Fin r ↪ Fin k :=
  ⟨Fin.castLE hr, Fin.castLE_injective hr⟩

def leadingMask {k : ℕ} (r : ℕ) (d : Fin k → ℝ) : Fin k → ℝ :=
  fun i => if i.val < r then d i else 0

def trailingMask {k : ℕ} (r : ℕ) (d : Fin k → ℝ) : Fin k → ℝ :=
  fun i => if i.val < r then 0 else d i

theorem leadingEmbedding_projector {r k : ℕ} (hr : r ≤ k) :
    columnEmbedding (leadingEmbedding hr)*(columnEmbedding (leadingEmbedding hr))ᵀ =
      Matrix.diagonal (leadingMask r (fun _ : Fin k => (1 : ℝ))) := by
  ext i j
  by_cases hi : i.val < r
  · let a : Fin r := ⟨i.val, hi⟩
    have hea : leadingEmbedding hr a = i := Fin.ext rfl
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · simp [columnEmbedding, Matrix.submatrix, Matrix.one_apply, hea,
        Matrix.diagonal_apply, leadingMask, hi, eq_comm]
    · intro b hb hba
      have hieb : i ≠ leadingEmbedding hr b := by
        intro he
        have hab := (leadingEmbedding hr).injective (hea.trans he)
        exact hba hab.symm
      simp [columnEmbedding, Matrix.submatrix, Matrix.one_apply, hieb]
    · simp
  · have hzero (b : Fin r) : i ≠ leadingEmbedding hr b := by
      intro he
      have : i.val = b.val := congrArg Fin.val he
      exact hi (this ▸ b.isLt)
    simp [Matrix.mul_apply, columnEmbedding, Matrix.submatrix, Matrix.one_apply,
      hzero, Matrix.diagonal_apply, leadingMask, hi]

theorem columnEmbedding_diagonal_intertwines {r k : ℕ} (e : Fin r ↪ Fin k)
    (d : Fin k → ℝ) :
    columnEmbedding e*Matrix.diagonal (fun j => d (e j)) = Matrix.diagonal d*columnEmbedding e := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = e j
  · simp [columnEmbedding, Matrix.submatrix, Matrix.one_apply, hij]
  · simp [columnEmbedding, Matrix.submatrix, Matrix.one_apply, hij]

theorem leading_diagonal_lift {r k : ℕ} (hr : r ≤ k) (d : Fin k → ℝ) :
    columnEmbedding (leadingEmbedding hr)*Matrix.diagonal (fun j => d (leadingEmbedding hr j))*
        (columnEmbedding (leadingEmbedding hr))ᵀ = Matrix.diagonal (leadingMask r d) := by
  rw [columnEmbedding_diagonal_intertwines, Matrix.mul_assoc, leadingEmbedding_projector,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i.val < r <;> simp [leadingMask, hi]

theorem spectral_filter_split {r k : ℕ} (hr : r ≤ k) (Q : Core k)
    (f : Fin k → ℝ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    Q*Matrix.diagonal f*Ω =
      (Q*columnEmbedding (leadingEmbedding hr))*
          (Matrix.diagonal (fun j => f (leadingEmbedding hr j))*
            ((columnEmbedding (leadingEmbedding hr))ᵀ*Ω)) +
        Q*(Matrix.diagonal (trailingMask r f)*Ω) := by
  have hsplit : Matrix.diagonal f = Matrix.diagonal (leadingMask r f)+Matrix.diagonal (trailingMask r f) := by
    rw [← Matrix.diagonal_add]
    congr 1
    funext i
    by_cases hi : i.val < r <;> simp [leadingMask, trailingMask, hi]
  conv_lhs => rw [hsplit]
  rw [Matrix.mul_add, Matrix.add_mul, ← leading_diagonal_lift hr]
  simp only [Matrix.mul_assoc]

theorem orthogonal_diagonal_mul {k : ℕ} (Q : Core k) (hQ : Qᵀ*Q = 1)
    (a b : Fin k → ℝ) :
    (Q*Matrix.diagonal a*Qᵀ)*(Q*Matrix.diagonal b*Qᵀ) =
      Q*Matrix.diagonal (fun i => a i*b i)*Qᵀ := by
  calc
    _ = Q*(Matrix.diagonal a*(Qᵀ*Q)*Matrix.diagonal b)*Qᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hQ, Matrix.mul_one, Matrix.diagonal_mul_diagonal]; rfl

theorem orthogonal_diagonal_complement {k : ℕ} (Q : Core k) (hQ : Q*Qᵀ = 1)
    (a : Fin k → ℝ) :
    (1 : Core k)-Q*Matrix.diagonal a*Qᵀ =
      Q*Matrix.diagonal (fun i => 1-a i)*Qᵀ := by
  rw [show Matrix.diagonal (fun i => 1-a i) = 1-Matrix.diagonal a from by
    ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQ]

end
end HierarchicalAbsoluteSpectral
