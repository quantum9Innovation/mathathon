import HierarchicalAbsoluteSpectral.MinMaxNear
import HierarchicalAbsoluteSpectral.MassSpectrumRoots

/-! The nonzero sorted spectra of the two Gram operators agree. This proves
the connection to Mathlib's actual zero-indexed singular values, including
dimension padding and repeated eigenvalues, without an assumed SVD. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open WithLp
open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {n m : ℕ}

theorem eigenbasis_head_square_bound (S : E →ₗ[ℝ] E) (hS : S.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n) (ha : 0 ≤ hS.eigenvalues hn j) (v : E)
    (htail : ∀ i, j < i → (hS.eigenvectorBasis hn).repr v i = 0) :
    hS.eigenvalues hn j*⟪v,S v⟫_ℝ ≤ ⟪v,S (S v)⟫_ℝ := by
  rw [eigenbasis_inner_apply S hS hn, eigenbasis_inner_apply_sq S hS hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hij : j < i
  · rw [htail i hij]
    simp
  · have hei := hS.eigenvalues_antitone hn (le_of_not_gt hij)
    have hnz : 0 ≤ hS.eigenvalues hn i := ha.trans hei
    have hh := mul_le_mul_of_nonneg_right hei
      (mul_nonneg hnz (sq_nonneg ((hS.eigenvectorBasis hn).repr v i)))
    nlinarith only [hh]

theorem gramEigenvalue_le_reverse (T : E →ₗ[ℝ] F)
    (hn : Module.finrank ℝ E = n) (hm : Module.finrank ℝ F = m)
    (j : ℕ) (hjn : j < n) (hjm : j < m) :
    T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨j,hjn⟩ ≤
      T.isSymmetric_self_comp_adjoint.eigenvalues hm ⟨j,hjm⟩ := by
  let S := T.adjoint.comp T
  let U := T.comp T.adjoint
  let hS := T.isSymmetric_adjoint_comp_self
  let hU := T.isSymmetric_self_comp_adjoint
  let a := hS.eigenvalues hn ⟨j,hjn⟩
  by_cases ha : a ≤ 0
  · exact ha.trans (T.isPositive_self_comp_adjoint.nonneg_eigenvalues hm ⟨j,hjm⟩)
  have hap : 0 < a := lt_of_not_ge ha
  let V := spectralHeadEmbedding S hS hn ⟨j,hjn⟩
  let W := T.comp V
  have hhead (z : EuclideanSpace ℝ (Fin (j+1))) : a*⟪V z,V z⟫_ℝ ≤ ⟪V z,S (V z)⟫_ℝ :=
    eigenbasis_head_bound S hS hn ⟨j,hjn⟩ _
      (fun i hi => spectralHeadEmbedding_tail_zero S hS hn ⟨j,hjn⟩ z i hi)
  have hW : Function.Injective W := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    have hz' : T (V z) = 0 := hz
    have hh := hhead z
    have hq : ⟪V z,S (V z)⟫_ℝ = 0 := by
      change ⟪V z,T.adjoint (T (V z))⟫_ℝ = 0
      rw [T.adjoint_inner_right, hz']
      simp
    have hVz : V z = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      nlinarith [real_inner_self_nonneg (x := V z)]
    apply spectralHeadEmbedding_injective S hS hn ⟨j,hjn⟩
    simpa only [map_zero] using hVz
  apply eigenvalue_lower_of_injective_form U hU hm ⟨j,hjm⟩ W hW a
  intro z
  have hh := eigenbasis_head_square_bound S hS hn ⟨j,hjn⟩ hap.le (V z)
    (fun i hi => spectralHeadEmbedding_tail_zero S hS hn ⟨j,hjn⟩ z i hi)
  have hnorm : ⟪W z,W z⟫_ℝ = ⟪V z,S (V z)⟫_ℝ := by
    exact (T.adjoint_inner_right (V z) (T (V z))).symm
  have hform : ⟪W z,U (W z)⟫_ℝ = ⟪V z,S (S (V z))⟫_ℝ := by
    exact (T.adjoint_inner_right (V z) (T (T.adjoint (T (V z))))).symm
  rw [hnorm, hform]
  exact hh

theorem gramEigenvalues_eq (T : E →ₗ[ℝ] F)
    (hn : Module.finrank ℝ E = n) (hm : Module.finrank ℝ F = m)
    (j : ℕ) (hjn : j < n) (hjm : j < m) :
    T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨j,hjn⟩ =
      T.isSymmetric_self_comp_adjoint.eigenvalues hm ⟨j,hjm⟩ := by
  apply le_antisymm (gramEigenvalue_le_reverse T hn hm j hjn hjm)
  simpa only [LinearMap.adjoint_adjoint] using
    gramEigenvalue_le_reverse T.adjoint hm hn j hjm hjn

theorem sq_singularValue_eq_reverseGram (T : E →ₗ[ℝ] F)
    (hn : Module.finrank ℝ E = n) (hm : Module.finrank ℝ F = m)
    (j : ℕ) (hjn : j < n) (hjm : j < m) :
    T.singularValues j^2 = T.isSymmetric_self_comp_adjoint.eigenvalues hm ⟨j,hjm⟩ := by
  rw [T.sq_singularValues_of_lt hn hjn, gramEigenvalues_eq T hn hm j hjn hjm]

open Matrix
open scoped MatrixOrder

theorem matrix_transpose_adjoint {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
    Mᵀ.toEuclideanLin = M.toEuclideanLin.adjoint := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint M

theorem matrix_adjoint_gram {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
    (Mᵀ*M).toEuclideanLin = M.toEuclideanLin.adjoint.comp M.toEuclideanLin := by
  rw [Matrix.toLpLin_mul, matrix_transpose_adjoint]

theorem matrix_reverse_gram {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
    (M*Mᵀ).toEuclideanLin = M.toEuclideanLin.comp M.toEuclideanLin.adjoint := by
  rw [Matrix.toLpLin_mul, matrix_transpose_adjoint]

theorem sq_tailSingularValue_eq_reverseGram {a b : ℕ}
    (M : Matrix (Fin a) (Fin b) ℝ) (j : ℕ) (hja : j < a) (hjb : j < b) :
    tailSingularValue M j^2 = orderedEigenvalue (M*Mᵀ)
      (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.posSemidef_self_mul_conjTranspose M).isHermitian) ⟨j,hja⟩ := by
  have hh := sq_singularValue_eq_reverseGram M.toEuclideanLin finrank_euclideanSpace_fin
    finrank_euclideanSpace_fin j hjb hja
  simpa only [tailSingularValue, orderedEigenvalue, matrix_reverse_gram] using hh

theorem tailSingularValue_eq_of_gram {a b c : ℕ}
    (A : Matrix (Fin a) (Fin c) ℝ) (B : Matrix (Fin b) (Fin c) ℝ)
    (hgram : Aᵀ*A = Bᵀ*B) (j : ℕ) :
    tailSingularValue A j = tailSingularValue B j := by
  by_cases hj : j < c
  · have hlin : A.toEuclideanLin.adjoint.comp A.toEuclideanLin =
        B.toEuclideanLin.adjoint.comp B.toEuclideanLin := by
      rw [← matrix_adjoint_gram, ← matrix_adjoint_gram, hgram]
    simp only [tailSingularValue,
      A.toEuclideanLin.singularValues_of_lt finrank_euclideanSpace_fin hj,
      B.toEuclideanLin.singularValues_of_lt finrank_euclideanSpace_fin hj]
    congr 1
    simp only [hlin]
  · have hh : Module.finrank ℝ (EuclideanSpace ℝ (Fin c)) ≤ j := by
      simpa using Nat.le_of_not_gt hj
    simp only [tailSingularValue, A.toEuclideanLin.singularValues_of_finrank_le hh,
      B.toEuclideanLin.singularValues_of_finrank_le hh]

end
end HierarchicalAbsoluteSpectral
