import HierarchicalAbsoluteSpectral.CoarseAlgebraFastLDLSuccess
import HierarchicalAbsoluteSpectral.CoarseAlgebraFastLDLCost
import HierarchicalAbsoluteSpectral.CoarseAlgebraInertiaSupportData
import HierarchicalAbsoluteSpectral.GaussianLeadingRestriction

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
variable {r n : ℕ}

def FiniteCongruenceDiagonal.replace {D : Core r} (out : FiniteCongruenceDiagonal D)
    (P V : Core r) (hP : P = out.basis) (hV : V = out.inverse) : FiniteCongruenceDiagonal D where
  basis := P
  inverse := V
  diagonal := out.diagonal
  left_inverse := by rw [hP,hV]; exact out.left_inverse
  right_inverse := by rw [hP,hV]; exact out.right_inverse
  congruence := by rw [hP]; exact out.congruence

def nonzeroFormData (H T : Core r) (d : Fin r → ℝ) (hd : ∀ i, d i ≠ 0)
    (hForm : Tᵀ*H*T = Matrix.diagonal d) : FiniteCongruenceDiagonal H := by
  let V := Matrix.diagonal (fun i => (d i)⁻¹)*Tᵀ*H
  have hDi : Matrix.diagonal (fun i => (d i)⁻¹)*Matrix.diagonal d = (1 : Core r) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp [hd i]
    · simp [hij]
  have hLeft : V*T = 1 := by
    calc
      _ = Matrix.diagonal (fun i => (d i)⁻¹)*(Tᵀ*H*T) := by simp only [V,Matrix.mul_assoc]
      _ = 1 := by rw [hForm,hDi]
  exact ⟨T,V,d,hLeft,mul_eq_one_comm.mp hLeft,hForm⟩

def congruenceInertiaProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (H : Core r) (hH : Hᵀ = H) (S : Core r) :
    ArithmeticProgram (Option (FiniteCongruenceDiagonal H)) := do
  let A1 ← certify ((kernels r r r).program Sᵀ H)
  let A ← certify ((kernels r r r).program A1.val S)
  have hA : A.val = Sᵀ*H*S := by
    simp only [A.property,ArithmeticKernel.program_eval,A1.property]
  have hAsym : A.valᵀ = A.val := by rw [hA]; simp [Matrix.transpose_mul,hH,Matrix.mul_assoc]
  let out? ← fastInertiaProgram kernels r A.val hAsym
  match out? with
  | none => ArithmeticProgram.pure none
  | some out => do
    let T ← certify ((kernels r r r).program S out.basis)
    let invD ← certify (diagonalInverseProgram out.diagonal)
    let U ← certify ((kernels r r r).program T.valᵀ H)
    let V ← certify ((kernels r r r).program invD.val U.val)
    have hT : T.val = S*out.basis := T.property.trans (ArithmeticKernel.program_eval _ _ _)
    have hForm : T.valᵀ*H*T.val = Matrix.diagonal out.diagonal := by
      calc
        _ = (S*out.basis)ᵀ*H*(S*out.basis) := congrArg (fun P => Pᵀ*H*P) hT
        _ = out.basisᵀ*(Sᵀ*H*S)*out.basis := by simp only [Matrix.transpose_mul,Matrix.mul_assoc]
        _ = out.basisᵀ*A.val*out.basis := congrArg (fun B => out.basisᵀ*B*out.basis) hA.symm
        _ = _ := out.congruence
    let expected := nonzeroFormData H T.val out.diagonal out.nonzero hForm
    have hV : V.val = expected.inverse := by
      simp only [V.property,ArithmeticKernel.program_eval,U.property,invD.property,
        diagonalInverseProgram_eval,expected,nonzeroFormData,Matrix.mul_assoc]
    ArithmeticProgram.pure (some (expected.replace T.val V.val rfl hV))

theorem congruenceInertiaProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (H : Core r) (hH : Hᵀ = H) (S : Core r) : (congruenceInertiaProgram kernels H hH S).admissible := by
  have hdiag (A : Core r) (out : RegularCongruenceData A) :
      (diagonalInverseProgram out.diagonal).admissible := diagonalInverseProgram_admissible _ out.nonzero
  simp only [congruenceInertiaProgram,admissible_bind,certify_admissible,
    ArithmeticKernel.program_admissible,fastInertiaProgram_admissible,true_and]
  split
  · trivial
  · simp only [admissible_bind,certify_admissible,ArithmeticKernel.program_admissible,
      hdiag,admissible_pure,and_self]

theorem congruenceInertiaProgram_work_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (H : Core r) (hH : Hᵀ = H) (S : Core r) :
    (congruenceInertiaProgram kernels H hH S).work ≤ fastLDLCost kernels r+5*(kernels r r r).cost+r := by
  simp only [congruenceInertiaProgram,work_bind,certify_work,ArithmeticKernel.program_work]
  split
  · simp only [work_pure]
    calc
      _ ≤ (kernels r r r).cost+((kernels r r r).cost+(fastLDLCost kernels r+0)) := by
        gcongr
        exact fastInertiaProgram_work_le _ _ _ _
      _ ≤ _ := by omega
  · simp only [work_bind,certify_work,ArithmeticKernel.program_work,diagonalInverseProgram_work,work_pure]
    calc
      _ ≤ (kernels r r r).cost+((kernels r r r).cost+(fastLDLCost kernels r+
          ((kernels r r r).cost+(r+((kernels r r r).cost+((kernels r r r).cost+0)))))) := by
        gcongr
        exact fastInertiaProgram_work_le _ _ _ _
      _ = _ := by omega

theorem congruenceInertiaProgram_success (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (H : Core r) (hH : Hᵀ = H) (S : Core r) (hReg : LeadingPrincipalRegular (Sᵀ*H*S)) :
    ∃ out, (congruenceInertiaProgram kernels H hH S).eval = some out := by
  let A1 := (certify ((kernels r r r).program Sᵀ H)).eval
  let A := (certify ((kernels r r r).program A1.val S)).eval
  have hA : A.val = Sᵀ*H*S := by dsimp [A,A1]; simp only [certify_eval,ArithmeticKernel.program_eval]
  have hAsym : A.valᵀ = A.val := by rw [hA]; simp [Matrix.transpose_mul,hH,Matrix.mul_assoc]
  have hRegA : LeadingPrincipalRegular A.val := by rw [hA]; exact hReg
  obtain ⟨out,ho⟩ := fastInertiaProgram_success kernels r A.val hAsym hRegA
  unfold congruenceInertiaProgram
  rw [eval_bind,eval_bind,eval_bind,ho]
  rw [eval_bind,eval_bind,eval_bind,eval_bind,eval_pure]
  exact ⟨_,rfl⟩

theorem InertiaSupport.compressed_transpose {D : Core n} (support : InertiaSupport D) (hD : Dᵀ = D) :
    support.compressedᵀ = support.compressed := by
  rw [support.compressed_eq]
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hD,Matrix.mul_assoc]

def gaussianReducedInertiaProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {D : Core n} (support : InertiaSupport D) (hD : Dᵀ = D) (g : Fin (n*n) → ℝ) :
    ArithmeticProgram (Option (FiniteCongruenceDiagonal support.compressed)) :=
  congruenceInertiaProgram kernels support.compressed (support.compressed_transpose hD)
    ((gaussianSquareMatrix n g).submatrix (Fin.castLEEmb support.dimension_le)
      (Fin.castLEEmb support.dimension_le))

theorem gaussianReducedInertiaProgram_success_ae (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {D : Core n} (support : InertiaSupport D) (hD : Dᵀ = D) :
    ∀ᵐ g ∂gaussianVector (n*n), ∃ out, (gaussianReducedInertiaProgram kernels support hD g).eval = some out := by
  have hH : support.compressed.IsHermitian := by
    simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
      using support.compressed_transpose hD
  have he := gaussian_congruence_leading_submatrix_regular_and_invertible_ae support.dimension_le
    support.compressed (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) support.compressed_isUnit
  filter_upwards [he] with g hg
  exact congruenceInertiaProgram_success kernels _ (support.compressed_transpose hD) _ hg.1

end
end HierarchicalAbsoluteSpectral
