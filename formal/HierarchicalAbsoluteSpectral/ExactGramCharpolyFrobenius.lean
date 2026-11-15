import HierarchicalAbsoluteSpectral.ExactGramCharpolyTerminal
import HierarchicalAbsoluteSpectral.ExactGramCharpolyCompanionBlock

/-!
The matrix in a completed compressed Krylov basis is upper block triangular
by generator. Both changes of basis are explicit matrices produced by the
field-arithmetic program.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix

namespace ExactGramKrylovBasis

variable {n d : ℕ} {A : Core n}

def generator (b : ExactGramKrylovBasis A d) (i : Fin b.width) : Fin n :=
  (ofLex (b.labels i)).1

def frobenius (b : ExactGramKrylovBasis A d) : Core b.width := b.inverse*A*b.basis

theorem inverse_column (b : ExactGramKrylovBasis A d) (i : Fin b.width) :
    b.inverse *ᵥ exactGramColumn b.basis i = Pi.single i 1 := by
  have hcol : b.basis *ᵥ Pi.single i 1 = exactGramColumn b.basis i := by
    rw [Matrix.mulVec_single_one]
    rfl
  rw [← hcol, Matrix.mulVec_mulVec, b.left_inverse, Matrix.one_mulVec]

theorem frobenius_column (b : ExactGramKrylovBasis A d) (i : Fin b.width) :
    exactGramColumn b.frobenius i = b.inverse *ᵥ (A *ᵥ exactGramColumn b.basis i) := by
  have hcol (M : Matrix (Fin b.width) (Fin b.width) ℝ) :
      M *ᵥ Pi.single i 1 = exactGramColumn M i := by
    rw [Matrix.mulVec_single_one]
    rfl
  rw [← hcol]
  have hB : b.basis *ᵥ Pi.single i 1 = exactGramColumn b.basis i := by
    rw [Matrix.mulVec_single_one]
    rfl
  rw [← hB]
  simp only [frobenius, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem coordinate_zero_of_generator_mem (b : ExactGramKrylovBasis A d)
    (g : ℕ) (i : Fin b.width) (hi : g ≤ (b.generator i).val)
    (x : Fin n → ℝ) (hx : x ∈ b.generatorSpan g) : (b.inverse *ᵥ x) i = 0 := by
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i).comp b.inverse.mulVecLin
  have hle : b.generatorSpan g ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro z ⟨k,hk,rfl⟩
    change (b.inverse *ᵥ exactGramColumn b.basis k) i = 0
    rw [b.inverse_column]
    have hki : k ≠ i := by
      intro heq
      subst k
      exact (Nat.not_lt_of_ge hi) hk
    simp [Pi.single_apply, hki, hki.symm]
  exact hle hx

theorem frobenius_blockTriangular (b : ExactGramKrylovBasis A d) (hnd : n ≤ d) :
    b.frobenius.BlockTriangular b.generator := by
  intro i j hij
  have hgen : (b.generator j).val+1 ≤ (b.generator i).val := Nat.succ_le_of_lt hij
  have hmem := b.orbit_mem_generator hnd ((b.generator j).val+1) (b.generator j)
    (Nat.lt_succ_self _) ((ofLex (b.labels j)).2+1)
  have hzero := b.coordinate_zero_of_generator_mem _ i hgen _ hmem
  have hcol := congrFun (b.frobenius_column j) i
  rw [b.mul_column] at hcol
  exact hcol.trans hzero

theorem frobenius_charpoly (b : ExactGramKrylovBasis A d) :
    b.frobenius.charpoly = A.charpoly :=
  exactGram_charpoly_changeBasis_rectangular A b.basis b.inverse b.left_inverse b.right_inverse

theorem width_eq (b : ExactGramKrylovBasis A d) : b.width = n := by
  simpa only [Fintype.card_fin] using
    (Matrix.square_of_invertible b.basis b.inverse b.right_inverse b.left_inverse).symm

end ExactGramKrylovBasis

end
end HierarchicalAbsoluteSpectral
