import HierarchicalAbsoluteSpectral.MatrixInequalities

/-! The exact congruence certificate returned by symmetric elimination.
Diagonal entries are field pivots, rather than computed eigenvalues. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
variable {n : ℕ}

structure FiniteCongruenceDiagonal (D : Core n) where
  basis : Core n
  inverse : Core n
  diagonal : Fin n → ℝ
  left_inverse : inverse*basis = 1
  right_inverse : basis*inverse = 1
  congruence : basisᵀ*D*basis = Matrix.diagonal diagonal

namespace FiniteCongruenceDiagonal

theorem isUnit {D : Core n} (out : FiniteCongruenceDiagonal D) : IsUnit out.basis :=
  ⟨⟨out.basis,out.inverse,out.right_inverse,out.left_inverse⟩,rfl⟩

theorem isUnit_det {D : Core n} (out : FiniteCongruenceDiagonal D) : IsUnit out.basis.det :=
  (Matrix.isUnit_iff_isUnit_det _).mp out.isUnit

def positiveCount {D : Core n} (out : FiniteCongruenceDiagonal D) : ℕ :=
  (Finset.univ.filter (fun i => 0 < out.diagonal i)).card

def negativeCount {D : Core n} (out : FiniteCongruenceDiagonal D) : ℕ :=
  (Finset.univ.filter (fun i => out.diagonal i < 0)).card

def zeroCount {D : Core n} (out : FiniteCongruenceDiagonal D) : ℕ :=
  (Finset.univ.filter (fun i => out.diagonal i = 0)).card

end FiniteCongruenceDiagonal

end
end HierarchicalAbsoluteSpectral
