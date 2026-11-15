import HierarchicalAbsoluteSpectral.ExactGramCharpolyFrobenius
import HierarchicalAbsoluteSpectral.ExactGramCharpolyChainIndex

/-!
The completed arithmetic Krylov basis has literal companion matrices on
its diagonal blocks. Their last columns are read from the computed matrix
U*A*B; no roots, signs of coefficients, or spectral oracle are used here.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Polynomial
open scoped BigOperators

namespace ExactGramKrylovBasis

variable {n d : ℕ} {A : Core n}

def chains (b : ExactGramKrylovBasis A d) (hnd : n ≤ d) : ExactGramChainIndexData b.labels :=
  exactGramChainIndexData b.labels (fun i q hq =>
    b.lower_exponent_selected hnd (ofLex (b.labels i)).1 (ofLex (b.labels i)).2 i rfl q hq)

def chainColumn (b : ExactGramKrylovBasis A d) (chain : ExactGramChainIndexData b.labels)
    (g : Fin n) (q : Fin (chain.length g)) : Fin b.width := ((chain.index g).symm q).val

@[simp] theorem chainColumn_label (b : ExactGramKrylovBasis A d)
    (chain : ExactGramChainIndexData b.labels) (g : Fin n) (q : Fin (chain.length g)) :
    b.labels (b.chainColumn chain g q) = toLex (g,q.val) := chain.inverse_label g q

theorem chainColumn_injective (b : ExactGramKrylovBasis A d)
    (chain : ExactGramChainIndexData b.labels) (g : Fin n) :
    Function.Injective (b.chainColumn chain g) :=
  Subtype.val_injective.comp (chain.index g).symm.injective

def chainBlock (b : ExactGramKrylovBasis A d) (chain : ExactGramChainIndexData b.labels)
    (g : Fin n) : Core (chain.length g) :=
  exactGramIndexedBlock b.frobenius b.generator chain.length chain.index g

@[simp] theorem chainBlock_apply (b : ExactGramKrylovBasis A d)
    (chain : ExactGramChainIndexData b.labels) (g : Fin n) (r q : Fin (chain.length g)) :
    b.chainBlock chain g r q =
      b.frobenius (b.chainColumn chain g r) (b.chainColumn chain g q) := rfl

def chainCoefficients (b : ExactGramKrylovBasis A d)
    (chain : ExactGramChainIndexData b.labels) (g : Fin n) : Fin (chain.length g) → ℝ :=
  fun r => b.chainBlock chain g r ⟨chain.length g-1, by have hr := r.isLt; omega⟩

theorem frobenius_chain_successor (b : ExactGramKrylovBasis A d)
    (chain : ExactGramChainIndexData b.labels) (g : Fin n) (q : Fin (chain.length g))
    (hq : q.val+1 < chain.length g) :
    exactGramColumn b.frobenius (b.chainColumn chain g q) =
      Pi.single (b.chainColumn chain g ⟨q.val+1,hq⟩) 1 := by
  have hA : A *ᵥ exactGramColumn b.basis (b.chainColumn chain g q) =
      exactGramColumn b.basis (b.chainColumn chain g ⟨q.val+1,hq⟩) := by
    rw [b.mul_column, b.column_eq]
    simp only [b.chainColumn_label, ofLex_toLex]
  rw [b.frobenius_column, hA, b.inverse_column]

theorem chainBlock_eq_companion (b : ExactGramKrylovBasis A d)
    (chain : ExactGramChainIndexData b.labels) (g : Fin n) :
    b.chainBlock chain g = exactGramCompanionMatrix (b.chainCoefficients chain g) := by
  ext r q
  by_cases hlast : q.val+1 = chain.length g
  · simp only [exactGramCompanionMatrix, hlast, if_true, chainCoefficients]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  · have hq : q.val+1 < chain.length g := by have hq' := q.isLt; omega
    have hh := congrFun (b.frobenius_chain_successor chain g q hq) (b.chainColumn chain g r)
    have hinj := b.chainColumn_injective chain g
    change b.chainBlock chain g r q = _ at hh
    rw [hh]
    simp only [exactGramCompanionMatrix, hlast, if_false]
    simp [Pi.single_apply, hinj.eq_iff, Fin.ext_iff, eq_comm]

/-- The original matrix's characteristic polynomial is exactly the product
of the coefficients extracted from the actual finite Krylov computation. -/
theorem charpoly_eq_chain_product (b : ExactGramKrylovBasis A d) (hnd : n ≤ d)
    (chain : ExactGramChainIndexData b.labels) :
    A.charpoly = ∏ g : Fin n, exactGramCompanionPolynomial (b.chainCoefficients chain g) := by
  rw [← b.frobenius_charpoly]
  exact exactGram_charpoly_of_blockTriangular_companion b.frobenius b.generator
    chain.length chain.index (b.chainCoefficients chain)
    (b.frobenius_blockTriangular hnd) (b.chainBlock_eq_companion chain)

end ExactGramKrylovBasis

end
end HierarchicalAbsoluteSpectral
