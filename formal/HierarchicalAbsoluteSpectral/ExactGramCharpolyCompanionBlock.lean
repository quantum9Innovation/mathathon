import HierarchicalAbsoluteSpectral.ExactGramCharpolyCompanionMatrix
import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber

/-!
Product extraction for an upper block-triangular family of cyclic chains.
Blocks may have different lengths, including zero.  The ambient indices and
the equivalences enumerating the diagonal blocks are explicit inputs.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Matrix Polynomial

variable {R : Type*} [CommRing R]

/-- Similarity invariance using an explicitly supplied inverse identity. -/
theorem exactGram_charpoly_changeBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B U : Matrix ι ι R) (hBU : B * U = 1) :
    (U * A * B).charpoly = A.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hBU, Matrix.one_mul]

/-- The same change-of-basis formula for a program state whose basis width
has not been cast to the ambient dimension. The inverse identities prove
that the two finite index types have equal cardinality. -/
theorem exactGram_charpoly_changeBasis_rectangular [Nontrivial R]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι R) (B : Matrix ι κ R) (U : Matrix κ ι R)
    (hUB : U * B = 1) (hBU : B * U = 1) :
    (U * A * B).charpoly = A.charpoly := by
  have hc : Fintype.card ι = Fintype.card κ :=
    Matrix.square_of_invertible B U hBU hUB
  have h := Matrix.charpoly_mul_comm_of_le (U * A) B (le_of_eq hc)
  simpa only [← hc, Nat.sub_self, pow_zero, one_mul, ← Matrix.mul_assoc, hBU,
    Matrix.one_mul] using h

/-- The usual block-triangular product over all block labels. Empty diagonal
blocks contribute one, so surjectivity of the block-label map is unnecessary. -/
theorem exactGram_blockTriangular_charpoly {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [LinearOrder κ]
    (A : Matrix ι ι R) (b : ι → κ) (htri : A.BlockTriangular b) :
    A.charpoly = ∏ j : κ, (A.toSquareBlock b j).charpoly := by
  classical
  rw [htri.charpoly]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro j _ hj
  have hempty : IsEmpty {i : ι // b i = j} := by
    refine ⟨fun i => hj ?_⟩
    exact Finset.mem_image.mpr ⟨i.val, Finset.mem_univ _, i.property⟩
  letI := hempty
  exact Matrix.charpoly_isEmpty

/-- A diagonal block enumerated by `Fin (length j)`. -/
def exactGramIndexedBlock {ι : Type*} {s : ℕ} (A : Matrix ι ι R)
    (b : ι → Fin s) (length : Fin s → ℕ)
    (index : ∀ j, {i : ι // b i = j} ≃ Fin (length j)) (j : Fin s) :
    Matrix (Fin (length j)) (Fin (length j)) R :=
  Matrix.reindex (index j) (index j) (A.toSquareBlock b j)

/-- An upper block-triangular matrix with explicit cyclic diagonal-block
bases has the product of the polynomials extracted from their last relations. -/
theorem exactGram_charpoly_of_blockTriangular_cyclic [Nontrivial R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ}
    (A : Matrix ι ι R) (b : ι → Fin s) (length : Fin s → ℕ)
    (index : ∀ j, {i : ι // b i = j} ≃ Fin (length j))
    (B U : ∀ j, Matrix (Fin (length j)) (Fin (length j)) R)
    (v c : ∀ j, Fin (length j) → R)
    (htri : A.BlockTriangular b)
    (hcol : ∀ j i r, B j r i =
      ((exactGramIndexedBlock A b length index j ^ (i : ℕ)) *ᵥ v j) r)
    (hUB : ∀ j, U j * B j = 1) (hBU : ∀ j, B j * U j = 1)
    (hrec : ∀ j, (exactGramIndexedBlock A b length index j ^ length j) *ᵥ v j =
      B j *ᵥ c j) :
    A.charpoly = ∏ j : Fin s, exactGramCompanionPolynomial (c j) := by
  rw [exactGram_blockTriangular_charpoly A b htri]
  apply Finset.prod_congr rfl
  intro j _
  have hj := exactGram_charpoly_of_cyclic
    (exactGramIndexedBlock A b length index j) (B j) (U j) (v j) (c j)
    (hcol j) (hUB j) (hBU j) (hrec j)
  simpa only [exactGramIndexedBlock, Matrix.charpoly_reindex] using hj

/-- The canonical enumeration of a block in a concatenation of chains. -/
def exactGramChainIndexEquiv {s : ℕ} (length : Fin s → ℕ) (j : Fin s) :
    {i : (Σ k : Fin s, Fin (length k)) // i.1 = j} ≃ Fin (length j) where
  toFun i := i.property ▸ i.val.2
  invFun i := ⟨⟨j, i⟩, rfl⟩
  left_inv i := by
    rcases i with ⟨⟨k, i⟩, h⟩
    cases h
    rfl
  right_inv _ := rfl

/-- A version with the natural sigma indexing of variable-length chains. -/
theorem exactGram_charpoly_of_cyclic_chains [Nontrivial R] {s : ℕ}
    (length : Fin s → ℕ)
    (A : Matrix (Σ j : Fin s, Fin (length j)) (Σ j : Fin s, Fin (length j)) R)
    (B U : ∀ j, Matrix (Fin (length j)) (Fin (length j)) R)
    (v c : ∀ j, Fin (length j) → R)
    (htri : A.BlockTriangular Sigma.fst)
    (hcol : ∀ j i r, B j r i =
      ((A.submatrix (fun r => ⟨j, r⟩) (fun r => ⟨j, r⟩) ^ (i : ℕ)) *ᵥ v j) r)
    (hUB : ∀ j, U j * B j = 1) (hBU : ∀ j, B j * U j = 1)
    (hrec : ∀ j, (A.submatrix (fun r => ⟨j, r⟩) (fun r => ⟨j, r⟩) ^ length j) *ᵥ v j =
      B j *ᵥ c j) :
    A.charpoly = ∏ j : Fin s, exactGramCompanionPolynomial (c j) := by
  have hblock : ∀ j : Fin s,
      exactGramIndexedBlock A Sigma.fst length (exactGramChainIndexEquiv length) j =
        A.submatrix (fun r => ⟨j, r⟩) (fun r => ⟨j, r⟩) := by
    intro j
    rfl
  apply exactGram_charpoly_of_blockTriangular_cyclic A Sigma.fst length
    (exactGramChainIndexEquiv length) B U v c htri
  · simpa only [hblock] using hcol
  · exact hUB
  · exact hBU
  · simpa only [hblock] using hrec

/-- A direct extraction interface when each enumerated diagonal block is
already the explicit companion matrix of its recurrence coefficients. -/
theorem exactGram_charpoly_of_blockTriangular_companion [Nontrivial R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ}
    (A : Matrix ι ι R) (b : ι → Fin s) (length : Fin s → ℕ)
    (index : ∀ j, {i : ι // b i = j} ≃ Fin (length j))
    (c : ∀ j, Fin (length j) → R)
    (htri : A.BlockTriangular b)
    (hdiag : ∀ j, exactGramIndexedBlock A b length index j =
      exactGramCompanionMatrix (c j)) :
    A.charpoly = ∏ j : Fin s, exactGramCompanionPolynomial (c j) := by
  rw [exactGram_blockTriangular_charpoly A b htri]
  apply Finset.prod_congr rfl
  intro j _
  calc
    (A.toSquareBlock b j).charpoly =
        (exactGramIndexedBlock A b length index j).charpoly :=
      (Matrix.charpoly_reindex (index j) _).symm
    _ = exactGramCompanionPolynomial (c j) := by
      rw [hdiag j, exactGramCompanionMatrix_charpoly]

end HierarchicalAbsoluteSpectral
