import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Monic

/-!
Exact characteristic-polynomial extraction from a cyclic Krylov basis.

The basis and its inverse are explicit inputs.  In particular, the extraction
does not assume that an algorithm already returns the characteristic polynomial.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Matrix Polynomial

variable {R : Type*} [CommRing R]

/-- The monic polynomial read from the last column relation of a Krylov chain. -/
noncomputable def exactGramCompanionPolynomial {n : ℕ} (c : Fin n → R) : R[X] :=
  X ^ n - ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

/-- Multiplying the Krylov basis by a coefficient vector evaluates the
corresponding linear combination of iterates on the generating vector. -/
theorem exactGram_cyclic_mulVec {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (v d : Fin n → R)
    (hcol : ∀ i j, B j i = ((A ^ (i : ℕ)) *ᵥ v) j) :
    B *ᵥ d = ∑ i : Fin n, d i • ((A ^ (i : ℕ)) *ᵥ v) := by
  ext j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcol]
  exact mul_comm _ _

/-- Cayley--Hamilton applied to the cyclic generator, with the leading
coefficient separated from the lower coefficients. -/
theorem exactGram_cyclic_charpoly_relation [Nontrivial R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) (v : Fin n → R)
    (hcol : ∀ i j, B j i = ((A ^ (i : ℕ)) *ᵥ v) j) :
    (A ^ n) *ᵥ v + B *ᵥ (fun i : Fin n => A.charpoly.coeff i) = 0 := by
  have hp : A.charpoly = X ^ n +
      ∑ i : Fin n, C (A.charpoly.coeff i) * X ^ (i : ℕ) := by
    have hp := A.charpoly_monic.as_sum
    simp only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      ← Fin.sum_univ_eq_sum_range] at hp
    exact hp
  have hCH := congrArg (fun M : Matrix (Fin n) (Fin n) R => M *ᵥ v)
    (Matrix.aeval_self_charpoly A)
  rw [hp] at hCH
  rw [exactGram_cyclic_mulVec A B v _ hcol]
  simpa only [map_add, map_sum, map_mul, map_pow, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.zero_mulVec] using hCH

/-- A left inverse already gives the coefficient independence needed for
exact characteristic-polynomial extraction from a cyclic basis. -/
theorem exactGram_charpoly_of_cyclic_leftInverse [Nontrivial R] {n : ℕ}
    (A B U : Matrix (Fin n) (Fin n) R) (v c : Fin n → R)
    (hcol : ∀ i j, B j i = ((A ^ (i : ℕ)) *ᵥ v) j)
    (hUB : U * B = 1) (hrec : (A ^ n) *ᵥ v = B *ᵥ c) :
    A.charpoly = exactGramCompanionPolynomial c := by
  have hCH := exactGram_cyclic_charpoly_relation A B v hcol
  rw [hrec, ← Matrix.mulVec_add] at hCH
  have hc := congrArg (fun w => U *ᵥ w) hCH
  rw [Matrix.mulVec_mulVec, hUB, Matrix.one_mulVec, Matrix.mulVec_zero] at hc
  have hcoeff : ∀ i : Fin n, A.charpoly.coeff i = -c i := by
    intro i
    have hi := congrFun hc i
    exact eq_neg_of_add_eq_zero_right hi
  have hp := A.charpoly_monic.as_sum
  simp only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    ← Fin.sum_univ_eq_sum_range, hcoeff] at hp
  simpa only [exactGramCompanionPolynomial, C_neg, neg_mul, Finset.sum_neg_distrib,
    sub_eq_add_neg] using hp

/-- The interface with two explicitly checked inverse identities. -/
theorem exactGram_charpoly_of_cyclic [Nontrivial R] {n : ℕ}
    (A B U : Matrix (Fin n) (Fin n) R) (v c : Fin n → R)
    (hcol : ∀ i j, B j i = ((A ^ (i : ℕ)) *ᵥ v) j)
    (hUB : U * B = 1) (_hBU : B * U = 1)
    (hrec : (A ^ n) *ᵥ v = B *ᵥ c) :
    A.charpoly = exactGramCompanionPolynomial c :=
  exactGram_charpoly_of_cyclic_leftInverse A B U v c hcol hUB hrec

/-- The last relation can be computed by multiplying the next Krylov vector
by the supplied inverse basis matrix. -/
theorem exactGram_charpoly_of_cyclic_coordinates [Nontrivial R] {n : ℕ}
    (A B U : Matrix (Fin n) (Fin n) R) (v : Fin n → R)
    (hcol : ∀ i j, B j i = ((A ^ (i : ℕ)) *ᵥ v) j)
    (hUB : U * B = 1) (hBU : B * U = 1) :
    A.charpoly = exactGramCompanionPolynomial (U *ᵥ ((A ^ n) *ᵥ v)) := by
  apply exactGram_charpoly_of_cyclic A B U v _ hcol hUB hBU
  rw [Matrix.mulVec_mulVec, hBU, Matrix.one_mulVec]

end HierarchicalAbsoluteSpectral
