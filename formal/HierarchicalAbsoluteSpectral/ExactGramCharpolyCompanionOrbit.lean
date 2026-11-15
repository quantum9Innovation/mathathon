import HierarchicalAbsoluteSpectral.ExactGramCharpolyCompanion

/-!
Cayley--Hamilton closes every sufficiently long truncated Krylov orbit.
These lemmas support the invariant generator flags used when extracting
several companion chains from an ordered Krylov basis.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Matrix Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- The dimension-th Krylov vector is an explicit combination of the
preceding ones, with coefficients from Cayley--Hamilton. -/
theorem exactGram_pow_dim_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (v : Fin n → R) :
    (A ^ n) *ᵥ v =
      ∑ i : Fin n, (-A.charpoly.coeff i) • ((A ^ (i : ℕ)) *ᵥ v) := by
  let B : Matrix (Fin n) (Fin n) R := fun j i => ((A ^ (i : ℕ)) *ᵥ v) j
  have hcol : ∀ i j, B j i = ((A ^ (i : ℕ)) *ᵥ v) j := fun _ _ => rfl
  have hCH := exactGram_cyclic_charpoly_relation A B v hcol
  rw [exactGram_cyclic_mulVec A B v _ hcol] at hCH
  simpa only [Finset.sum_neg_distrib, neg_smul] using eq_neg_of_add_eq_zero_left hCH

/-- Once the truncation length reaches the ambient dimension, every later
Krylov vector lies in the span of the truncated orbit. -/
theorem exactGram_pow_mulVec_mem_span {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (hnd : n ≤ d) (k : ℕ) :
    (A ^ k) *ᵥ v ∈
      Submodule.span R (Set.range (fun i : Fin d => (A ^ (i : ℕ)) *ᵥ v)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k < d
      · exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
      · have hnk : n ≤ k := hnd.trans (Nat.le_of_not_gt hk)
        have hCH := exactGram_pow_dim_mulVec A ((A ^ (k-n)) *ᵥ v)
        simp only [Matrix.mulVec_mulVec, ← pow_add] at hCH
        rw [Nat.add_sub_of_le hnk] at hCH
        rw [hCH]
        apply Submodule.sum_mem
        intro i _
        apply Submodule.smul_mem
        apply ih
        have hi := i.isLt
        omega

/-- Any submodule containing the first `d` iterates contains the entire
orbit when `d` reaches the ambient dimension. -/
theorem exactGram_pow_mulVec_mem_of_initial {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R)
    (S : Submodule R (Fin n → R)) (hnd : n ≤ d)
    (hmem : ∀ i : Fin d, (A ^ (i : ℕ)) *ᵥ v ∈ S) (k : ℕ) :
    (A ^ k) *ᵥ v ∈ S := by
  apply (show Submodule.span R
      (Set.range (fun i : Fin d => (A ^ (i : ℕ)) *ᵥ v)) ≤ S from ?_)
    (exactGram_pow_mulVec_mem_span A v hnd k)
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hmem i

end HierarchicalAbsoluteSpectral
