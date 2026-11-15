import HierarchicalAbsoluteSpectral.ExactGramCharpolyCompanion

/-! Explicit companion matrices, with the final column in the sign convention
`X^n - sum i, C (c i) * X^i`. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Matrix Polynomial

variable {R : Type*} [CommRing R]

/-- Ones on the subdiagonal and the final recurrence coefficients in the
last column. This definition also covers the empty matrix. -/
def exactGramCompanionMatrix {n : ℕ} (c : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if j.val + 1 = n then c i else if i.val = j.val + 1 then 1 else 0

theorem exactGramCompanionMatrix_mulVec_single {n : ℕ} (c : Fin n → R)
    (j : Fin n) (hj : j.val + 1 < n) :
    exactGramCompanionMatrix c *ᵥ Pi.single j 1 = Pi.single ⟨j.val + 1, hj⟩ 1 := by
  rw [Matrix.mulVec_single_one]
  ext i
  change exactGramCompanionMatrix c i j =
    (Pi.single ⟨j.val + 1, hj⟩ (1 : R) : Fin n → R) i
  simp [exactGramCompanionMatrix, ne_of_lt hj, Pi.single_apply, Fin.ext_iff]

theorem exactGramCompanionMatrix_mulVec_last {n : ℕ} (c : Fin (n+1) → R) :
    exactGramCompanionMatrix c *ᵥ Pi.single (Fin.last n) 1 = c := by
  rw [Matrix.mulVec_single_one]
  ext i
  change exactGramCompanionMatrix c i (Fin.last n) = c i
  simp [exactGramCompanionMatrix]

/-- Before the end of the chain, the iterates of the first coordinate vector
are exactly the remaining coordinate vectors. -/
theorem exactGramCompanionMatrix_pow_mulVec {n : ℕ} (c : Fin (n+1) → R)
    (k : ℕ) (hk : k < n+1) :
    (exactGramCompanionMatrix c ^ k) *ᵥ Pi.single 0 1 = Pi.single ⟨k, hk⟩ 1 := by
  induction k with
  | zero =>
      rw [pow_zero, Matrix.one_mulVec]
      apply congrArg (fun i : Fin (n+1) => (Pi.single i (1 : R) : Fin (n+1) → R))
      exact Fin.ext rfl
  | succ k ih =>
      have hprev : k < n+1 := Nat.lt_trans (Nat.lt_succ_self k) hk
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih hprev]
      exact exactGramCompanionMatrix_mulVec_single c ⟨k, hprev⟩ hk

/-- The exact characteristic polynomial of the explicit companion matrix.
The proof uses Cayley--Hamilton and the explicit standard cyclic basis. -/
theorem exactGramCompanionMatrix_charpoly [Nontrivial R] {n : ℕ} (c : Fin n → R) :
    (exactGramCompanionMatrix c).charpoly = exactGramCompanionPolynomial c := by
  cases n with
  | zero => simp [exactGramCompanionPolynomial]
  | succ n =>
      apply exactGram_charpoly_of_cyclic (exactGramCompanionMatrix c) 1 1
        (Pi.single 0 1) c
      · intro i j
        rw [exactGramCompanionMatrix_pow_mulVec c i.val i.isLt]
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      · simp
      · simp
      · rw [pow_succ', ← Matrix.mulVec_mulVec,
          exactGramCompanionMatrix_pow_mulVec c n (Nat.lt_succ_self n)]
        have hlast : (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1)) = Fin.last n := Fin.ext rfl
        rw [hlast, Matrix.one_mulVec]
        exact exactGramCompanionMatrix_mulVec_last c

end HierarchicalAbsoluteSpectral
