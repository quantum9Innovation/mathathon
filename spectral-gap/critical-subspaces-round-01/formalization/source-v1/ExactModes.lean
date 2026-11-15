import CouplingError

open Matrix CriticalPairs
open scoped BigOperators

namespace CriticalSubspaces

noncomputable section

def hostVector (q p : ℕ) : Option (Fin q) ⊕ (Fin p × Bool) → ℝ :=
  Pi.single (Sum.inl none) 1

theorem coupled_host (q p : ℕ) (b : ℝ) (w : Fin p → ℝ)
    (v : Option (Fin q) ⊕ (Fin p × Bool) → ℝ) :
    (coupled q p b w *ᵥ v) (Sum.inl none) =
      b * (∑ i : Fin q, v (Sum.inl (some i))) +
      b * ∑ i : Fin p × Bool, v (Sum.inr i) := by
  simp [coupled, decoupled, Matrix.add_mulVec, Matrix.fromBlocks_mulVec,
    freeStar_host, removedCoupling_host, Function.comp_def]

theorem coupled_free (q p : ℕ) (b : ℝ) (w : Fin p → ℝ)
    (v : Option (Fin q) ⊕ (Fin p × Bool) → ℝ) (i : Fin q) :
    (coupled q p b w *ᵥ v) (Sum.inl (some i)) = b * v (Sum.inl none) := by
  simp [coupled, decoupled, Matrix.add_mulVec, Matrix.fromBlocks_mulVec,
    freeStar_leaf, removedCoupling_free, Function.comp_def]

theorem coupled_pair (q p : ℕ) (b : ℝ) (w : Fin p → ℝ)
    (v : Option (Fin q) ⊕ (Fin p × Bool) → ℝ) (k : Fin p) (s : Bool) :
    (coupled q p b w *ᵥ v) (Sum.inr (k, s)) =
      w k * v (Sum.inr (k, !s)) + b * v (Sum.inl none) := by
  simp [coupled, decoupled, Matrix.add_mulVec, Matrix.fromBlocks_mulVec,
    pairMatrix_action, removedCoupling_pair, Function.comp_def]

theorem removedCoupling_pairVector (q p : ℕ) (b : ℝ) (k : Fin p) (σ : ℝ) :
    removedCoupling q p b *ᵥ embeddedPair q p k σ =
      (b * (1 + σ)) • hostVector q p := by
  funext i
  cases i with
  | inl i =>
    cases i with
    | none =>
      simp [removedCoupling_host, embeddedPair, pairVector, hostVector,
        Fintype.sum_prod_type, add_comm]
    | some i => simp [removedCoupling_free, hostVector]
  | inr i => simp [removedCoupling_pair, embeddedPair, hostVector]

theorem coupled_pairVector_action (q p : ℕ) (b : ℝ) (w : Fin p → ℝ)
    (k : Fin p) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    coupled q p b w *ᵥ embeddedPair q p k σ =
      (σ * w k) • embeddedPair q p k σ + (b * (1 + σ)) • hostVector q p := by
  rw [coupled, Matrix.add_mulVec, decoupled_pair_eigen q p b w k σ hσ,
    removedCoupling_pairVector]

theorem antisymmetric_pair_hasEigenvector (q p : ℕ) (b : ℝ) (w : Fin p → ℝ)
    (k : Fin p) :
    Module.End.HasEigenvector (coupled q p b w).mulVecLin (-w k)
      (embeddedPair q p k (-1)) := by
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · simpa using coupled_pairVector_action q p b w k (-1) (by norm_num)
  · exact (decoupled_pair_hasEigenvector q p b w k (-1) (by norm_num)).2

def symmetricDifference (q p : ℕ) (i j : Fin p) :
    Option (Fin q) ⊕ (Fin p × Bool) → ℝ :=
  embeddedPair q p i 1 - embeddedPair q p j 1

theorem symmetricDifference_hasEigenvector (q p : ℕ) (b : ℝ) (w : Fin p → ℝ)
    (i j : Fin p) (hij : i ≠ j) (hw : w i = w j) :
    Module.End.HasEigenvector (coupled q p b w).mulVecLin (w i)
      (symmetricDifference q p i j) := by
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · change coupled q p b w *ᵥ symmetricDifference q p i j =
      w i • symmetricDifference q p i j
    rw [symmetricDifference, Matrix.mulVec_sub,
      coupled_pairVector_action q p b w i 1 (by norm_num),
      coupled_pairVector_action q p b w j 1 (by norm_num), ← hw]
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    ring
  · intro h
    have h0 := congrFun h (Sum.inr (i, false))
    simp [symmetricDifference, embeddedPair, pairVector, hij] at h0

theorem symmetricDifference_zero_host (q p : ℕ) (i j : Fin p) :
    symmetricDifference q p i j (Sum.inl none) = 0 := by
  simp [symmetricDifference, embeddedPair]

def symmetricProfile (q p : ℕ) (a : Fin p → ℝ) :
    Option (Fin q) ⊕ (Fin p × Bool) → ℝ :=
  Sum.elim 0 (fun i => a i.1)

theorem symmetricProfile_dark (q p : ℕ) (b w : ℝ) (a : Fin p → ℝ)
    (ha : ∑ i, a i = 0) :
    coupled q p b (fun _ => w) *ᵥ symmetricProfile q p a =
      w • symmetricProfile q p a := by
  funext i
  cases i with
  | inl i =>
    cases i with
    | none =>
      simp [coupled_host, symmetricProfile, Fintype.sum_prod_type,
        ← Finset.mul_sum, ha]
    | some i => simp [coupled_free, symmetricProfile]
  | inr i =>
    rcases i with ⟨k, s⟩
    simp [coupled_pair, symmetricProfile]

#print axioms coupled_host
#print axioms coupled_free
#print axioms coupled_pair
#print axioms removedCoupling_pairVector
#print axioms coupled_pairVector_action
#print axioms antisymmetric_pair_hasEigenvector
#print axioms symmetricDifference_hasEigenvector
#print axioms symmetricDifference_zero_host
#print axioms symmetricProfile_dark

end

end CriticalSubspaces
