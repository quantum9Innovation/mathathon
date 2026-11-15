import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Matrix
open scoped BigOperators

namespace CriticalPairs

noncomputable section

def pairMatrix (p : ℕ) (w : Fin p → ℝ) : Matrix (Fin p × Bool) (Fin p × Bool) ℝ :=
  fun i j => if i.1 = j.1 then if i.2 = j.2 then 0 else w i.1 else 0

theorem pairMatrix_action (p : ℕ) (w : Fin p → ℝ) (v : Fin p × Bool → ℝ)
    (k : Fin p) (s : Bool) :
    (pairMatrix p w *ᵥ v) (k, s) = w k * v (k, !s) := by
  cases s with
  | false => simp [Matrix.mulVec, dotProduct, pairMatrix, Fintype.sum_prod_type]
  | true => simp [Matrix.mulVec, dotProduct, pairMatrix, Fintype.sum_prod_type]

def pairVector (p : ℕ) (k : Fin p) (σ : ℝ) : Fin p × Bool → ℝ :=
  fun i => if i.1 = k then if i.2 then σ else 1 else 0

theorem pairVector_eigen (p : ℕ) (w : Fin p → ℝ) (k : Fin p) (σ : ℝ)
    (hσ : σ ^ 2 = 1) :
    pairMatrix p w *ᵥ pairVector p k σ = (σ * w k) • pairVector p k σ := by
  funext i
  rcases i with ⟨j, s⟩
  rw [pairMatrix_action]
  by_cases hj : j = k
  · subst j
    cases s with
    | false => simp [pairVector, mul_comm]
    | true =>
      simp [pairVector]
      calc
        w k = w k * σ ^ 2 := by rw [hσ, mul_one]
        _ = σ * w k * σ := by ring
  · cases s with
    | false => simp [pairVector, hj]
    | true => simp [pairVector, hj]

theorem pairVector_nonzero (p : ℕ) (k : Fin p) (σ : ℝ) :
    pairVector p k σ ≠ 0 := by
  intro h
  have h0 := congrFun h (k, false)
  simp [pairVector] at h0

def freeStar (q : ℕ) (b : ℝ) : Matrix (Option (Fin q)) (Option (Fin q)) ℝ :=
  fun i j => match i, j with
    | none, some _ => b
    | some _, none => b
    | _, _ => 0

theorem freeStar_host (q : ℕ) (b : ℝ) (v : Option (Fin q) → ℝ) :
    (freeStar q b *ᵥ v) none = b * ∑ j : Fin q, v (some j) := by
  simp [Matrix.mulVec, dotProduct, freeStar, Finset.mul_sum]

theorem freeStar_leaf (q : ℕ) (b : ℝ) (v : Option (Fin q) → ℝ) (i : Fin q) :
    (freeStar q b *ᵥ v) (some i) = b * v none := by
  simp [Matrix.mulVec, dotProduct, freeStar]

def freeBright (q : ℕ) (t : ℝ) : Option (Fin q) → ℝ
  | none => t
  | some _ => 1

theorem freeBright_eigen (q : ℕ) (b t : ℝ) (ht : t ^ 2 = (q : ℝ)) :
    freeStar q b *ᵥ freeBright q t = (b * t) • freeBright q t := by
  funext i
  cases i with
  | none =>
    simp [Matrix.mulVec, dotProduct, freeStar, freeBright]
    rw [← ht]
    ring
  | some i => simp [Matrix.mulVec, dotProduct, freeStar, freeBright]

def decoupled (q p : ℕ) (b : ℝ) (w : Fin p → ℝ) :
    Matrix (Option (Fin q) ⊕ (Fin p × Bool)) (Option (Fin q) ⊕ (Fin p × Bool)) ℝ :=
  Matrix.fromBlocks (freeStar q b) 0 0 (pairMatrix p w)

def embeddedPair (q p : ℕ) (k : Fin p) (σ : ℝ) :
    Option (Fin q) ⊕ (Fin p × Bool) → ℝ :=
  Sum.elim 0 (pairVector p k σ)

def embeddedBright (q p : ℕ) (t : ℝ) :
    Option (Fin q) ⊕ (Fin p × Bool) → ℝ :=
  Sum.elim (freeBright q t) 0

theorem decoupled_pair_eigen (q p : ℕ) (b : ℝ) (w : Fin p → ℝ)
    (k : Fin p) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    decoupled q p b w *ᵥ embeddedPair q p k σ =
      (σ * w k) • embeddedPair q p k σ := by
  rw [decoupled, embeddedPair, Matrix.fromBlocks_mulVec]
  funext i
  cases i with
  | inl i => simp [Function.comp_def, Matrix.mulVec, dotProduct]
  | inr i => simpa [Function.comp_def] using congrFun (pairVector_eigen p w k σ hσ) i

theorem decoupled_pair_hasEigenvector (q p : ℕ) (b : ℝ) (w : Fin p → ℝ)
    (k : Fin p) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    Module.End.HasEigenvector (decoupled q p b w).mulVecLin (σ * w k)
      (embeddedPair q p k σ) := by
  refine ⟨Module.End.mem_eigenspace_iff.mpr (decoupled_pair_eigen q p b w k σ hσ), ?_⟩
  intro h
  have h0 := congrFun h (Sum.inr (k, false))
  simp [embeddedPair, pairVector] at h0

theorem decoupled_bright_eigen (q p : ℕ) (b : ℝ) (w : Fin p → ℝ)
    (t : ℝ) (ht : t ^ 2 = (q : ℝ)) :
    decoupled q p b w *ᵥ embeddedBright q p t =
      (b * t) • embeddedBright q p t := by
  rw [decoupled, embeddedBright, Matrix.fromBlocks_mulVec]
  funext i
  cases i with
  | inl i => simpa [Function.comp_def] using congrFun (freeBright_eigen q b t ht) i
  | inr i => simp [Function.comp_def, Matrix.mulVec, dotProduct]

theorem decoupled_bright_hasEigenvector (q p : ℕ) (hq : 0 < q)
    (b : ℝ) (w : Fin p → ℝ) (t : ℝ) (ht : t ^ 2 = (q : ℝ)) :
    Module.End.HasEigenvector (decoupled q p b w).mulVecLin (b * t)
      (embeddedBright q p t) := by
  refine ⟨Module.End.mem_eigenspace_iff.mpr (decoupled_bright_eigen q p b w t ht), ?_⟩
  intro h
  have h0 := congrFun h (Sum.inl (some ⟨0, hq⟩))
  simp [embeddedBright, freeBright] at h0

theorem pair_eigenvalue_coverage (p : ℕ) (w : Fin p → ℝ) (μ : ℝ)
    (v : Fin p × Bool → ℝ) (hv : v ≠ 0)
    (he : pairMatrix p w *ᵥ v = μ • v) :
    ∃ k : Fin p, μ = w k ∨ μ = -w k := by
  obtain ⟨⟨k, s⟩, hi⟩ := Function.ne_iff.mp hv
  have h1 := congrFun he (k, s)
  have h2 := congrFun he (k, !s)
  simp only [pairMatrix_action, Pi.smul_apply, smul_eq_mul, Bool.not_not] at h1 h2
  have hpoly : (μ ^ 2 - (w k) ^ 2) * v (k, s) = 0 := by
    nlinarith [congrArg (fun x : ℝ => μ * x) h1,
      congrArg (fun x : ℝ => w k * x) h2]
  have hz : μ ^ 2 - (w k) ^ 2 = 0 := (mul_eq_zero.mp hpoly).resolve_right hi
  exact ⟨k, sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp hz)⟩

theorem freeStar_nonzero_eigenvalue_square (q : ℕ) (b μ : ℝ) (hμ : μ ≠ 0)
    (v : Option (Fin q) → ℝ) (hv : v ≠ 0)
    (he : freeStar q b *ᵥ v = μ • v) :
    μ ^ 2 = (q : ℝ) * b ^ 2 := by
  have hnone := congrFun he none
  simp only [freeStar_host, Pi.smul_apply, smul_eq_mul] at hnone
  have hsome (i : Fin q) : b * v none = μ * v (some i) := by
    have h := congrFun he (some i)
    simpa only [freeStar_leaf, Pi.smul_apply, smul_eq_mul] using h
  have hx : v none ≠ 0 := by
    intro h0
    apply hv
    funext i
    cases i with
    | none => exact h0
    | some i =>
      have h := hsome i
      rw [h0, mul_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hμ
  have hsum := congrArg (fun f : Fin q → ℝ => ∑ i, f i) (funext hsome)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hpoly : (μ ^ 2 - (q : ℝ) * b ^ 2) * v none = 0 := by
    nlinarith [congrArg (fun x : ℝ => b * x) hsum,
      congrArg (fun x : ℝ => μ * x) hnone]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hpoly).resolve_right hx)

theorem decoupled_eigenvalue_coverage (q p : ℕ) (b μ : ℝ) (w : Fin p → ℝ)
    (he : Module.End.HasEigenvalue (decoupled q p b w).mulVecLin μ) :
    μ = 0 ∨ μ = b * Real.sqrt q ∨ μ = -(b * Real.sqrt q) ∨
      ∃ k : Fin p, μ = w k ∨ μ = -w k := by
  by_cases hμ : μ = 0
  · exact Or.inl hμ
  · obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have heq := hv.apply_eq_smul
    change decoupled q p b w *ᵥ v = μ • v at heq
    have hleft : freeStar q b *ᵥ (v ∘ Sum.inl) = μ • (v ∘ Sum.inl) := by
      funext i
      have h := congrFun heq (Sum.inl i)
      simpa [decoupled, Matrix.fromBlocks_mulVec] using h
    have hright : pairMatrix p w *ᵥ (v ∘ Sum.inr) = μ • (v ∘ Sum.inr) := by
      funext i
      have h := congrFun heq (Sum.inr i)
      simpa [decoupled, Matrix.fromBlocks_mulVec] using h
    by_cases hleft0 : v ∘ Sum.inl = 0
    · have hright0 : v ∘ Sum.inr ≠ 0 := by
        intro hr
        apply hv.2
        funext i
        cases i with
        | inl i => exact congrFun hleft0 i
        | inr i => exact congrFun hr i
      exact Or.inr (Or.inr (Or.inr (pair_eigenvalue_coverage p w μ _ hright0 hright)))
    · have hs := freeStar_nonzero_eigenvalue_square q b μ hμ _ hleft0 hleft
      have hsq : μ ^ 2 = (b * Real.sqrt q) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
        simpa [mul_comm] using hs
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hp | hn
      · exact Or.inr (Or.inl hp)
      · exact Or.inr (Or.inr (Or.inl hn))

#print axioms freeStar_host
#print axioms freeStar_leaf
#print axioms pair_eigenvalue_coverage
#print axioms freeStar_nonzero_eigenvalue_square
#print axioms decoupled_eigenvalue_coverage
#print axioms pairMatrix_action
#print axioms pairVector_eigen
#print axioms pairVector_nonzero
#print axioms freeBright_eigen
#print axioms decoupled_pair_eigen
#print axioms decoupled_pair_hasEigenvector
#print axioms decoupled_bright_eigen
#print axioms decoupled_bright_hasEigenvector

end

end CriticalPairs
