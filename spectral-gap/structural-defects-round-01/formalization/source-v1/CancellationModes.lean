import ProjectedResolvent
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring

namespace StructuralDefects

open Matrix GrowingDefects

noncomputable section

def cancellationMatrix {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (c : Fin m ↪ Fin n) (d : ℝ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  Matrix.fromBlocks A ((d • 1 - A) * selectionMatrix c)
    ((selectionMatrix c).transpose * (d • 1 - A)) 0

def compactFamily {n m : ℕ} (c : Fin m ↪ Fin n) (t : Fin m → ℝ) :
    Fin n ⊕ Fin m → ℝ := Sum.elim (selectionMatrix c *ᵥ t) t

theorem cancellationMatrix_symmetric {n m : ℕ} (c : Fin m ↪ Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) (d : ℝ) (hA : A.transpose = A) :
    (cancellationMatrix A c d).transpose = cancellationMatrix A c d := by
  simp only [cancellationMatrix, Matrix.fromBlocks_transpose, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.transpose_zero, hA]

theorem independent_mark_compression {n m : ℕ} (c : Fin m ↪ Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hind : ∀ i j, A (c i) (c j) = 0) :
    (selectionMatrix c).transpose * A * selectionMatrix c = 0 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.transpose_apply, selectionMatrix,
    ite_mul, mul_ite, hind]

theorem selected_cancellation_compression {n m : ℕ} (c : Fin m ↪ Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) (d : ℝ)
    (hind : ∀ i j, A (c i) (c j) = 0) :
    (selectionMatrix c).transpose * (d • 1 - A) * selectionMatrix c = d • 1 := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, selection_isometry, independent_mark_compression c A hind, sub_zero]

theorem compactFamily_eigen_equation {n m : ℕ} (c : Fin m ↪ Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) (d : ℝ)
    (hind : ∀ i j, A (c i) (c j) = 0) (t : Fin m → ℝ) :
    cancellationMatrix A c d *ᵥ compactFamily c t = d • compactFamily c t := by
  have hlow : ((selectionMatrix c).transpose * (d • 1 - A)) *ᵥ
      (selectionMatrix c *ᵥ t) = d • t := by
    rw [Matrix.mulVec_mulVec, selected_cancellation_compression c A d hind,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [cancellationMatrix, compactFamily, Matrix.fromBlocks_mulVec,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero, hlow]
  funext i
  cases i with
  | inl i =>
    simp only [Sum.elim_inl, Pi.smul_apply, ← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply,
      Pi.sub_apply, smul_eq_mul]
    ring
  | inr i => rfl

theorem compactFamily_injective {n m : ℕ} (c : Fin m ↪ Fin n) :
    Function.Injective (compactFamily c) := by
  intro t v h
  funext j
  exact congrFun h (Sum.inr j)

theorem compactFamily_hasEigenvector {n m : ℕ} (c : Fin m ↪ Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) (d : ℝ)
    (hind : ∀ i j, A (c i) (c j) = 0) (t : Fin m → ℝ) (ht : t ≠ 0) :
    Module.End.HasEigenvector (cancellationMatrix A c d).mulVecLin d (compactFamily c t) := by
  refine ⟨Module.End.mem_eigenspace_iff.mpr (compactFamily_eigen_equation c A d hind t), ?_⟩
  intro h
  apply ht
  funext j
  exact congrFun h (Sum.inr j)

theorem compact_single_coordinates {n m : ℕ} (c : Fin m ↪ Fin n) (j : Fin m) :
    compactFamily c (Pi.single j 1) =
      Sum.elim (Pi.single (c j) 1) (Pi.single j 1) := by
  funext i
  cases i with
  | inl i => simp [compactFamily, selectionMatrix, Pi.single_apply]
  | inr i => rfl

theorem stationary_cancellation_eigen {n m : ℕ} (c : Fin m ↪ Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) (d : ℝ) (u : Fin n → ℝ)
    (hu : A *ᵥ u = d • u) :
    cancellationMatrix A c d *ᵥ Sum.elim u 0 = d • Sum.elim u 0 := by
  have hc : (d • (1 : Matrix (Fin n) (Fin n) ℝ) - A) *ᵥ u = 0 := by
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, hu]
  rw [cancellationMatrix, Matrix.fromBlocks_mulVec]
  change Sum.elim (A *ᵥ u + ((d • 1 - A) * selectionMatrix c) *ᵥ 0)
    (((selectionMatrix c).transpose * (d • 1 - A)) *ᵥ u + 0 *ᵥ 0) = _
  simp only [Matrix.mulVec_zero, add_zero,
    ← Matrix.mulVec_mulVec, hc, hu]
  funext i
  cases i with
  | inl i => rfl
  | inr i => simp

def cancellationLift {n m : ℕ} (c : Fin m ↪ Fin n) (u : Fin n → ℝ) :
    ℝ × (Fin m → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin m → ℝ) where
  toFun x := Sum.elim (x.1 • u + selectionMatrix c *ᵥ x.2) x.2
  map_add' x y := by
    funext i
    cases i with
    | inl i => simp [Matrix.mulVec_add, add_smul, add_assoc, add_comm, add_left_comm]
    | inr i => rfl
  map_smul' r x := by
    funext i
    cases i with
    | inl i => simp [Matrix.mulVec_smul, mul_add, mul_assoc]
    | inr i => rfl

theorem cancellationLift_injective {n m : ℕ} (c : Fin m ↪ Fin n) (u : Fin n → ℝ)
    (hu : u ≠ 0) : Function.Injective (cancellationLift c u) := by
  intro x y h
  have ht : x.2 = y.2 := by
    funext j
    exact congrFun h (Sum.inr j)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  have hh := congrFun h (Sum.inl i)
  change x.1 * u i + (selectionMatrix c *ᵥ x.2) i =
    y.1 * u i + (selectionMatrix c *ᵥ y.2) i at hh
  rw [ht] at hh
  have ha : x.1 = y.1 := mul_right_cancel₀ hi (add_right_cancel hh)
  exact Prod.ext ha ht

theorem cancellationLift_eigen_equation {n m : ℕ} (c : Fin m ↪ Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) (d : ℝ) (u : Fin n → ℝ)
    (hu : A *ᵥ u = d • u) (hind : ∀ i j, A (c i) (c j) = 0)
    (x : ℝ × (Fin m → ℝ)) :
    cancellationMatrix A c d *ᵥ cancellationLift c u x = d • cancellationLift c u x := by
  have hsplit : cancellationLift c u x = x.1 • Sum.elim u 0 + compactFamily c x.2 := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => simp [cancellationLift, compactFamily]
  rw [hsplit, Matrix.mulVec_add, Matrix.mulVec_smul,
    stationary_cancellation_eigen c A d u hu, compactFamily_eigen_equation c A d hind]
  module

theorem cancellation_eigenspace_dimension {n m : ℕ} (c : Fin m ↪ Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) (d : ℝ) (u : Fin n → ℝ)
    (hu : A *ᵥ u = d • u) (hne : u ≠ 0)
    (hind : ∀ i j, A (c i) (c j) = 0) :
    m + 1 ≤ Module.finrank ℝ (Module.End.eigenspace (cancellationMatrix A c d).mulVecLin d) := by
  let f : ℝ × (Fin m → ℝ) →ₗ[ℝ]
      Module.End.eigenspace (cancellationMatrix A c d).mulVecLin d :=
    (cancellationLift c u).codRestrict _ (fun x => Module.End.mem_eigenspace_iff.mpr
      (cancellationLift_eigen_equation c A d u hu hind x))
  have hf : Function.Injective f := by
    intro x y h
    apply cancellationLift_injective c u hne
    exact congrArg Subtype.val h
  have h := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Nat.add_comm] using h

#print axioms cancellationMatrix_symmetric
#print axioms independent_mark_compression
#print axioms selected_cancellation_compression
#print axioms compactFamily_eigen_equation
#print axioms compactFamily_injective
#print axioms compactFamily_hasEigenvector
#print axioms compact_single_coordinates
#print axioms stationary_cancellation_eigen
#print axioms cancellationLift_injective
#print axioms cancellationLift_eigen_equation
#print axioms cancellation_eigenspace_dimension

end

end StructuralDefects
