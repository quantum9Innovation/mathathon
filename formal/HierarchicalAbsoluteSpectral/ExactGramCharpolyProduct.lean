import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! Dense coefficient arrays and their polynomial meaning. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Polynomial
open scoped BigOperators

abbrev ExactGramDensePolynomial (d : ℕ) (R : Type*) := Fin (d+1) → R

def exactGramDenseCast {R : Type*} {d e : ℕ} (h : d = e)
    (a : ExactGramDensePolynomial d R) : ExactGramDensePolynomial e R :=
  fun i => a (Fin.cast (congrArg (fun k => k+1) h.symm) i)

def exactGramDenseToPolynomial {R : Type*} [CommSemiring R] {d : ℕ}
    (a : ExactGramDensePolynomial d R) : R[X] :=
  ∑ i : Fin (d+1), monomial i.val (a i)

@[simp] theorem exactGramDenseToPolynomial_cast {R : Type*} [CommSemiring R] {d e : ℕ}
    (h : d = e) (a : ExactGramDensePolynomial d R) :
    exactGramDenseToPolynomial (exactGramDenseCast h a) = exactGramDenseToPolynomial a := by
  subst e
  rfl

@[simp] theorem exactGramDenseToPolynomial_zero {R : Type*} [CommSemiring R] (d : ℕ) :
    exactGramDenseToPolynomial (0 : ExactGramDensePolynomial d R) = 0 := by
  simp [exactGramDenseToPolynomial]

@[simp] theorem exactGramDenseToPolynomial_add {R : Type*} [CommSemiring R] {d : ℕ}
    (a b : ExactGramDensePolynomial d R) :
    exactGramDenseToPolynomial (a+b) = exactGramDenseToPolynomial a + exactGramDenseToPolynomial b := by
  simp only [exactGramDenseToPolynomial, Pi.add_apply, map_add, Finset.sum_add_distrib]

@[simp] theorem exactGramDenseToPolynomial_single {R : Type*} [CommSemiring R] {d : ℕ}
    (i : Fin (d+1)) (x : R) :
    exactGramDenseToPolynomial (Pi.single i x) = monomial i.val x := by
  classical
  simp [exactGramDenseToPolynomial, Pi.single_apply, apply_ite]

theorem exactGramDenseToPolynomial_update {R : Type*} [CommSemiring R] {d : ℕ}
    (a : ExactGramDensePolynomial d R) (i : Fin (d+1)) (x : R) :
    exactGramDenseToPolynomial (Function.update a i (a i+x)) =
      exactGramDenseToPolynomial a + monomial i.val x := by
  classical
  have h : Function.update a i (a i+x) = a + Pi.single i x := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hj, Pi.single_apply, hj]
  rw [h, exactGramDenseToPolynomial_add, exactGramDenseToPolynomial_single]

@[simp] theorem exactGramDenseToPolynomial_one :
    exactGramDenseToPolynomial (fun _ : Fin 1 => (1 : ℝ)) = 1 := by
  simp [exactGramDenseToPolynomial]

def exactGramConvolutionPairs (d e : ℕ) : List (Fin (d+1) × Fin (e+1)) :=
  (List.ofFn (fun i : Fin (d+1) => List.ofFn (fun j : Fin (e+1) => (i,j)))).flatten

@[simp] theorem exactGramConvolutionPairs_length (d e : ℕ) :
    (exactGramConvolutionPairs d e).length = (d+1)*(e+1) := by
  simp [exactGramConvolutionPairs, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  <;> ring

def exactGramConvolutionIndex {d e : ℕ} (ij : Fin (d+1) × Fin (e+1)) : Fin (d+e+1) :=
  ⟨ij.1.val + ij.2.val, by have hi := ij.1.isLt; have hj := ij.2.isLt; omega⟩

theorem exactGramConvolutionPairs_sum {R : Type*} [CommSemiring R] {d e : ℕ}
    (a : ExactGramDensePolynomial d R) (b : ExactGramDensePolynomial e R) :
    ((exactGramConvolutionPairs d e).map
      (fun ij => monomial (ij.1.val+ij.2.val) (a ij.1*b ij.2))).sum =
      exactGramDenseToPolynomial a * exactGramDenseToPolynomial b := by
  simp only [exactGramConvolutionPairs, List.map_flatten, List.map_ofFn, List.map_map,
    List.sum_flatten, List.sum_ofFn, Function.comp_def]
  unfold exactGramDenseToPolynomial
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, monomial_mul_monomial]

end
end HierarchicalAbsoluteSpectral
