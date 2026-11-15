import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic
import HierarchicalAbsoluteSpectral.MassSpectrum

/-!
Elementary symmetric coefficients used by the exact-Gram initializer.
The spectral list in this file is an analytical object: the initializer
will read the coefficients of a computed characteristic polynomial.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators

def exactGramElementary {k : ℕ} (v : Fin k → ℝ) (j : ℕ) : ℝ :=
  ((List.ofFn v : List ℝ) : Multiset ℝ).esymm j

@[simp] theorem exactGramElementary_zero {k : ℕ} (v : Fin k → ℝ) :
    exactGramElementary v 0 = 1 := by
  simp [exactGramElementary, Multiset.esymm]

@[simp] theorem exactGramElementary_empty (v : Fin 0 → ℝ) (j : ℕ) :
    exactGramElementary v (j+1) = 0 := by
  simp [exactGramElementary, Multiset.esymm]

theorem exactGramElementary_succ {k : ℕ} (v : Fin (k+1) → ℝ) (j : ℕ) :
    exactGramElementary v (j+1) =
      v 0 * exactGramElementary (fun i => v i.succ) j +
        exactGramElementary (fun i => v i.succ) (j+1) := by
  simp only [exactGramElementary, List.ofFn_succ]
  change (v 0 ::ₘ ((List.ofFn (fun i => v i.succ) : List ℝ) : Multiset ℝ)).esymm
    (j+1) = _
  simp only [
    Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add,
    Multiset.sum_add, Multiset.map_map, Function.comp_def, Multiset.prod_cons]
  rw [Multiset.sum_map_mul_left]
  exact add_comm _ _

theorem exactGramElementary_nonneg {k : ℕ} (v : Fin k → ℝ)
    (hv : ∀ i, 0 ≤ v i) (j : ℕ) : 0 ≤ exactGramElementary v j := by
  induction k generalizing j with
  | zero => cases j <;> simp
  | succ k ih =>
      cases j with
      | zero => simp
      | succ j =>
          rw [exactGramElementary_succ]
          exact add_nonneg (mul_nonneg (hv _) (ih _ (fun i => hv _) _))
            (ih _ (fun i => hv _) _)

theorem exactGramElementary_eq_zero_of_lt {k : ℕ} (v : Fin k → ℝ) (j : ℕ)
    (hj : k < j) : exactGramElementary v j = 0 := by
  induction k generalizing j with
  | zero => cases j <;> simp_all
  | succ k ih =>
      rcases j with _ | j
      · omega
      · rw [exactGramElementary_succ, ih _ _ (by omega), ih _ _ (by omega)]
        simp

@[simp] theorem exactGramElementary_one {k : ℕ} (v : Fin k → ℝ) :
    exactGramElementary v 1 = ∑ i, v i := by
  simp [exactGramElementary, Multiset.esymm, Multiset.powersetCard_one,
    List.sum_ofFn]

/-- The lower coefficient bound is valid with vanishing and repeated entries.
The index is zero based, so this is `v_j e_(j-1) ≤ j e_j` in paper notation. -/
theorem exactGramElementary_lower_mul {k : ℕ} (v : Fin k → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hsort : Antitone v) (j : Fin k) :
    v j * exactGramElementary v j.val ≤
      ((j.val+1 : ℕ) : ℝ) * exactGramElementary v (j.val+1) := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.val_zero, zero_add, Nat.cast_one, one_mul, exactGramElementary_zero]
        rw [exactGramElementary_succ]
        simp only [exactGramElementary_zero, mul_one]
        exact le_add_of_nonneg_right (exactGramElementary_nonneg _ (fun i => hv i.succ) 1)
      · let w : Fin k → ℝ := fun i => v i.succ
        have hw : ∀ i, 0 ≤ w i := fun i => hv i.succ
        have hsortw : Antitone w := fun i j hij => hsort (Fin.succ_le_succ_iff.mpr hij)
        have hrec := ih w hw hsortw i
        have hhead : w i ≤ v 0 := hsort (Fin.zero_le _)
        have hfirst := mul_le_mul_of_nonneg_left hrec (hv 0)
        have hsecond := mul_le_mul_of_nonneg_right hhead
          (exactGramElementary_nonneg w hw (i.val+1))
        have hrest := exactGramElementary_nonneg w hw (i.val+2)
        simp only [Fin.val_succ]
        rw [exactGramElementary_succ v i.val, exactGramElementary_succ v (i.val+1)]
        change w i * (v 0 * exactGramElementary w i.val + exactGramElementary w (i.val+1)) ≤
          ((i.val+1+1 : ℕ) : ℝ) *
            (v 0 * exactGramElementary w (i.val+1) + exactGramElementary w (i.val+2))
        push_cast at hfirst ⊢
        nlinarith

/-- The sharp upper coefficient bound. No strict ordering is required. -/
theorem exactGramElementary_upper_mul {k : ℕ} (v : Fin k → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hsort : Antitone v) (j : Fin k) :
    exactGramElementary v (j.val+1) ≤
      ((k-j.val : ℕ) : ℝ) * v j * exactGramElementary v j.val := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.val_zero, zero_add, Nat.sub_zero, exactGramElementary_zero, mul_one,
          exactGramElementary_one]
        calc
          (∑ i, v i) ≤ ∑ _ : Fin (k+1), v 0 :=
            Finset.sum_le_sum (fun i _ => hsort (Fin.zero_le i))
          _ = ((k+1 : ℕ) : ℝ) * v 0 := by simp
      · let w : Fin k → ℝ := fun i => v i.succ
        have hw : ∀ i, 0 ≤ w i := fun i => hv i.succ
        have hsortw : Antitone w := fun i j hij => hsort (Fin.succ_le_succ_iff.mpr hij)
        have hrec := ih w hw hsortw i
        have htail : exactGramElementary w (i.val+2) ≤
            ((k-i.val : ℕ) : ℝ) * w i * exactGramElementary w (i.val+1) := by
          by_cases hi : i.val+1 < k
          · let next : Fin k := ⟨i.val+1, hi⟩
            have hnext := ih w hw hsortw next
            have hcoef : ((k-(i.val+1) : ℕ) : ℝ) ≤ ((k-i.val : ℕ) : ℝ) := by
              exact_mod_cast Nat.sub_le_sub_left (by omega : i.val ≤ i.val+1) k
            have hval : w next ≤ w i := hsortw (show i.val ≤ next.val from Nat.le_succ _)
            exact hnext.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul hcoef hval (hw _) (by positivity))
              (exactGramElementary_nonneg w hw (i.val+1)))
          · rw [exactGramElementary_eq_zero_of_lt w (i.val+2) (by omega)]
            exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw _))
              (exactGramElementary_nonneg w hw _)
        have hfirst := mul_le_mul_of_nonneg_left hrec (hv 0)
        simp only [Fin.val_succ, Nat.add_sub_add_right]
        rw [exactGramElementary_succ v (i.val+1), exactGramElementary_succ v i.val]
        change v 0 * exactGramElementary w (i.val+1) + exactGramElementary w (i.val+2) ≤
          ((k-i.val : ℕ) : ℝ) * w i *
            (v 0 * exactGramElementary w i.val + exactGramElementary w (i.val+1))
        nlinarith

theorem exactGramElementary_pos {k : ℕ} (v : Fin k → ℝ)
    (hv : ∀ i, 0 ≤ v i) (j : ℕ) (hj : j ≤ k)
    (hpos : ∀ i : Fin k, i.val < j → 0 < v i) : 0 < exactGramElementary v j := by
  induction k generalizing j with
  | zero =>
      have hjzero : j = 0 := by omega
      subst j
      simp
  | succ k ih =>
      cases j with
      | zero => simp
      | succ j =>
          rw [exactGramElementary_succ]
          have hhead : 0 < v 0 := hpos 0 (by simp)
          have htail := ih (fun i => v i.succ) (fun i => hv i.succ) j (by omega)
            (fun i hi => hpos i.succ (by simpa using Nat.succ_lt_succ hi))
          exact add_pos_of_pos_of_nonneg (mul_pos hhead htail)
            (exactGramElementary_nonneg _ (fun i => hv i.succ) _)

/-- The manuscript's coefficient-ratio inequalities, with its one-based
index translated to `j.val+1`. Positivity of the target alone suffices. -/
theorem exactGramElementary_ratio {k : ℕ} (v : Fin k → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hsort : Antitone v) (j : Fin k) (hj : 0 < v j) :
    0 < exactGramElementary v j.val ∧
      v j / ((j.val+1 : ℕ) : ℝ) ≤
        exactGramElementary v (j.val+1) / exactGramElementary v j.val ∧
      exactGramElementary v (j.val+1) / exactGramElementary v j.val ≤
        ((k-j.val : ℕ) : ℝ) * v j := by
  have he : 0 < exactGramElementary v j.val :=
    exactGramElementary_pos v hv j.val (Nat.le_of_lt j.isLt)
      (fun i hi => hj.trans_le (hsort (by exact le_of_lt hi)))
  have hindex : (0:ℝ) < ((j.val+1 : ℕ) : ℝ) := by positivity
  refine ⟨he, ?_, ?_⟩
  · rw [div_le_div_iff₀ hindex he]
    simpa only [mul_comm] using exactGramElementary_lower_mul v hv hsort j
  · rw [div_le_iff₀ he]
    exact exactGramElementary_upper_mul v hv hsort j

/-- The coefficient read by the initializer. The sign is a known constant
depending on the index, so this uses one scalar multiplication. -/
def exactGramSignedCoeff (p : Polynomial ℝ) (k j : ℕ) : ℝ :=
  (-1 : ℝ)^j * p.coeff (k-j)

theorem exactGramSignedCoeff_prod {k : ℕ} (v : Fin k → ℝ) (j : ℕ) (hj : j ≤ k) :
    exactGramSignedCoeff (∏ i, (Polynomial.X - Polynomial.C (v i))) k j =
      exactGramElementary v j := by
  have h := Multiset.prod_X_sub_C_coeff
    (((List.ofFn v : List ℝ) : Multiset ℝ)) (k := k-j) (by simp)
  simp only [Multiset.map_coe, List.map_ofFn, Multiset.prod_coe, List.prod_ofFn,
    Multiset.coe_card, List.length_ofFn, Nat.sub_sub_self hj, Function.comp_def] at h
  simp only [exactGramSignedCoeff, h, ← mul_assoc, ← pow_add,
    show j+j = 2*j by omega, pow_mul, neg_one_sq, one_pow, one_mul,
    exactGramElementary]

theorem exactGram_charpoly_eq_prod {k : ℕ} (A : Core k) (hA : A.IsHermitian) :
    A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (orderedEigenvalue A hA i)) := by
  have h := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).charpoly_eq
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := k))
  simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.charpoly_toLin,
    orderedEigenvalue] using h

theorem exactGramSignedCoeff_charpoly {k : ℕ} (A : Core k) (hA : A.IsHermitian)
    (j : ℕ) (hj : j ≤ k) :
    exactGramSignedCoeff A.charpoly k j =
      exactGramElementary (orderedEigenvalue A hA) j := by
  rw [exactGram_charpoly_eq_prod A hA]
  exact exactGramSignedCoeff_prod _ j hj

/-- Characteristic-coefficient ratios bracket the literal sorted PSD
eigenvalue, rather than an unspecified enumeration of the roots. -/
theorem exactGram_charpoly_ratio {k : ℕ} (A : Core k) (hA : A.PosSemidef)
    (j : Fin k) (hj : 0 < orderedEigenvalue A hA.isHermitian j) :
    0 < exactGramSignedCoeff A.charpoly k j.val ∧
      orderedEigenvalue A hA.isHermitian j / ((j.val+1 : ℕ) : ℝ) ≤
        exactGramSignedCoeff A.charpoly k (j.val+1) /
          exactGramSignedCoeff A.charpoly k j.val ∧
      exactGramSignedCoeff A.charpoly k (j.val+1) /
          exactGramSignedCoeff A.charpoly k j.val ≤
        ((k-j.val : ℕ) : ℝ) * orderedEigenvalue A hA.isHermitian j := by
  rw [exactGramSignedCoeff_charpoly A hA.isHermitian j.val (Nat.le_of_lt j.isLt),
    exactGramSignedCoeff_charpoly A hA.isHermitian (j.val+1) j.isLt]
  exact exactGramElementary_ratio (orderedEigenvalue A hA.isHermitian)
    (orderedEigenvalue_nonneg A hA)
    ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian).eigenvalues_antitone
      finrank_euclideanSpace_fin) j hj

theorem exactGramSignedCoeff_pos_iff {k : ℕ} (A : Core k) (hA : A.PosSemidef)
    (j : Fin k) : 0 < exactGramSignedCoeff A.charpoly k (j.val+1) ↔
      0 < orderedEigenvalue A hA.isHermitian j := by
  let v := orderedEigenvalue A hA.isHermitian
  have hv : ∀ i, 0 ≤ v i := orderedEigenvalue_nonneg A hA
  have hsort : Antitone v :=
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian).eigenvalues_antitone
      finrank_euclideanSpace_fin
  rw [exactGramSignedCoeff_charpoly A hA.isHermitian (j.val+1) j.isLt]
  change 0 < exactGramElementary v (j.val+1) ↔ 0 < v j
  constructor
  · intro he
    by_contra hj
    have hz : v j = 0 := le_antisymm (le_of_not_gt hj) (hv _)
    have hu := exactGramElementary_upper_mul v hv hsort j
    rw [hz, mul_zero, zero_mul] at hu
    linarith
  · intro hj
    exact exactGramElementary_pos v hv (j.val+1) j.isLt
      (fun i hi => hj.trans_le (hsort (show i ≤ j by exact Nat.le_of_lt_succ hi)))

end
end HierarchicalAbsoluteSpectral
