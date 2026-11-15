import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixCore
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixRectCost
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixExactCost
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftRandomCost

/-! A finite, all-outcome cost for the literal support-level comparator.
The cap depends on dimension and accuracy alone. Both zero-check failures
and the exact-support branch satisfy the same bound. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

def exactGramAppendixSearchWorkBudget (C q : ℝ) (m : ℕ) (ε : ℝ) (hε : 0 < ε) : ℝ :=
  33*(C+1)*(Nat.clog 2 (m+1)+1:ℕ)*((2*(m+1):ℕ):ℝ)^q+10+
    2*(exactGramAppendixSearchCap m ε hε:ℝ)+
    (exactGramAppendixSearchCap m ε hε:ℝ)*(5+105*(C+1)*(m:ℝ)^q)

def exactGramAppendixCoreWorkBudget (C q : ℝ) (m : ℕ) (ε : ℝ) (hε : 0 < ε) : ℝ :=
  33*(C+1)*(Nat.clog 2 (m+1)+1:ℕ)*((2*(m+1):ℕ):ℝ)^q+
    (36+105*(exactGramAppendixSearchCap m ε hε:ℝ))*(C+1)*(m:ℝ)^q+
    7*(exactGramAppendixSearchCap m ε hε:ℝ)+16

theorem exactGramAppendixUpperProgram_work_bound_dimension
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q : ℝ) (hC : 0 < C) (hq : 2 ≤ q)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^q)
    {k : ℕ} (H : Core k) (hH : H.PosSemidef) (j : Fin k)
    (m : ℕ) (hkm : k ≤ m) (ε : ℝ) (hε : 0 < ε)
    (tape : ExactGramAppendixSearchTape k ε hε) :
    ((exactGramAppendixUpperProgram kernels H hH j ε hε tape).work:ℝ) ≤
      exactGramAppendixSearchWorkBudget C q m ε hε := by
  rw [exactGramAppendixUpperProgram_work]
  have hbound := exactGramAppendixSearchProgram_work_bound kernels C q hC hq hK H hH j ε hε tape
  have hcap : (exactGramAppendixSearchCap k ε hε:ℝ) ≤ exactGramAppendixSearchCap m ε hε := by
    exact_mod_cast exactGramAppendixSearchCap_mono k m hkm ε hε
  have hlog : (Nat.clog 2 (k+1)+1:ℕ) ≤ Nat.clog 2 (m+1)+1 :=
    Nat.add_le_add_right (Nat.clog_monotone 2 (by omega)) 1
  have hpow : ((2*(k+1):ℕ):ℝ)^q ≤ ((2*(m+1):ℕ):ℝ)^q :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2 (Nat.add_le_add_right hkm 1))
      (by linarith)
  have hsmall : (k:ℝ)^q ≤ (m:ℝ)^q :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkm) (by linarith)
  apply hbound.trans
  calc
    _ ≤ 33*(C+1)*(Nat.clog 2 (m+1)+1:ℕ)*((2*(m+1):ℕ):ℝ)^q+7+
        (2*(exactGramAppendixSearchCap m ε hε:ℝ)+3)+
        (exactGramAppendixSearchCap m ε hε:ℝ)*(5+105*(C+1)*(m:ℝ)^q) := by
      gcongr
    _ = _ := by unfold exactGramAppendixSearchWorkBudget; ring

theorem exactGramAppendixCoreProgram_work_bound_rectangular
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q leftCost rightCost outputCost : ℝ) (hC : 0 < C) (hq : 2 ≤ q)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^q)
    {n m p : ℕ} {A : Matrix (Fin n) (Fin m) ℝ} {B : Matrix (Fin m) (Fin p) ℝ}
    (support : ExactGramAppendixSupport A B) (r : ℕ) (ε : ℝ) (hε : 0 < ε)
    (tape : ExactGramAppendixTape support.dimension ε hε) (hm : 1 ≤ m)
    (physical : ExactGramAppendixPhysicalBudget kernels n m p r leftCost rightCost outputCost) :
    ((exactGramAppendixCoreProgram kernels support r ε hε tape).work:ℝ) ≤
      exactGramAppendixCoreWorkBudget C q m ε hε+4*leftCost+rightCost+outputCost := by
  let P : ℝ := (C+1)*(m:ℝ)^q
  let K : ℝ := (support.dimension*support.dimension:ℕ)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hkk : K ≤ P := by
    have hs : (support.dimension:ℝ)^2 ≤ (m:ℝ)^2 := by
      have hh : (support.dimension:ℝ) ≤ m := by exact_mod_cast support.dimension_le
      nlinarith [show (0:ℝ) ≤ support.dimension from Nat.cast_nonneg _]
    have hp : (m:ℝ)^(2:ℝ) ≤ (m:ℝ)^q :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm : (1:ℝ) ≤ m) hq
    rw [Real.rpow_two] at hp
    have hpow := Real.rpow_nonneg (Nat.cast_nonneg m) q
    dsimp only [P,K]
    push_cast
    nlinarith
  have hl0 : 0 ≤ leftCost := (Nat.cast_nonneg _).trans (physical.forward 0 (Nat.zero_le _))
  have hr0 : 0 ≤ rightCost := (Nat.cast_nonneg _).trans (physical.right 0 (Nat.zero_le _))
  have ho0 : 0 ≤ outputCost := (Nat.cast_nonneg _).trans (physical.output 0 (Nat.zero_le _))
  have hsearch0 : 0 ≤ exactGramAppendixSearchWorkBudget C q m ε hε := by
    unfold exactGramAppendixSearchWorkBudget
    positivity
  have htotal : exactGramAppendixSearchWorkBudget C q m ε hε+
      (6+K+K+(24*P+(10*P+4*leftCost+rightCost+outputCost))) ≤
      exactGramAppendixCoreWorkBudget C q m ε hε+4*leftCost+rightCost+outputCost := by
    unfold exactGramAppendixSearchWorkBudget exactGramAppendixCoreWorkBudget
    dsimp only [P] at hkk ⊢
    nlinarith
  have hupper (j : Fin support.dimension) :=
    exactGramAppendixUpperProgram_work_bound_dimension kernels C q hC hq hK support.core
      support.positive.posSemidef j m support.dimension_le ε hε tape.1
  have hcong (D : Core support.dimension) (hD : Dᵀ = D) (S : Core support.dimension) :
      ((congruenceInertiaProgram kernels D hD S).work:ℝ) ≤ 24*P := by
    simpa only [P,mul_assoc] using
      exactGramAppendixCongruence_work_bound kernels C q hC hq hK D hD S m hm support.dimension_le
  have hlift {D : Core support.dimension} (diag : FiniteCongruenceDiagonal D)
      (hr : diag.negativeCount ≤ r) :
      ((exactGramAppendixLiftProgram kernels A B support.lift diag hr).work:ℝ) ≤
        10*P+4*leftCost+rightCost+outputCost := by
    simpa only [P,mul_assoc] using
      exactGramAppendixLiftProgram_work_bound_rectangular kernels C q leftCost rightCost outputCost
        hC hq hK A B support.lift diag hr hm support.dimension_le physical.forward physical.gram
        physical.basis physical.left physical.right physical.output
  have hexact (hfull : support.dimension ≤ r) :
      ((support.exactOutputProgram kernels r hfull).work:ℝ) ≤
        10*P+4*leftCost+rightCost+outputCost := by
    simpa only [P,mul_assoc] using
      exactGramAppendixExactOutputProgram_work_bound_rectangular kernels C q leftCost rightCost outputCost
        hC hq hK A B support hfull hm physical.forward physical.gram physical.basis physical.left
        physical.right physical.output
  apply le_trans _ htotal
  unfold exactGramAppendixCoreProgram
  split
  · simp only [work_bind, certify_work, work_pure, add_zero]
    exact (hexact _).trans (by linarith)
  · simp only [work_bind, certify_work]
    split
    · simp only [work_pure, add_zero]
      exact (hupper _).trans (by linarith)
    · simp only [work_bind, certify_work, exactGramAppendixJitterProgram_work,
        blockScaleProgram_work, blockSubProgram_work]
      split
      · simp only [work_pure, add_zero, Nat.cast_add, Nat.cast_ofNat]
        calc
          _ ≤ exactGramAppendixSearchWorkBudget C q m ε hε+(6+(K+(K+24*P))) := by
            gcongr
            · exact hupper _
            · exact hcong _ _ _
          _ ≤ _ := by linarith
      · simp only [work_bind, certify_work, work_pure, add_zero, Nat.cast_add, Nat.cast_ofNat]
        calc
          _ ≤ exactGramAppendixSearchWorkBudget C q m ε hε+
              (6+(K+(K+(24*P+(10*P+4*leftCost+rightCost+outputCost))))) := by
            gcongr
            · exact hupper _
            · exact hcong _ _ _
            · exact hlift _ _
          _ = _ := by ring

end
end HierarchicalAbsoluteSpectral
