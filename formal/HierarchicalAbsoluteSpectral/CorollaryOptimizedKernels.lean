import HierarchicalAbsoluteSpectral.RuntimeFamilySequences
import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedKernelFamily
import Matmul.RectangularContinuity

/-! Actual circuit families behind the comparator bounds.  Finite minima of
certified positive-slack circuits give one family independent of the exponent
slack in the final asymptotic statement. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Matmul.RectangularPrograms Matmul.RectangularOptimization
open scoped Topology

theorem exists_fixed_rectangular_kernel_subpolynomial (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ (K : ∀ n : ℕ, ArithmeticKernel n (width κ n) n) (χ : ℕ → ℝ),
      (∀ n, 1 ≤ χ n) ∧
      (∀ n : ℕ, 1 ≤ n → ((K n).cost:ℝ) ≤ (n:ℝ)^(rectangularBound κ)*χ n) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, χ n ≤ (n:ℝ)^ε) := by
  have hex : ∀ j : ℕ, ∃ (K : ∀ n : ℕ, ArithmeticKernel n (width κ n) n) (C : ℝ),
      0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        ((K n).cost:ℝ) ≤ C*(n:ℝ)^(rectangularBound κ+1/(j+1:ℝ)) := by
    intro j
    exact exists_rectangular_arithmetic_kernels κ (1/(j+1:ℝ)) hκ (by positivity)
  choose P C hC hP using hex
  let caps := fun n : ℕ => List.ofFn (fun j : Fin (n+1) =>
    (⟨n,width κ n,n,P j.val n⟩ : MatrixKernelCap))
  let K := fun n : ℕ => combineKernelCaps classicalArithmeticKernels (caps n) n (width κ n) n
  have hdom (n j : ℕ) (hj : j ≤ n) : (K n).cost ≤ (P j n).cost := by
    apply combineKernelCaps_cost_le_cap classicalArithmeticKernels (caps n)
      ⟨n,width κ n,n,P j n⟩ _ n (width κ n) n ⟨le_rfl,le_rfl,le_rfl⟩
    apply List.mem_ofFn.mpr
    exact ⟨⟨j,by omega⟩,rfl⟩
  have hsmall (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n : ℕ in atTop, ((K n).cost:ℝ) ≤ (n:ℝ)^(rectangularBound κ+ε) := by
    obtain ⟨j,hj⟩ := exists_nat_one_div_lt (show (0:ℝ) < ε/2 by positivity)
    have ht : Tendsto (fun n : ℕ => (n:ℝ)^(ε/2)) atTop atTop :=
      (tendsto_rpow_atTop (show 0 < ε/2 by positivity)).comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop (max j 1),ht.eventually (eventually_ge_atTop (C j))]
      with n hn hCn
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hjn : j ≤ n := (le_max_left _ _).trans hn
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
    have hcost : ((K n).cost:ℝ) ≤ (P j n).cost := by exact_mod_cast hdom n j hjn
    calc
      _ ≤ C j*(n:ℝ)^(rectangularBound κ+1/(j+1:ℝ)) := hcost.trans (hP j n hn1)
      _ ≤ (n:ℝ)^(ε/2)*(n:ℝ)^(rectangularBound κ+1/(j+1:ℝ)) :=
        mul_le_mul_of_nonneg_right hCn (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (n:ℝ)^(ε/2+(rectangularBound κ+1/(j+1:ℝ))) :=
        (Real.rpow_add hn0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  let χ := fun n : ℕ => 1+((K n).cost:ℝ)/(n:ℝ)^(rectangularBound κ)
  refine ⟨K,χ,?_,?_,?_⟩
  · intro n
    dsimp [χ]
    have hh : 0 ≤ ((K n).cost:ℝ)/(n:ℝ)^(rectangularBound κ) := by positivity
    linarith
  · intro n hn
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have hp : 0 < (n:ℝ)^(rectangularBound κ) := Real.rpow_pos_of_pos hnR _
    dsimp [χ]
    have he : (n:ℝ)^(rectangularBound κ)*(1+((K n).cost:ℝ)/(n:ℝ)^(rectangularBound κ)) =
        (n:ℝ)^(rectangularBound κ)+(K n).cost := by field_simp
    rw [he]
    linarith
  · intro ε hε
    have ht : Tendsto (fun n : ℕ => (n:ℝ)^(ε/2)) atTop atTop :=
      (tendsto_rpow_atTop (show 0 < ε/2 by positivity)).comp tendsto_natCast_atTop_atTop
    filter_upwards [hsmall (ε/2) (by positivity),eventually_ge_atTop (1:ℕ),
      ht.eventually (eventually_ge_atTop (2:ℝ))] with n hn hn1 hlarge
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
    have hdiv : ((K n).cost:ℝ)/(n:ℝ)^(rectangularBound κ) ≤ (n:ℝ)^(ε/2) := by
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)).mpr
      calc
        _ ≤ (n:ℝ)^(rectangularBound κ+ε/2) := hn
        _ = _ := by rw [Real.rpow_add hn0]; ring
    have hpow : ((n:ℝ)^(ε/2))^2 = (n:ℝ)^ε := by
      rw [← Real.rpow_two,← Real.rpow_mul hn0.le]
      congr 1
      ring
    dsimp [χ]
    nlinarith

def comparatorGramCaps (κ : ℝ)
    (P : ∀ j n : ℕ, ArithmeticKernel n (width (κ+1/(j+1:ℝ)) n) n)
    (m : ℕ) : List MatrixKernelCap :=
  List.ofFn (fun j : Fin (m+1) =>
    ⟨m,width (κ+1/(j.val+1:ℝ)) m,m,P j.val m⟩)

/-- The family is fixed once the certified candidates are chosen.  Its
finite gate-count minimum uses only dimensions, never matrix entries. -/
def comparatorGramKernelFamily (κ : ℝ)
    (P : ∀ j n : ℕ, ArithmeticKernel n (width (κ+1/(j+1:ℝ)) n) n)
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (m : ℕ) :
    ∀ a b c : ℕ, ArithmeticKernel a b c :=
  combineKernelCaps fallback (comparatorGramCaps κ P m)

theorem comparatorGramKernelFamily_le_fallback (κ : ℝ)
    (P : ∀ j n : ℕ, ArithmeticKernel n (width (κ+1/(j+1:ℝ)) n) n)
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (m a b c : ℕ) :
    (comparatorGramKernelFamily κ P fallback m a b c).cost ≤ (fallback a b c).cost :=
  combineKernelCaps_cost_le_fallback _ _ _ _ _

theorem comparatorGramKernelFamily_le_candidate (κ : ℝ)
    (P : ∀ j n : ℕ, ArithmeticKernel n (width (κ+1/(j+1:ℝ)) n) n)
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (m N j : ℕ) (hj : j ≤ m) (hN : N ≤ width (κ+1/(j+1:ℝ)) m) :
    (comparatorGramKernelFamily κ P fallback m m N m).cost ≤ (P j m).cost := by
  apply combineKernelCaps_cost_le_cap fallback (comparatorGramCaps κ P m)
    ⟨m,width (κ+1/(j+1:ℝ)) m,m,P j m⟩ _ m N m ⟨le_rfl,hN,le_rfl⟩
  apply List.mem_ofFn.mpr
  exact ⟨⟨j,by omega⟩,rfl⟩

theorem comparatorGramKernelFamily_le_candidate_shape (κ : ℝ)
    (P : ∀ j n : ℕ, ArithmeticKernel n (width (κ+1/(j+1:ℝ)) n) n)
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (m a b c j : ℕ) (hj : j ≤ m) (ha : a ≤ m)
    (hb : b ≤ width (κ+1/(j+1:ℝ)) m) (hc : c ≤ m) :
    (comparatorGramKernelFamily κ P fallback m a b c).cost ≤ (P j m).cost := by
  apply combineKernelCaps_cost_le_cap fallback (comparatorGramCaps κ P m)
    ⟨m,width (κ+1/(j+1:ℝ)) m,m,P j m⟩ _ a b c ⟨ha,hb,hc⟩
  apply List.mem_ofFn.mpr
  exact ⟨⟨j,by omega⟩,rfl⟩

theorem exists_comparator_gram_kernel_family_uniform (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ P : ∀ j n : ℕ, ArithmeticKernel n (width (κ+1/(j+1:ℝ)) n) n,
      ∀ (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop)
        (hN : ∀ᶠ i : ℕ in atTop, 0 < N i)
        (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) atTop (𝓝 κ))
        (fallback : ℕ → ∀ a b c : ℕ, ArithmeticKernel a b c)
        (ε : ℝ) (hε : 0 < ε),
      ∀ᶠ i : ℕ in atTop,
        ∀ a b c : ℕ, a ≤ m i → b ≤ N i → c ≤ m i →
          ((comparatorGramKernelFamily κ P (fallback i) (m i) a b c).cost:ℝ) ≤
            (m i:ℝ)^(rectangularBound κ+ε) := by
  have hex : ∀ j : ℕ,
      ∃ (P : ∀ n : ℕ, ArithmeticKernel n (width (κ+1/(j+1:ℝ)) n) n) (C : ℝ),
        0 < C ∧ ∀ n : ℕ, 1 ≤ n → ((P n).cost:ℝ) ≤
          C*(n:ℝ)^(rectangularBound (κ+1/(j+1:ℝ))+1/(j+1:ℝ)) := by
    intro j
    exact exists_rectangular_arithmetic_kernels (κ+1/(j+1:ℝ)) (1/(j+1:ℝ))
      (by positivity) (by positivity)
  choose P C hC hP using hex
  refine ⟨P,?_⟩
  intro m N hm hN hgrowth fallback ε hε
  obtain ⟨j,hj⟩ := exists_nat_one_div_lt (show (0:ℝ) < ε/4 by positivity)
  have hmR : Tendsto (fun i => (m i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have ht : Tendsto (fun i => (m i:ℝ)^(ε/2)) atTop atTop :=
    (tendsto_rpow_atTop (show 0 < ε/2 by positivity)).comp hmR
  have hdim := family_sequence_dimension_powers atTop (fun i => (m i:ℝ))
    (fun i => (N i:ℝ)) (κ-1) (1/(j+1:ℝ)) (by positivity) hmR
    (hN.mono (fun i hi => by exact_mod_cast hi))
    (by convert hgrowth using 1 <;> congr 1 <;> ring)
  have hbound : rectangularBound (κ+1/(j+1:ℝ)) ≤ rectangularBound κ+1/(j+1:ℝ) := by
    have hh := rectangularBound_le_add_delta hκ
      (show 0 ≤ κ+1/(j+1:ℝ) by positivity)
      (show κ ≤ κ+1/(j+1:ℝ) by linarith [show (0:ℝ) ≤ 1/(j+1:ℝ) by positivity])
    convert hh using 1 <;> ring
  filter_upwards [hm.eventually (eventually_ge_atTop (max j 1)),hdim,
    ht.eventually (eventually_ge_atTop (C j))] with i hi hNi hCi
  have hmi : 1 ≤ m i := (le_max_right _ _).trans hi
  have hji : j ≤ m i := (le_max_left _ _).trans hi
  have hm0 : (0:ℝ) < m i := by exact_mod_cast hmi
  have hm1 : (1:ℝ) ≤ m i := by exact_mod_cast hmi
  have hfit : N i ≤ width (κ+1/(j+1:ℝ)) (m i) := by
    have hreal : (N i:ℝ) ≤ (m i:ℝ)^(κ+1/(j+1:ℝ)) := by
      convert hNi.2 using 1 <;> congr 1 <;> ring
    exact_mod_cast hreal.trans (Nat.le_ceil ((m i:ℝ)^(κ+1/(j+1:ℝ))))
  intro a b c ha hb hc
  have hcost : ((comparatorGramKernelFamily κ P (fallback i) (m i) a b c).cost:ℝ)
      ≤ (P j (m i)).cost := by
    exact_mod_cast comparatorGramKernelFamily_le_candidate_shape κ P (fallback i)
      (m i) a b c j hji ha (hb.trans hfit) hc
  calc
    _ ≤ C j*(m i:ℝ)^(rectangularBound (κ+1/(j+1:ℝ))+1/(j+1:ℝ)) :=
      hcost.trans (hP j (m i) hmi)
    _ ≤ (m i:ℝ)^(ε/2)*(m i:ℝ)^(rectangularBound (κ+1/(j+1:ℝ))+1/(j+1:ℝ)) :=
      mul_le_mul_of_nonneg_right hCi (Real.rpow_nonneg hm0.le _)
    _ = (m i:ℝ)^(ε/2+(rectangularBound (κ+1/(j+1:ℝ))+1/(j+1:ℝ))) :=
      (Real.rpow_add hm0 _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)

theorem exists_comparator_gram_kernel_family (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ P : ∀ j n : ℕ, ArithmeticKernel n (width (κ+1/(j+1:ℝ)) n) n,
      ∀ (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop)
        (hN : ∀ᶠ i : ℕ in atTop, 0 < N i)
        (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) atTop (𝓝 κ))
        (fallback : ℕ → ∀ a b c : ℕ, ArithmeticKernel a b c)
        (ε : ℝ) (hε : 0 < ε),
      ∀ᶠ i : ℕ in atTop,
        ((comparatorGramKernelFamily κ P (fallback i) (m i) (m i) (N i) (m i)).cost:ℝ) ≤
          (m i:ℝ)^(rectangularBound κ+ε) := by
  obtain ⟨P,hP⟩ := exists_comparator_gram_kernel_family_uniform κ hκ
  refine ⟨P,?_⟩
  intro m N hm hN hgrowth fallback ε hε
  filter_upwards [hP m N hm hN hgrowth fallback ε hε] with i hi
  exact hi (m i) (N i) (m i) le_rfl le_rfl le_rfl

end
end HierarchicalAbsoluteSpectral
