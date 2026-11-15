import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedHalfKernel

/-! A literal dense-output circuit family with subpolynomial overhead.
Finite gate-count minima diagonalize the certified positive-slack families. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Matmul.RectangularPrograms

theorem exists_fixed_dense_output_kernel_subpolynomial :
    ∃ (K : ∀ n : ℕ, ArithmeticKernel n (width (1/2) n) n) (χ : ℕ → ℝ),
      (∀ n, 1 ≤ χ n) ∧
      (∀ n : ℕ, 1 ≤ n → ((K n).cost:ℝ) ≤ (n:ℝ)^2*χ n) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, χ n ≤ (n:ℝ)^ε) := by
  have hex : ∀ j : ℕ, ∃ (K : ∀ n : ℕ, ArithmeticKernel n (width (1/2) n) n) (C : ℝ),
      0 < C ∧ ∀ n : ℕ, 1 ≤ n → ((K n).cost:ℝ) ≤ C*(n:ℝ)^(2+1/(j+1:ℝ)) := by
    intro j
    exact exists_half_rectangular_arithmetic_kernels (1/(j+1:ℝ)) (by positivity)
  choose P C hC hP using hex
  let caps := fun n : ℕ => List.ofFn (fun j : Fin (n+1) =>
    (⟨n,width (1/2) n,n,P j.val n⟩ : MatrixKernelCap))
  let K := fun n : ℕ => combineKernelCaps classicalArithmeticKernels (caps n) n (width (1/2) n) n
  have hdom (n j : ℕ) (hj : j ≤ n) : (K n).cost ≤ (P j n).cost := by
    apply combineKernelCaps_cost_le_cap classicalArithmeticKernels (caps n)
      ⟨n,width (1/2) n,n,P j n⟩ _ n (width (1/2) n) n ⟨le_rfl,le_rfl,le_rfl⟩
    apply List.mem_ofFn.mpr
    exact ⟨⟨j,by omega⟩,rfl⟩
  have hsmall (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n : ℕ in atTop, ((K n).cost:ℝ) ≤ (n:ℝ)^(2+ε) := by
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
      _ ≤ C j*(n:ℝ)^(2+1/(j+1:ℝ)) := hcost.trans (hP j n hn1)
      _ ≤ (n:ℝ)^(ε/2)*(n:ℝ)^(2+1/(j+1:ℝ)) :=
        mul_le_mul_of_nonneg_right hCn (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (n:ℝ)^(ε/2+(2+1/(j+1:ℝ))) := (Real.rpow_add hn0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  let χ := fun n : ℕ => 1+((K n).cost:ℝ)/(n:ℝ)^2
  refine ⟨K,χ,?_,?_,?_⟩
  · intro n
    dsimp [χ]
    have hh : 0 ≤ ((K n).cost:ℝ)/(n:ℝ)^2 := by positivity
    linarith
  · intro n hn
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    dsimp [χ]
    have he : (n:ℝ)^2*(1+((K n).cost:ℝ)/(n:ℝ)^2) = (n:ℝ)^2+(K n).cost := by
      field_simp
    rw [he]
    nlinarith [sq_nonneg (n:ℝ)]
  · intro ε hε
    have ht : Tendsto (fun n : ℕ => (n:ℝ)^(ε/2)) atTop atTop :=
      (tendsto_rpow_atTop (show 0 < ε/2 by positivity)).comp tendsto_natCast_atTop_atTop
    filter_upwards [hsmall (ε/2) (by positivity),eventually_ge_atTop (1:ℕ),
      ht.eventually (eventually_ge_atTop (2:ℝ))] with n hn hn1 hlarge
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
    have hdiv : ((K n).cost:ℝ)/(n:ℝ)^2 ≤ (n:ℝ)^(ε/2) := by
      apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
      calc
        _ ≤ (n:ℝ)^(2+ε/2) := hn
        _ = _ := by rw [Real.rpow_add hn0,Real.rpow_two]; ring
    have hpow : ((n:ℝ)^(ε/2))^2 = (n:ℝ)^ε := by
      rw [← Real.rpow_two,← Real.rpow_mul hn0.le]
      congr 1
      ring
    dsimp [χ]
    nlinarith


/-- Both half-width orientations are fixed before any exponent is requested. -/
theorem exists_fixed_half_output_kernels_subpolynomial :
    ∃ (outer : ∀ N : ℕ, ArithmeticKernel N N (width (1/2) N))
      (inner : ∀ N : ℕ, ArithmeticKernel N (width (1/2) N) N) (χ : ℕ → ℝ),
      (∀ N, 1 ≤ χ N) ∧
      (∀ N : ℕ, 1 ≤ N →
        ((outer N).cost:ℝ) ≤ (N:ℝ)^2*χ N ∧
        ((inner N).cost:ℝ) ≤ (N:ℝ)^2*χ N) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, χ N ≤ (N:ℝ)^ε) := by
  obtain ⟨outer,χo,hχo,ho,hso⟩ := exists_fixed_half_kernel_subpolynomial
  obtain ⟨inner,χi,hχi,hi,hsi⟩ := exists_fixed_dense_output_kernel_subpolynomial
  refine ⟨outer,inner,fun N => max (χo N) (χi N),?_,?_,?_⟩
  · intro N
    exact (hχo N).trans (le_max_left _ _)
  · intro N hN
    constructor
    · exact (ho N hN).trans
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _))
    · exact (hi N hN).trans
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _))
  · intro ε hε
    filter_upwards [hso ε hε,hsi ε hε] with N ho hi
    exact max_le ho hi

end
end HierarchicalAbsoluteSpectral
