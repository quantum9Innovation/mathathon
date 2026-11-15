import HierarchicalAbsoluteSpectral.ExactGramCharpolyAlgorithm

/-!
Complete arithmetic cost of the original exact-field coefficient route.
The bound includes every Krylov/rank-profile stage, the two final matrix
products, every companion-factor sign, and every convolution operation.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped BigOperators

theorem exactGramBranchingStep_work_bound_of_cap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N →
      a ≤ N → b ≤ N → c ≤ N → ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    {n d : ℕ} {A : Core n} (b : ExactGramKrylovBasis A d)
    (N : ℕ) (hN : 1 ≤ N) (hnN : n ≤ N) (hwwN : b.width+b.width ≤ N) :
    ((exactGramBranchingStep kernels b).work:ℝ) ≤ 22*(C+1)*(N:ℝ)^p := by
  have hwN : b.width ≤ N := b.width_le.trans hnN
  have hE := kernelEnvelope_bound kernels C p hC hK N hN
  have hfirst : ((rankProfileMulProgram kernels b.power b.power).work:ℝ) ≤ C*(N:ℝ)^p := by
    apply le_trans _ hE
    exact_mod_cast rankProfileMulProgram_work_le kernels b.power b.power N hnN hnN hnN
  have hsecond : ((rankProfileMulProgram kernels b.power b.basis).work:ℝ) ≤ C*(N:ℝ)^p := by
    apply le_trans _ hE
    exact_mod_cast rankProfileMulProgram_work_le kernels b.power b.basis N hnN hnN hwN
  have hprofile (W : Matrix (Fin n) (Fin (b.width+b.width)) ℝ) :=
    fieldColumnRankProfileProgram_work_bound kernels C p hC hp hK W N hN hnN hwwN
  simp only [exactGramBranchingStep, work_bind, certify_work, work_pure, add_zero, Nat.cast_add]
  calc
    _ ≤ C*(N:ℝ)^p+(C*(N:ℝ)^p+20*(C+1)*(N:ℝ)^p) :=
      add_le_add hfirst (add_le_add hsecond (hprofile _))
    _ ≤ _ := by
      have hpow := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ N) p
      nlinarith

theorem exactGramBranchingProgram_work_bound_of_cap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N →
      a ≤ N → b ≤ N → c ≤ N → ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    {n : ℕ} (A : Core n) (t N : ℕ) (hN : 1 ≤ N) (h2n : n+n ≤ N) :
    ((exactGramBranchingProgram kernels A t).work:ℝ) ≤ 22*t*(C+1)*(N:ℝ)^p := by
  induction t with
  | zero => simp [exactGramBranchingProgram]
  | succ t ih =>
      rw [exactGramBranchingProgram, work_bind, Nat.cast_add]
      let b := (exactGramBranchingProgram kernels A t).eval
      have hw := b.width_le
      have hs := exactGramBranchingStep_work_bound_of_cap kernels C p hC hp hK b N hN
        (by omega) (by omega)
      dsimp only [b] at hs
      push_cast
      calc
        _ ≤ 22*(t:ℝ)*(C+1)*(N:ℝ)^p+22*(C+1)*(N:ℝ)^p := add_le_add ih hs
        _ = _ := by ring

theorem exactGramCharpolyFromBasisProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N →
      a ≤ N → b ≤ N → c ≤ N → ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    {n d : ℕ} {A : Core n} (b : ExactGramKrylovBasis A d) (hnd : n ≤ d)
    (N : ℕ) (hN : 1 ≤ N) (hnN : n+1 ≤ N) :
    ((exactGramCharpolyFromBasisProgram kernels b hnd).work:ℝ) ≤ 11*(C+1)*(N:ℝ)^p := by
  have hnN' : n ≤ N := by omega
  have hwN : b.width ≤ N := b.width_le.trans hnN'
  have hE := kernelEnvelope_bound kernels C p hC hK N hN
  have hfirst : ((rankProfileMulProgram kernels b.inverse A).work:ℝ) ≤ C*(N:ℝ)^p := by
    apply le_trans _ hE
    exact_mod_cast rankProfileMulProgram_work_le kernels b.inverse A N hwN hnN' hnN'
  have hsecond (M : Matrix (Fin b.width) (Fin n) ℝ) :
      ((rankProfileMulProgram kernels M b.basis).work:ℝ) ≤ C*(N:ℝ)^p := by
    apply le_trans _ hE
    exact_mod_cast rankProfileMulProgram_work_le kernels M b.basis N hwN hnN' hwN
  let chain := b.chains hnd
  have hproduct (c : ∀ g, Fin (chain.length g) → ℝ) :
      ((exactGramCompanionProductProgram chain.length c).work:ℝ) ≤ 9*(N:ℝ)^p := by
    have hwork : ((exactGramCompanionProductProgram chain.length c).work:ℝ) ≤ 9*(n+1:ℕ)^2 := by
      exact_mod_cast exactGramCompanionProductProgram_work_bound chain.length c n le_rfl
        (by rw [chain.sum_length]; exact b.width_le)
    have hsq : ((n+1:ℕ):ℝ)^2 ≤ (N:ℝ)^p := by
      calc
        _ ≤ (N:ℝ)^2 := by gcongr
        _ = (N:ℝ)^(2:ℝ) := (Real.rpow_two _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hp
    exact hwork.trans (by nlinarith)
  simp only [exactGramCharpolyFromBasisProgram, work_bind, certify_work, work_pure,
    add_zero, Nat.cast_add]
  calc
    _ ≤ C*(N:ℝ)^p+(C*(N:ℝ)^p+9*(N:ℝ)^p) :=
      add_le_add hfirst (add_le_add (hsecond _) (hproduct _))
    _ ≤ _ := by
      have hpow := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ N) p
      nlinarith

/-- A finite all-input cost cap, including empty matrices. For positive
dimension this is `O(n^p log(n+1))`, the appendix's soft matrix cost. -/
theorem exactGramCharpolyProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N →
      a ≤ N → b ≤ N → c ≤ N → ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    {n : ℕ} (A : Core n) :
    ((exactGramCharpolyProgram kernels A).work:ℝ) ≤
      33*(C+1)*(Nat.clog 2 (n+1)+1:ℕ)*((2*(n+1):ℕ):ℝ)^p := by
  let t := Nat.clog 2 (n+1)
  let N := 2*(n+1)
  have hN : 1 ≤ N := by dsimp [N]; omega
  have h2n : n+n ≤ N := by dsimp [N]; omega
  have hnN : n+1 ≤ N := by dsimp [N]; omega
  have hnd : n ≤ exactGramKrylovWidth t := by
    rw [exactGramKrylovWidth_eq]
    exact (Nat.le_succ n).trans (Nat.le_pow_clog (by norm_num) _)
  have hloop := exactGramBranchingProgram_work_bound_of_cap kernels C p hC hp hK A t N hN h2n
  simp only [exactGramCharpolyProgram, work_bind, Nat.cast_add]
  have hout := exactGramCharpolyFromBasisProgram_work_bound kernels C p hC hp hK
    (exactGramBranchingProgram kernels A t).eval hnd N hN hnN
  dsimp only [N,t] at hloop hout
  simp only [Nat.cast_one]
  have hpow := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (2*(n+1):ℕ)) p
  have hnonneg : 0 ≤ (C+1)*((2*(n+1):ℕ):ℝ)^p := mul_nonneg (by linarith) hpow
  have ht : 0 ≤ (Nat.clog 2 (n+1):ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg ht hnonneg]

theorem exactGramCharpolyInitializerProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N →
      a ≤ N → b ≤ N → c ≤ N → ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    {n : ℕ} (A : Core n) (j : Fin n) (stretch : ℝ) :
    ((exactGramCharpolyInitializerProgram kernels A j stretch).work:ℝ) ≤
      33*(C+1)*(Nat.clog 2 (n+1)+1:ℕ)*((2*(n+1):ℕ):ℝ)^p+7 := by
  have hwork : ((exactGramCharpolyInitializerProgram kernels A j stretch).work:ℝ) ≤
      (exactGramCharpolyProgram kernels A).work+7 := by
    exact_mod_cast exactGramCharpolyInitializerProgram_work_le kernels A j stretch
  exact hwork.trans (add_le_add
    (exactGramCharpolyProgram_work_bound kernels C p hC hp hK A) (le_refl 7))

/-- The algorithm is instantiated by the repository's verified fast matrix
circuits. No characteristic-polynomial algorithm is assumed in this witness. -/
theorem exists_fast_exactGramCharpolyProgram (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ), 0 < C ∧
      ∀ (n : ℕ) (A : Core n),
        (exactGramCharpolyProgram kernels A).admissible ∧
        (exactGramCharpolyProgram kernels A).rankProfileFieldOnly ∧
        exactGramDenseToPolynomial (exactGramCharpolyProgram kernels A).eval.coefficients = A.charpoly ∧
        ((exactGramCharpolyProgram kernels A).work:ℝ) ≤
          C*(Nat.clog 2 (n+1)+1:ℕ)*((2*(n+1):ℕ):ℝ)^(9/4+ζ) := by
  obtain ⟨kernels,C,hC,hK⟩ := exists_padded_arithmetic_kernels ζ hζ
  refine ⟨kernels,33*(C+1),by positivity,?_⟩
  intro n A
  refine ⟨exactGramCharpolyProgram_admissible kernels A,
    exactGramCharpolyProgram_fieldOnly kernels A, exactGramCharpolyProgram_correct kernels A, ?_⟩
  apply exactGramCharpolyProgram_work_bound kernels C (9/4+ζ) hC (by linarith) _ A
  intro a b c N hmax _hN ha hb hc
  apply (hK a b c hmax).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (by positivity)
    (by exact_mod_cast max_le ha (max_le hb hc)) (by linarith)

theorem exactGramCoeffInitializerProgram_fieldOnly {n : ℕ} (p : Polynomial ℝ)
    (j : Fin n) (stretch : ℝ) :
    (exactGramCoeffInitializerProgram p j stretch).rankProfileFieldOnly := by
  simp only [exactGramCoeffInitializerProgram, rankProfileFieldOnly_bind,
    rankProfileFieldOnly_mul, eval_mul, true_and, ArithmeticProgram.rankProfileFieldOnly]
  split <;> simp only [rankProfileFieldOnly_bind, rankProfileFieldOnly_div,
    rankProfileFieldOnly_mul, rankProfileFieldOnly_pure, and_self]

theorem exactGramCharpolyInitializerProgram_fieldOnly
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) (j : Fin n) (stretch : ℝ) :
    (exactGramCharpolyInitializerProgram kernels A j stretch).rankProfileFieldOnly := by
  simp only [exactGramCharpolyInitializerProgram, rankProfileFieldOnly_bind,
    exactGramCharpolyProgram_fieldOnly, exactGramCoeffInitializerProgram_fieldOnly, and_self]

end
end HierarchicalAbsoluteSpectral
