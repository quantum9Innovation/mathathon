import HierarchicalAbsoluteSpectral.BaseFixedCoreAlgebraCostBounds

/-! Numeric bounds for the actual support, Gaussian initializer and
coarse-base programs.  The coarse Gram products are charged separately.
Core algebra is never multiplied by a Krylov/filter degree here. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L k s t : ℕ}
attribute [local irreducible] mainPositiveQueryProgram mainStrongThresholdProgram

theorem coarseSupportProgram_work_core_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (H : Matrix (Fin s) (Fin m) ℝ) (J : Matrix (Fin t) (Fin m) ℝ) (hm : 1 ≤ m) :
    ((coarseSupportProgram K H J).work:ℝ) ≤
      baseFixedCoarseGramCost K m s t+11*(C+1)*(m:ℝ)^e :=
  (Nat.cast_le.mpr (coarseSupportProgram_work_bound K H J hm)).trans
    (coarseSupportWorkCap_core_bound K C e hC he hK m s t hm)

theorem gaussianInitializerProgram_work_empty_le
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core 0) (Ξ : Matrix (Fin 0) (Fin 0) ℝ) (β : ℝ) :
    (gaussianInitializerProgram K T Ξ β).work ≤ 5*(K 0 0 0).cost+10 := by
  have hRange (Y : Matrix (Fin 0) (Fin 0) ℝ) :
      (orthogonalRangeProgram K Y).work = 2*(K 0 0 0).cost := by
    simp [orthogonalRangeProgram,psdGramProgram,psdEmpty]
    omega
  let Y := ((K 0 0 0).program T Ξ).certify.eval.val
  let out := (orthogonalRangeProgram K Y).eval
  have hd : out.dimension = 0 := by have hh := out.dimension_le_cols; omega
  simp only [gaussianInitializerProgram,work_bind,certify_work,ArithmeticKernel.program_work,
    blockSubProgram_work,matrixFrobeniusProgram_work,initializerRatioProgram_work,work_pure,add_zero]
  change (K 0 0 0).cost+((orthogonalRangeProgram K Y).work+
    ((K out.dimension 0 0).cost+((K 0 out.dimension 0).cost+
      (0+(1+(7+(initializerBracketProgram _ _).work)))))) ≤ _
  calc
    _ ≤ (K 0 0 0).cost+((orthogonalRangeProgram K Y).work+
        ((K out.dimension 0 0).cost+((K 0 out.dimension 0).cost+(0+(1+(7+2)))))) := by
      gcongr
      exact initializerBracketProgram_work _ _
    _ = _ := by rw [hd,hRange]; ring

/-- This is a numerical bound for the executed initializer, including an
empty support and arbitrary zero/rank-deficient input matrices. -/
theorem gaussianInitializerProgram_work_core_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ)
    (N : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) (hr : r ≤ k) :
    ((gaussianInitializerProgram K T Ξ β).work:ℝ) ≤ 25*(C+1)*(N:ℝ)^e := by
  by_cases hk1 : 1 ≤ k
  · exact (Nat.cast_le.mpr (gaussianInitializerProgram_work_le K T Ξ β hk1 hr)).trans
      (baseFixedInitializerWorkCap_bound K C e hC he hK k r N hN hk (hr.trans hk))
  · have hk0 : k = 0 := by omega
    have hr0 : r = 0 := by omega
    subst k r
    have hw : ((gaussianInitializerProgram K T Ξ β).work:ℝ) ≤ 5*(K 0 0 0).cost+10 := by
      exact_mod_cast gaussianInitializerProgram_work_empty_le K T Ξ β
    have hc := hK 0 0 0 N hN (by omega) (by omega) (by omega)
    have hpow1 : 1 ≤ (N:ℝ)^e := Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
    have hpow0 := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ N) e
    nlinarith [mul_nonneg hC.le hpow0]

theorem baseFixedSetupCost_log_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (k N d : ℕ) (hN : 1 ≤ N) (hk : k ≤ N)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1/64) :
    ((baseConstructionCost K k h hh+2*k*k+d:ℕ):ℝ) ≤
      (36+(d:ℝ))*(C+1)*(N:ℝ)^e*(1+4*Real.log (1/(4*h))) := by
  let B := 1+4*Real.log (1/(4*h))
  have hlog : 0 ≤ Real.log (1/(4*h)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by positivity : 0 < 4*h)).mpr
    linarith
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hsteps := baseNewtonSteps_bound h hh hh1
  have hcoeff : 25+(d:ℝ)+11*(baseNewtonSteps h hh:ℝ) ≤ (36+(d:ℝ))*B := by
    change (baseNewtonSteps h hh:ℝ) ≤ B at hsteps
    nlinarith [mul_nonneg (by positivity : 0 ≤ 25+(d:ℝ)) (sub_nonneg.mpr hB)]
  have hb := baseFixedSetupCost_core_bound K C e hC he hK k N d hN hk h hh
  have hm := mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ (C+1)*(N:ℝ)^e)
  dsimp only [B] at hm
  nlinarith only [hb,hm]

theorem coarseBaseProgram_work_core_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (Q : Core k) (hQ : Q.PosSemidef) (t : ℝ) (ht : 0 < t)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1/64) (N : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) :
    ((coarseBaseProgram K Q hQ t ht h hh).work:ℝ) ≤
      36*(C+1)*(N:ℝ)^e*(1+4*Real.log (1/(4*h))) := by
  rw [coarseBaseProgram_work]
  simpa only [Nat.add_zero,Nat.cast_zero,add_zero] using
    baseFixedSetupCost_log_bound K C e hC he hK k N 0 hN hk h hh hh1

theorem mainInitializerWorkCap_core_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (D : MainSupportData S) :
    (baseFixedInitializerWorkCap K D.pair.dimension r:ℝ) ≤ 25*(C+1)*(m:ℝ)^e :=
  baseFixedInitializerWorkCap_bound K C e hC he hK _ r m
    (by have hh:=I.rank_positive; have hh':=I.rank_le_core; omega)
    (mainSupport_dimension_le S D) I.rank_le_core

theorem mainGaussianInitializerProgram_work_core_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (D : MainSupportData S)
    (g : MainRandomTape I) (hr : r ≤ D.pair.dimension) :
    ((gaussianInitializerProgram K D.rightGram (columnsMatrix (mainInitializerArray I S D g))
      I.singleFailure).work:ℝ) ≤ 25*(C+1)*(m:ℝ)^e :=
  gaussianInitializerProgram_work_core_bound K C e hC he hK _ _ _ m
    (by have hh:=I.rank_positive; have hh':=I.rank_le_core; omega)
    (mainSupport_dimension_le S D) hr

end
end HierarchicalAbsoluteSpectral
