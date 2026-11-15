import HierarchicalAbsoluteSpectral.CorollaryTwoLevelBudgets
import HierarchicalAbsoluteSpectral.BaseMainTapeCost
import HierarchicalAbsoluteSpectral.RuntimeFamilyDimensions

/-! All Gaussian tape entries, scalar preparation, input reads, and factor
writes in the two-level explicit construction budget. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Filter
open ArithmeticProgram hiding pure
variable {N m r : ℕ}

def twoLevelRemainingGaussianDrawCount (I : TwoLevelProblem N m r) : ℕ :=
  2*r*m+I.fixed.queryCap*I.fixed.repetitions*((r+1)*m+2*m*m)

theorem twoLevelGaussianDrawCount_eq (I : TwoLevelProblem N m r) :
    Fintype.card (MainGaussianIndex N m N r 1 I.fixed.queryCap I.fixed.repetitions) =
      12*2^dyadicPaddingLevel N+twoLevelRemainingGaussianDrawCount I := by
  rw [mainGaussianDrawCount]
  unfold twoLevelRemainingGaussianDrawCount
  ring

def twoLevelScalarPreparationWorkCap (I : TwoLevelProblem N m r) : ℕ :=
  (twoLevelParametersProgram m).work+4+3*I.fixed.queryCap+2*I.fixed.repetitions+29

def twoLevelScalarPreparationCoefficient (c : ℝ) : ℝ :=
  200+57/Real.log 2+3*twoLevelQueryCapCoefficient c+2*twoLevelRepetitionCoefficient c

theorem twoLevelScalarPreparationCoefficient_nonneg (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ twoLevelScalarPreparationCoefficient c := by
  dsimp [twoLevelScalarPreparationCoefficient,twoLevelRepetitionCoefficient,twoLevelQueryCapCoefficient]
  positivity

theorem twoLevelRemainingGaussianDrawCount_bound (I : TwoLevelProblem N m r)
    (c : ℝ) (hc : 0 ≤ c) (hm : 2 ≤ m) (hδ : (m:ℝ)^(-c) ≤ I.delta) :
    (twoLevelRemainingGaussianDrawCount I:ℝ) ≤
      2*(m:ℝ)^2+4*(twoLevelQueryCapCoefficient c*twoLevelRepetitionCoefficient c)*
        (m:ℝ)^2*(Real.log (m:ℝ))^2 := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<2) hmR
  have hlog0 : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ twoLevelQueryCapCoefficient c := by unfold twoLevelQueryCapCoefficient; positivity
  have hR : 0 ≤ twoLevelRepetitionCoefficient c := by unfold twoLevelRepetitionCoefficient; positivity
  have hq := I.queryCap_log_bound c hc hlog hδ
  have hr := I.repetitions_log_bound c hc hlog hδ
  have hqr := mul_le_mul hq hr (Nat.cast_nonneg _) (mul_nonneg hQ hlog0)
  have hbody : (r+1)*m+2*m*m ≤ 4*m*m := by
    have hrm := I.rank_le_core
    nlinarith
  have hbodyR : (((r+1)*m+2*m*m:ℕ):ℝ) ≤ 4*(m:ℝ)^2 := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,pow_two,mul_assoc] using (Nat.cast_le.mpr hbody :
      (((r+1)*m+2*m*m:ℕ):ℝ) ≤ (4*m*m:ℕ))
  have hprod := mul_le_mul hqr hbodyR (Nat.cast_nonneg _)
    (mul_nonneg (mul_nonneg hQ hlog0) (mul_nonneg hR hlog0))
  have hsmall : (2*r*m:ℕ) ≤ 2*m*m := by nlinarith [I.rank_le_core]
  have hsmallR : ((2*r*m:ℕ):ℝ) ≤ 2*(m:ℝ)^2 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,pow_two,mul_assoc] using
      (Nat.cast_le.mpr hsmall : ((2*r*m:ℕ):ℝ) ≤ (2*m*m:ℕ))
  unfold twoLevelRemainingGaussianDrawCount
  push_cast at hprod hsmallR ⊢
  nlinarith only [hprod,hsmallR]

theorem twoLevelScalarPreparationWorkCap_log_bound (I : TwoLevelProblem N m r)
    (c : ℝ) (hc : 0 ≤ c) (hm : 2 ≤ m) (hδ : (m:ℝ)^(-c) ≤ I.delta) :
    (twoLevelScalarPreparationWorkCap I:ℝ) ≤
      twoLevelScalarPreparationCoefficient c*Real.log (m:ℝ) := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<2) hmR
  have hlower : (1/2:ℝ) ≤ Real.log (m:ℝ) := family_log_two_lower.trans hlog
  have hq := I.queryCap_log_bound c hc hlog hδ
  have hr := I.repetitions_log_bound c hc hlog hδ
  have hp := twoLevelParametersProgram_work_log (m:ℝ) (by linarith)
  have hdiv : 57*Real.log (m:ℝ)/Real.log 2 = (57/Real.log 2)*Real.log (m:ℝ) := by ring
  rw [hdiv] at hp
  unfold twoLevelScalarPreparationWorkCap twoLevelScalarPreparationCoefficient
  push_cast
  nlinarith only [hq,hr,hp,hlower]

theorem twoLevelRemainingGaussianDrawCount_eventually (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta →
      (twoLevelRemainingGaussianDrawCount I:ℝ) ≤ (m:ℝ)^(2+ε) := by
  let Q := twoLevelQueryCapCoefficient c
  let R := twoLevelRepetitionCoefficient c
  have hQ : 0 ≤ Q := by dsimp [Q,twoLevelQueryCapCoefficient]; positivity
  have hR : 0 ≤ R := by dsimp [R,twoLevelRepetitionCoefficient]; positivity
  have habs := family_core_polylog_absorbed (8+4*Q*R) 2 (2+ε) 2 (by positivity) (by linarith)
  have hcast : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually habs,eventually_ge_atTop (2:ℕ)] with m hmAbs hm N r I hδ
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hlog : (1/2:ℝ) ≤ Real.log (m:ℝ) := family_log_two_lower.trans
    (Real.log_le_log (by norm_num) hmR)
  have hs := twoLevelRemainingGaussianDrawCount_bound I c hc hm hδ
  have hsq : (1:ℝ) ≤ 4*(Real.log (m:ℝ))^2 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2*(m:ℝ)^2 by positivity)
  have hbound : (twoLevelRemainingGaussianDrawCount I:ℝ) ≤
      (8+4*Q*R)*(m:ℝ)^2*(Real.log (m:ℝ))^2 := by
    dsimp [Q,R]
    nlinarith only [hs,hscaled]
  exact hbound.trans (by simpa only [Real.rpow_two,Real.rpow_natCast] using hmAbs)

theorem twoLevelGaussianDrawCount_eventually (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta →
      (Fintype.card (MainGaussianIndex N m N r 1 I.fixed.queryCap I.fixed.repetitions):ℝ) ≤
        (12*2^dyadicPaddingLevel N:ℕ)+(m:ℝ)^(2+ε) := by
  filter_upwards [twoLevelRemainingGaussianDrawCount_eventually c ε hc hε]
    with m hm N r I hδ
  rw [twoLevelGaussianDrawCount_eq,Nat.cast_add]
  exact add_le_add le_rfl (hm N r I hδ)

theorem twoLevelScalarPreparationWorkCap_eventually (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta → (twoLevelScalarPreparationWorkCap I:ℝ) ≤ (m:ℝ)^ε := by
  have habs := family_core_polylog_absorbed (twoLevelScalarPreparationCoefficient c) 1 ε 0
    (twoLevelScalarPreparationCoefficient_nonneg c hc) hε
  have hcast : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually habs,eventually_ge_atTop (2:ℕ)] with m hmAbs hm N r I hδ
  exact (twoLevelScalarPreparationWorkCap_log_bound I c hc hm hδ).trans
    (by simpa only [Real.rpow_zero,Real.rpow_one,mul_one] using hmAbs)

def twoLevelRuntimeRestWorkCap (I : TwoLevelProblem N m r) : ℕ :=
  m*(N+N)+2*N*r+
    Fintype.card (MainGaussianIndex N m N r 1 I.fixed.queryCap I.fixed.repetitions)+
    twoLevelScalarPreparationWorkCap I

def twoLevelRuntimeRestCoefficient (c : ℝ) : ℝ :=
  128+4*twoLevelQueryCapCoefficient c*twoLevelRepetitionCoefficient c+
    2*twoLevelScalarPreparationCoefficient c

theorem twoLevelRuntimeRestWorkCap_log_bound (I : TwoLevelProblem N m r)
    (c : ℝ) (hc : 0 ≤ c) (hm : 2 ≤ m) (hδ : (m:ℝ)^(-c) ≤ I.delta) :
    (twoLevelRuntimeRestWorkCap I:ℝ) ≤
      twoLevelRuntimeRestCoefficient c*(m:ℝ)*(N:ℝ)*(Real.log (m:ℝ))^2 := by
  let Q := twoLevelQueryCapCoefficient c
  let R := twoLevelRepetitionCoefficient c
  let K := twoLevelScalarPreparationCoefficient c
  have hQ : 0 ≤ Q := by dsimp [Q,twoLevelQueryCapCoefficient]; positivity
  have hR : 0 ≤ R := by dsimp [R,twoLevelRepetitionCoefficient]; positivity
  have hK : 0 ≤ K := twoLevelScalarPreparationCoefficient_nonneg c hc
  have hm1 : 1 ≤ m := by omega
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hNpos : 0 < N := (lt_of_lt_of_le (by omega : 0 < m) I.core_le_side)
  have hmn : (1:ℝ) ≤ (m:ℝ)*(N:ℝ) := by exact_mod_cast (show 1 ≤ m*N from one_le_mul hm1 hNpos)
  have hlog : (1/2:ℝ) ≤ Real.log (m:ℝ) := family_log_two_lower.trans
    (Real.log_le_log (by norm_num) hmR)
  have hlog0 : 0 ≤ Real.log (m:ℝ) := by linarith
  have hcore : (m:ℝ) ≤ N := by exact_mod_cast I.core_le_side
  have hcore2 : (m:ℝ)^2 ≤ (m:ℝ)*(N:ℝ) := by nlinarith
  have hread : m*(N+N)+2*N*r ≤ 4*m*N := by nlinarith [I.rank_le_core]
  have hreadR : ((m*(N+N)+2*N*r:ℕ):ℝ) ≤ 4*(m:ℝ)*(N:ℝ) := by exact_mod_cast hread
  have hpad : ((12*2^dyadicPaddingLevel N:ℕ):ℝ) ≤ 24*(N:ℝ) := by
    exact_mod_cast (show 12*2^dyadicPaddingLevel N ≤ 24*N by
      nlinarith [(dyadicPaddingLevel_lt_two N hNpos).le])
  have hNscale : (N:ℝ) ≤ (m:ℝ)*(N:ℝ) := by
    have hm1R : (1:ℝ) ≤ m := by exact_mod_cast hm1
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hm1R (Nat.cast_nonneg N)
  have hdraw := twoLevelRemainingGaussianDrawCount_bound I c hc hm hδ
  have hscalar := twoLevelScalarPreparationWorkCap_log_bound I c hc hm hδ
  have hdrawscale := mul_le_mul_of_nonneg_right hcore2
    (show 0 ≤ 4*(Q*R)*(Real.log (m:ℝ))^2 by positivity)
  have hscalarlog : K*Real.log (m:ℝ) ≤ 2*K*(Real.log (m:ℝ))^2 := by
    have hh := mul_nonneg (mul_nonneg hK hlog0)
      (show 0 ≤ 2*Real.log (m:ℝ)-1 by linarith)
    nlinarith only [hh]
  have hscalarscale := mul_le_mul_of_nonneg_left hmn
    (show 0 ≤ 2*K*(Real.log (m:ℝ))^2 by positivity)
  have hsq : (1:ℝ) ≤ 4*(Real.log (m:ℝ))^2 := by nlinarith
  have hconstantscale := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 30*(m:ℝ)*(N:ℝ) by positivity)
  have hpositive : 0 ≤ (m:ℝ)*(N:ℝ)*(Real.log (m:ℝ))^2 := by positivity
  unfold twoLevelRuntimeRestWorkCap twoLevelRuntimeRestCoefficient
  rw [twoLevelGaussianDrawCount_eq]
  push_cast at hreadR hpad ⊢
  dsimp [Q,R,K] at hdrawscale hscalarlog hscalarscale
  nlinarith [hreadR,hpad,hdraw,hscalar,hdrawscale,hscalarlog,hscalarscale,hconstantscale]

/-- All tape entries and all explicit preparation and factor writes fit in
the input scale, including every Gaussian sample used by the program. -/
theorem twoLevelRuntimeRestWorkCap_eventually (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta → (twoLevelRuntimeRestWorkCap I:ℝ) ≤
        (m:ℝ)*(N:ℝ)*(m:ℝ)^ε := by
  have hQ : 0 ≤ twoLevelQueryCapCoefficient c := by unfold twoLevelQueryCapCoefficient; positivity
  have hR : 0 ≤ twoLevelRepetitionCoefficient c := by unfold twoLevelRepetitionCoefficient; positivity
  have hK := twoLevelScalarPreparationCoefficient_nonneg c hc
  have hC : 0 ≤ twoLevelRuntimeRestCoefficient c := by unfold twoLevelRuntimeRestCoefficient; positivity
  have habs := family_core_polylog_absorbed (twoLevelRuntimeRestCoefficient c) 2 ε 0 hC hε
  have hcast : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually habs,eventually_ge_atTop (2:ℕ)] with m hmAbs hm N r I hδ
  have hcap := twoLevelRuntimeRestWorkCap_log_bound I c hc hm hδ
  have habs' : twoLevelRuntimeRestCoefficient c*(Real.log (m:ℝ))^2 ≤ (m:ℝ)^ε := by
    simpa only [Real.rpow_zero,mul_one,Real.rpow_two] using hmAbs
  have hs := mul_le_mul_of_nonneg_left habs' (show 0 ≤ (m:ℝ)*(N:ℝ) by positivity)
  exact hcap.trans (by convert hs using 1 <;> ring)

theorem twoLevelRuntimeRestWorkCap_power_eventually (c B ε : ℝ)
    (hc : 0 ≤ c) (hB : 1 ≤ B) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta → (N:ℝ) ≤ (m:ℝ)^B →
      (twoLevelRuntimeRestWorkCap I:ℝ) ≤ (m:ℝ)^(1+B+ε) := by
  filter_upwards [twoLevelRuntimeRestWorkCap_eventually c ε hc hε,
    eventually_ge_atTop (1:ℕ)] with m hm hm1 N r I hδ hN
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm1
  calc
    _ ≤ (m:ℝ)*(N:ℝ)*(m:ℝ)^ε := hm N r I hδ
    _ ≤ (m:ℝ)*(m:ℝ)^B*(m:ℝ)^ε := by gcongr
    _ = (m:ℝ)^(1:ℝ)*(m:ℝ)^B*(m:ℝ)^ε := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hm0,← Real.rpow_add hm0]

#print axioms twoLevelRuntimeRestWorkCap_power_eventually

end
end HierarchicalAbsoluteSpectral
