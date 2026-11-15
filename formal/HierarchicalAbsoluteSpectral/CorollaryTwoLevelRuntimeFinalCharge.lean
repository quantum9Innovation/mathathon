import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalPowers
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalKernels
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelBudgets

/-! Fixed numerical charges for the actual two-level core. Their exponent
is strictly below the coarse-support exponent, including all ceilings. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter

theorem HasCorePowerBound.natCeil {f : ℕ → ℝ} {E : ℝ}
    (hf : HasCorePowerBound f E) (hE : 0 ≤ E)
    (hf0 : ∀ᶠ m : ℕ in atTop, 0 ≤ f m) :
    HasCorePowerBound (fun m => (⌈f m⌉₊:ℝ)) E := by
  apply (hf.add ((HasCorePowerBound.const 1).exponent_mono hE)).mono
  filter_upwards [hf0] with m hm
  exact (Nat.ceil_lt_add_one hm).le

def twoLevelRuntimeFinalSlack : ℝ := 1/1000000
def twoLevelRuntimeActionExponent : ℝ := 867/400+1/75+twoLevelRuntimeFinalSlack
def twoLevelRuntimeDegreeExponent : ℝ := 107/600+twoLevelRuntimeFinalSlack
def twoLevelRuntimeCoreExponent : ℝ := twoLevelRuntimeDegreeExponent+twoLevelRuntimeActionExponent

def twoLevelRuntimeActionCharge (m : ℕ) : ℕ := ⌈(m:ℝ)^twoLevelRuntimeActionExponent⌉₊
def twoLevelRuntimeDegreeCharge (m : ℕ) : ℕ := ⌈(m:ℝ)^twoLevelRuntimeDegreeExponent⌉₊
def twoLevelRuntimeSmallCharge (C : ℝ) (m : ℕ) : ℕ :=
  ⌈2000*(C+1)*(m:ℝ)^twoLevelRuntimeGlobalExponent*(1+Real.log (m:ℝ))⌉₊
def twoLevelRuntimeQueryCharge (c : ℝ) (m : ℕ) : ℕ :=
  ⌈twoLevelQueryCapCoefficient c*Real.log (m:ℝ)⌉₊
def twoLevelRuntimeRepetitionCharge (c : ℝ) (m : ℕ) : ℕ :=
  ⌈twoLevelRepetitionCoefficient c*Real.log (m:ℝ)⌉₊

def twoLevelRuntimeFinalCoreCharge (c C : ℝ) (m : ℕ) : ℕ :=
  1000*(twoLevelRuntimeQueryCharge c m+1)*(twoLevelRuntimeRepetitionCharge c m+1)*
    ((twoLevelRuntimeDegreeCharge m+1)*(twoLevelRuntimeActionCharge m+1)+
      2*twoLevelRuntimeSmallCharge C m+1)

theorem twoLevelRuntimeCoreExponent_bounds :
    0 ≤ twoLevelRuntimeActionExponent ∧ 0 ≤ twoLevelRuntimeDegreeExponent ∧
      twoLevelRuntimeGlobalExponent ≤ twoLevelRuntimeCoreExponent ∧
      twoLevelRuntimeCoreExponent < (3362:ℝ)/1425 := by
  norm_num [twoLevelRuntimeActionExponent,twoLevelRuntimeDegreeExponent,twoLevelRuntimeCoreExponent,
    twoLevelRuntimeFinalSlack,twoLevelRuntimeGlobalExponent]

theorem twoLevelRuntimeActionCharge_power :
    HasCorePowerBound (fun m => (twoLevelRuntimeActionCharge m:ℝ)) twoLevelRuntimeActionExponent :=
  (HasCorePowerBound.rpow _).natCeil twoLevelRuntimeCoreExponent_bounds.1
    (Eventually.of_forall (fun m => Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem twoLevelRuntimeDegreeCharge_power :
    HasCorePowerBound (fun m => (twoLevelRuntimeDegreeCharge m:ℝ)) twoLevelRuntimeDegreeExponent :=
  (HasCorePowerBound.rpow _).natCeil twoLevelRuntimeCoreExponent_bounds.2.1
    (Eventually.of_forall (fun m => Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem twoLevelRuntimeSmallCharge_power (C : ℝ) (hC : 0 < C) :
    HasCorePowerBound (fun m => (twoLevelRuntimeSmallCharge C m:ℝ)) twoLevelRuntimeGlobalExponent := by
  have hlog : HasCorePowerBound (fun m => 1+Real.log (m:ℝ)) 0 := by
    simpa only [pow_one] using HasCorePowerBound.one_add_log_pow 1
  have hlog0 : ∀ᶠ m : ℕ in atTop, 0 ≤ 1+Real.log (m:ℝ) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
    have hl := Real.log_nonneg (show (1:ℝ) ≤ m by exact_mod_cast hm)
    linarith
  have hp := ((HasCorePowerBound.rpow twoLevelRuntimeGlobalExponent).const_mul
    (2000*(C+1)) (by positivity)).mul hlog hlog0
  have hp' : HasCorePowerBound
      (fun m => 2000*(C+1)*(m:ℝ)^twoLevelRuntimeGlobalExponent*(1+Real.log (m:ℝ)))
      twoLevelRuntimeGlobalExponent := by simpa only [add_zero] using hp
  apply hp'.natCeil (by norm_num [twoLevelRuntimeGlobalExponent])
  filter_upwards [hlog0] with m hm
  positivity

theorem twoLevelRuntimeQueryCharge_power (c : ℝ) (hc : 0 ≤ c) :
    HasCorePowerBound (fun m => (twoLevelRuntimeQueryCharge c m:ℝ)) 0 := by
  have hl2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hC : 0 ≤ twoLevelQueryCapCoefficient c := by unfold twoLevelQueryCapCoefficient; positivity
  have hlog : HasCorePowerBound (fun m => Real.log (m:ℝ)) 0 := by
    simpa only [Real.rpow_one] using HasCorePowerBound.polylog 1
  apply (hlog.const_mul _ hC).natCeil le_rfl
  filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
  exact mul_nonneg hC (Real.log_nonneg (by exact_mod_cast hm))

theorem twoLevelRuntimeRepetitionCharge_power (c : ℝ) (hc : 0 ≤ c) :
    HasCorePowerBound (fun m => (twoLevelRuntimeRepetitionCharge c m:ℝ)) 0 := by
  have hl2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hC : 0 ≤ twoLevelRepetitionCoefficient c := by
    unfold twoLevelRepetitionCoefficient twoLevelQueryCapCoefficient
    positivity
  have hlog : HasCorePowerBound (fun m => Real.log (m:ℝ)) 0 := by
    simpa only [Real.rpow_one] using HasCorePowerBound.polylog 1
  apply (hlog.const_mul _ hC).natCeil le_rfl
  filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
  exact mul_nonneg hC (Real.log_nonneg (by exact_mod_cast hm))

theorem twoLevelRuntimeFinalCoreCharge_power (c C : ℝ) (hc : 0 ≤ c) (hC : 0 < C) :
    HasCorePowerBound (fun m => (twoLevelRuntimeFinalCoreCharge c C m:ℝ)) twoLevelRuntimeCoreExponent := by
  have hA := twoLevelRuntimeActionCharge_power.add
    ((HasCorePowerBound.const 1).exponent_mono twoLevelRuntimeCoreExponent_bounds.1)
  have hQ := twoLevelRuntimeDegreeCharge_power.add
    ((HasCorePowerBound.const 1).exponent_mono twoLevelRuntimeCoreExponent_bounds.2.1)
  have hAQ := hQ.mul hA (Eventually.of_forall (fun m => by positivity))
  have hB := ((twoLevelRuntimeSmallCharge_power C hC).const_mul 2 (by norm_num)).exponent_mono
    twoLevelRuntimeCoreExponent_bounds.2.2.1
  have hE : 0 ≤ twoLevelRuntimeCoreExponent := add_nonneg
    twoLevelRuntimeCoreExponent_bounds.2.1 twoLevelRuntimeCoreExponent_bounds.1
  have hsum := (hAQ.add hB).add ((HasCorePowerBound.const 1).exponent_mono hE)
  have hqc := (twoLevelRuntimeQueryCharge_power c hc).add (HasCorePowerBound.const 1)
  have hrc := (twoLevelRuntimeRepetitionCharge_power c hc).add (HasCorePowerBound.const 1)
  have hqr := hqc.mul hrc (Eventually.of_forall (fun m => by positivity))
  have hall := (hqr.const_mul 1000 (by norm_num)).mul hsum
    (Eventually.of_forall (fun m => by positivity))
  simpa only [twoLevelRuntimeFinalCoreCharge,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
    zero_add,add_zero,twoLevelRuntimeCoreExponent] using hall

theorem twoLevelRuntimeFinalCoreCharge_eventually (c C : ℝ) (hc : 0 ≤ c) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop, (twoLevelRuntimeFinalCoreCharge c C m:ℝ) ≤ (m:ℝ)^(3362/1425:ℝ) := by
  have hmargin := twoLevelRuntimeCoreExponent_bounds.2.2.2
  have hsmall := twoLevelRuntimeFinalCoreCharge_power c C hc hC
    (((3362/1425:ℝ)-twoLevelRuntimeCoreExponent)/2) (by linarith)
  filter_upwards [hsmall,eventually_ge_atTop (1:ℕ)] with m hm hm1
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  exact hm.trans (Real.rpow_le_rpow_of_exponent_le hmR (by linarith))

end
end HierarchicalAbsoluteSpectral
