import HierarchicalAbsoluteSpectral.CorollaryTwoLevelExponents

/-! Power calculus and the explicit five-term runtime envelope for the
two-level construction. All logarithmic and fixed multiplicative factors are
absorbed with quantified positive slack. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter
open scoped BigOperators Topology

/-- An upper power bound with every positive slack in the integer core size. -/
def HasCorePowerBound (cost : ℕ → ℝ) (E : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, cost m ≤ (m:ℝ)^(E+ε)

theorem core_polylog_absorbed (C γ a b : ℝ) (hC : 0 ≤ C) (hab : b < a) :
    ∀ᶠ m : ℕ in atTop, C*(m:ℝ)^b*(Real.log (m:ℝ))^γ ≤ (m:ℝ)^a :=
  tendsto_natCast_atTop_atTop.eventually (family_core_polylog_absorbed C γ a b hC hab)

namespace HasCorePowerBound

theorem zero (E : ℝ) : HasCorePowerBound (fun _ => 0) E := by
  intro ε hε
  exact Eventually.of_forall (fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _)

theorem rpow (E : ℝ) : HasCorePowerBound (fun m => (m:ℝ)^E) E := by
  intro ε hε
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  exact Real.rpow_le_rpow_of_exponent_le hmR (by linarith)

theorem mono {f g : ℕ → ℝ} {E : ℝ}
    (hf : HasCorePowerBound f E) (hfg : ∀ᶠ m : ℕ in atTop, g m ≤ f m) :
    HasCorePowerBound g E := by
  intro ε hε
  filter_upwards [hf ε hε,hfg] with m hm hgm
  exact hgm.trans hm

theorem exponent_mono {f : ℕ → ℝ} {E F : ℝ}
    (hf : HasCorePowerBound f E) (hEF : E ≤ F) : HasCorePowerBound f F := by
  intro ε hε
  filter_upwards [hf ε hε,eventually_ge_atTop 1] with m hm hm1
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  exact hm.trans (Real.rpow_le_rpow_of_exponent_le hmR (by linarith))

theorem const_mul {f : ℕ → ℝ} {E : ℝ} (hf : HasCorePowerBound f E)
    (C : ℝ) (hC : 0 ≤ C) : HasCorePowerBound (fun m => C*f m) E := by
  intro ε hε
  have hε2 : 0 < ε/2 := by positivity
  have ha := core_polylog_absorbed C 0 (E+ε) (E+ε/2) hC (by linarith)
  filter_upwards [hf (ε/2) hε2,ha] with m hm ha
  exact (mul_le_mul_of_nonneg_left hm hC).trans (by simpa using ha)

theorem const (C : ℝ) : HasCorePowerBound (fun _ => C) 0 := by
  intro ε hε
  have ha := core_polylog_absorbed (max C 0) 0 ε 0 (le_max_right _ _) hε
  filter_upwards [ha] with m hm
  have hh : max C 0 ≤ (m:ℝ)^ε := by simpa using hm
  simpa using (le_max_left C 0).trans hh

theorem add {f g : ℕ → ℝ} {E : ℝ}
    (hf : HasCorePowerBound f E) (hg : HasCorePowerBound g E) :
    HasCorePowerBound (fun m => f m+g m) E := by
  intro ε hε
  have hε2 : 0 < ε/2 := by positivity
  have ha := core_polylog_absorbed 2 0 (E+ε) (E+ε/2) (by norm_num) (by linarith)
  filter_upwards [hf (ε/2) hε2,hg (ε/2) hε2,ha] with m hfm hgm ha
  have hh : 2*(m:ℝ)^(E+ε/2) ≤ (m:ℝ)^(E+ε) := by simpa using ha
  exact (show f m+g m ≤ 2*(m:ℝ)^(E+ε/2) by linarith).trans hh

theorem add_max {f g : ℕ → ℝ} {E F : ℝ}
    (hf : HasCorePowerBound f E) (hg : HasCorePowerBound g F) :
    HasCorePowerBound (fun m => f m+g m) (max E F) :=
  (hf.exponent_mono (le_max_left _ _)).add (hg.exponent_mono (le_max_right _ _))

theorem mul {f g : ℕ → ℝ} {E F : ℝ}
    (hf : HasCorePowerBound f E) (hg : HasCorePowerBound g F)
    (hg0 : ∀ᶠ m : ℕ in atTop, 0 ≤ g m) :
    HasCorePowerBound (fun m => f m*g m) (E+F) := by
  intro ε hε
  have hε2 : 0 < ε/2 := by positivity
  filter_upwards [hf (ε/2) hε2,hg (ε/2) hε2,hg0,eventually_ge_atTop 1]
    with m hfm hgm hgm0 hm1
  have hmR : (0:ℝ) < m := by
    have hmR1 : (1:ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  calc
    _ ≤ (m:ℝ)^(E+ε/2)*(m:ℝ)^(F+ε/2) :=
      mul_le_mul hfm hgm hgm0 (Real.rpow_nonneg hmR.le _)
    _ = _ := by rw [← Real.rpow_add hmR]; congr 1 <;> ring

theorem finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (E : ι → ℝ) (F : ℝ) (hf : ∀ i ∈ s, HasCorePowerBound (f i) (E i))
    (hE : ∀ i ∈ s, E i ≤ F) :
    HasCorePowerBound (fun m => ∑ i ∈ s, f i m) F := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero F
  | @insert i s hi ih =>
    have hfi := (hf i (Finset.mem_insert_self i s)).exponent_mono
      (hE i (Finset.mem_insert_self i s))
    have hfs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hE j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using hfi.add hfs

theorem pow {f : ℕ → ℝ} {E : ℝ} (hf : HasCorePowerBound f E)
    (hf0 : ∀ᶠ m : ℕ in atTop, 0 ≤ f m) (k : ℕ) :
    HasCorePowerBound (fun m => (f m)^k) ((k:ℝ)*E) := by
  induction k with
  | zero => simpa using const 1
  | succ k ih =>
    have hh := ih.mul hf hf0
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hh

theorem of_eventually_polylog {f : ℕ → ℝ} {E : ℝ} (C γ : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᶠ m : ℕ in atTop, f m ≤ C*(m:ℝ)^E*(Real.log (m:ℝ))^γ) :
    HasCorePowerBound f E := by
  intro ε hε
  filter_upwards [hf,core_polylog_absorbed C γ (E+ε) E hC (by linarith)]
    with m hm hp
  exact hm.trans hp

theorem polylog (γ : ℝ) : HasCorePowerBound (fun m => (Real.log (m:ℝ))^γ) 0 := by
  apply of_eventually_polylog 1 γ (by norm_num)
  exact Eventually.of_forall (fun m => by simp)

theorem mul_polylog {f : ℕ → ℝ} {E : ℝ} (hf : HasCorePowerBound f E)
    (γ : ℝ) : HasCorePowerBound (fun m => f m*(Real.log (m:ℝ))^γ) E := by
  have hg0 : ∀ᶠ m : ℕ in atTop, 0 ≤ (Real.log (m:ℝ))^γ := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hm)) γ
  have hp := hf.mul (polylog γ) hg0
  simpa using hp

theorem one_add_log_pow (k : ℕ) :
    HasCorePowerBound (fun m => (1+Real.log (m:ℝ))^k) 0 := by
  have hlog : HasCorePowerBound (fun m => Real.log (m:ℝ)) 0 := by
    simpa using polylog 1
  have hh := (const 1).add hlog
  have hh0 : ∀ᶠ m : ℕ in atTop, 0 ≤ 1+Real.log (m:ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hlog0 := Real.log_nonneg (show (1:ℝ) ≤ m by exact_mod_cast hm)
    linarith
  simpa using hh.pow hh0 k

/-- Pull the core estimate along any diverging integer dimension family. -/
theorem along {ι : Type*} {l : Filter ι} {f : ℕ → ℝ} {E : ℝ}
    (hf : HasCorePowerBound f E) (m : ι → ℕ) (hm : Tendsto m l atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, f (m i) ≤ (m i:ℝ)^(E+ε) :=
  fun ε hε => hm.eventually (hf ε hε)

/-- The existing dimension transfer applied to a proved scalar core bound. -/
theorem construction_transfer {ι : Type*} (l : Filter ι) (m : ι → ℕ)
    (N : ι → ℝ) (cost : ℕ → ℝ) (hm : Tendsto m l atTop)
    (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i)/Real.log (m i:ℝ)) l (𝓝 (59/50:ℝ)))
    (hcost : HasCorePowerBound cost (3362/1425)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, cost (m i) ≤ (N i)^((6724/3363:ℝ)+ε) :=
  twoLevel_construction_exponent_transfer l (fun i => (m i:ℝ)) N (fun i => cost (m i))
    (tendsto_natCast_atTop_atTop.comp hm) hN hgrowth (hcost.along m hm)

end HasCorePowerBound

/-- The scalar powers arising from the actual finite leaf costs. The two
action powers include the query degree, and the fine action includes its
additional intermediate-level factor. A common polylog factor is retained
outside this sum in the theorems below. -/
def twoLevelRuntimePowerEnvelope (m : ℕ) (ζ : ℝ) : ℝ :=
  (m:ℝ)^((3362/1425:ℝ)+ζ) +
  (m:ℝ)^((9006001/4130000:ℝ)+107/600+3*ζ) +
  (m:ℝ)^((867/400:ℝ)+107/600+1/75+4*ζ) +
  (m:ℝ)^((9/4:ℝ)+ζ) +
  (m:ℝ)^((109/50:ℝ)+ζ)

theorem twoLevelRuntimePowerEnvelope_bound (m : ℕ) (ζ : ℝ)
    (hm : 1 ≤ m) (hζ : 0 ≤ ζ) :
    twoLevelRuntimePowerEnvelope m ζ ≤ 5*(m:ℝ)^((3362/1425:ℝ)+4*ζ) := by
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hc := Real.rpow_le_rpow_of_exponent_le hmR
    (show (3362/1425:ℝ)+ζ ≤ 3362/1425+4*ζ by linarith)
  have ht := Real.rpow_le_rpow_of_exponent_le hmR
    (show (9006001/4130000:ℝ)+107/600+3*ζ ≤ 3362/1425+4*ζ by nlinarith)
  have hf := Real.rpow_le_rpow_of_exponent_le hmR
    (show (867/400:ℝ)+107/600+1/75+4*ζ ≤ 3362/1425+4*ζ by nlinarith)
  have hs := Real.rpow_le_rpow_of_exponent_le hmR
    (show (9/4:ℝ)+ζ ≤ 3362/1425+4*ζ by nlinarith)
  have hi := Real.rpow_le_rpow_of_exponent_le hmR
    (show (109/50:ℝ)+ζ ≤ 3362/1425+4*ζ by nlinarith)
  unfold twoLevelRuntimePowerEnvelope
  linarith

theorem twoLevelRuntimePowerEnvelope_eventually (C γ ζ ε : ℝ)
    (hC : 0 ≤ C) (hζ : 0 ≤ ζ) (hslack : 4*ζ < ε) :
    ∀ᶠ m : ℕ in atTop,
      C*twoLevelRuntimePowerEnvelope m ζ*(Real.log (m:ℝ))^γ ≤
        (m:ℝ)^((3362/1425:ℝ)+ε) := by
  have ha := core_polylog_absorbed (5*C) γ ((3362/1425:ℝ)+ε)
    ((3362/1425:ℝ)+4*ζ) (by positivity) (by linarith)
  filter_upwards [ha,eventually_ge_atTop 1] with m ha hm
  have hp := twoLevelRuntimePowerEnvelope_bound m ζ hm hζ
  have hlog : 0 ≤ (Real.log (m:ℝ))^γ := Real.rpow_nonneg (Real.log_nonneg (by
    exact_mod_cast hm)) _
  calc
    _ ≤ C*(5*(m:ℝ)^((3362/1425:ℝ)+4*ζ))*(Real.log (m:ℝ))^γ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) hlog
    _ = (5*C)*(m:ℝ)^((3362/1425:ℝ)+4*ζ)*(Real.log (m:ℝ))^γ := by ring
    _ ≤ _ := ha

/-- The algorithmic exponent slack may be fixed before the constants and
polylog degree of the finite leaf count are known. -/
theorem exists_twoLevelRuntimePowerEnvelope_slack (ε : ℝ) (hε : 0 < ε) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ C γ : ℝ, 0 ≤ C →
      ∀ᶠ m : ℕ in atTop,
        C*twoLevelRuntimePowerEnvelope m ζ*(Real.log (m:ℝ))^γ ≤
          (m:ℝ)^((3362/1425:ℝ)+ε) := by
  refine ⟨ε/16,by positivity,?_⟩
  intro C γ hC
  exact twoLevelRuntimePowerEnvelope_eventually C γ (ε/16) ε hC (by positivity) (by linarith)

/-- Add the five concrete leaf-cost caps before absorbing their common
polylog factor. The leaf costs may count different actual program stages. -/
theorem twoLevelRuntimePowerEnvelope_of_leaf_caps
    (coarse trueAction fineAction square inputRead : ℕ → ℝ) (C γ ζ : ℝ)
    (hc : ∀ᶠ m : ℕ in atTop,
      coarse m ≤ C*(m:ℝ)^((3362/1425:ℝ)+ζ)*(Real.log (m:ℝ))^γ)
    (ht : ∀ᶠ m : ℕ in atTop,
      trueAction m ≤ C*(m:ℝ)^((9006001/4130000:ℝ)+107/600+3*ζ)*(Real.log (m:ℝ))^γ)
    (hf : ∀ᶠ m : ℕ in atTop,
      fineAction m ≤ C*(m:ℝ)^((867/400:ℝ)+107/600+1/75+4*ζ)*(Real.log (m:ℝ))^γ)
    (hs : ∀ᶠ m : ℕ in atTop,
      square m ≤ C*(m:ℝ)^((9/4:ℝ)+ζ)*(Real.log (m:ℝ))^γ)
    (hi : ∀ᶠ m : ℕ in atTop,
      inputRead m ≤ C*(m:ℝ)^((109/50:ℝ)+ζ)*(Real.log (m:ℝ))^γ) :
    ∀ᶠ m : ℕ in atTop, coarse m+trueAction m+fineAction m+square m+inputRead m ≤
      C*twoLevelRuntimePowerEnvelope m ζ*(Real.log (m:ℝ))^γ := by
  filter_upwards [hc,ht,hf,hs,hi] with m hcm htm hfm hsm him
  have hh := add_le_add (add_le_add (add_le_add (add_le_add hcm htm) hfm) hsm) him
  calc
    _ ≤ _ := hh
    _ = _ := by unfold twoLevelRuntimePowerEnvelope; ring

/-- Use an actual finite leaf-count envelope once its termwise cap is proved. -/
theorem twoLevelRuntimePowerEnvelope_cost_bound {cost : ℕ → ℝ} (C γ ζ ε : ℝ)
    (hC : 0 ≤ C) (hζ : 0 ≤ ζ) (hslack : 4*ζ < ε)
    (hleaf : ∀ᶠ m : ℕ in atTop,
      cost m ≤ C*twoLevelRuntimePowerEnvelope m ζ*(Real.log (m:ℝ))^γ) :
    ∀ᶠ m : ℕ in atTop, cost m ≤ (m:ℝ)^((3362/1425:ℝ)+ε) := by
  filter_upwards [hleaf,twoLevelRuntimePowerEnvelope_eventually C γ ζ ε hC hζ hslack]
    with m hm hp
  exact hm.trans hp

/-- Separate proved stage estimates imply the construction exponent. The
hypotheses retain each stage's own exponent rather than assuming the target
runtime estimate for their aggregate. -/
theorem twoLevelRuntimeFiniteLeafCosts_power_bound
    (coarse trueAction fineAction square inputRead : ℕ → ℝ)
    (hc : HasCorePowerBound coarse (3362/1425))
    (ht : HasCorePowerBound trueAction ((9006001/4130000:ℝ)+107/600))
    (hf : HasCorePowerBound fineAction ((867/400:ℝ)+107/600+1/75))
    (hs : HasCorePowerBound square (9/4))
    (hi : HasCorePowerBound inputRead (109/50)) :
    HasCorePowerBound
      (fun m => coarse m+trueAction m+fineAction m+square m+inputRead m) (3362/1425) := by
  exact (((hc.add (ht.exponent_mono (by norm_num))).add
    (hf.exponent_mono (by norm_num))).add (hs.exponent_mono (by norm_num))).add
      (hi.exponent_mono (by norm_num))

/-- Transfer the five finite stage costs along a dimension family after the
stage estimates have been established. -/
theorem twoLevelRuntimeFiniteLeafCosts_construction_transfer {ι : Type*}
    (l : Filter ι) (m : ι → ℕ) (N : ι → ℝ)
    (coarse trueAction fineAction square inputRead : ℕ → ℝ)
    (hm : Tendsto m l atTop) (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i)/Real.log (m i:ℝ)) l (𝓝 (59/50:ℝ)))
    (hc : HasCorePowerBound coarse (3362/1425))
    (ht : HasCorePowerBound trueAction ((9006001/4130000:ℝ)+107/600))
    (hf : HasCorePowerBound fineAction ((867/400:ℝ)+107/600+1/75))
    (hs : HasCorePowerBound square (9/4))
    (hi : HasCorePowerBound inputRead (109/50)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l,
      coarse (m i)+trueAction (m i)+fineAction (m i)+square (m i)+inputRead (m i) ≤
        (N i)^((6724/3363:ℝ)+ε) :=
  (twoLevelRuntimeFiniteLeafCosts_power_bound coarse trueAction fineAction square inputRead
    hc ht hf hs hi).construction_transfer l m N _ hm hN hgrowth

end
end HierarchicalAbsoluteSpectral
