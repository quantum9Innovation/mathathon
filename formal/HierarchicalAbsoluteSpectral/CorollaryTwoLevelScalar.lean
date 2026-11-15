import HierarchicalAbsoluteSpectral.RuntimeFamilyBounds
import HierarchicalAbsoluteSpectral.ScalarConstruction

/-! Counted scalar preparation for the two-level example.  Rational powers
are rounded to dyadics by integer powers and scalar halving comparisons.
No logarithm or general root occurs in the executed program. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

def twoLevelIntegerPowerProgram (x : ℝ) : ℕ → ArithmeticProgram ℝ
  | 0 => .pure 1
  | a+1 => do
      let y ← twoLevelIntegerPowerProgram x a
      mul y x

@[simp] theorem twoLevelIntegerPowerProgram_eval (x : ℝ) (a : ℕ) :
    (twoLevelIntegerPowerProgram x a).eval = x^a := by
  induction a with
  | zero => rfl
  | succ a ih => simp [twoLevelIntegerPowerProgram,ih,pow_succ]

@[simp] theorem twoLevelIntegerPowerProgram_work (x : ℝ) (a : ℕ) :
    (twoLevelIntegerPowerProgram x a).work = a := by
  induction a with
  | zero => rfl
  | succ a ih => simp [twoLevelIntegerPowerProgram,ih]

@[simp] theorem twoLevelIntegerPowerProgram_admissible (x : ℝ) (a : ℕ) :
    (twoLevelIntegerPowerProgram x a).admissible := by
  induction a with
  | zero => trivial
  | succ a ih => simp [twoLevelIntegerPowerProgram,ih]

def twoLevelRoundedExponent (m : ℝ) (a b : ℕ) : ℕ :=
  leastHalvings (m^a) 1 (by norm_num)/b+1

def twoLevelRoundedPower (m : ℝ) (a b : ℕ) : ℝ :=
  1/(2 : ℝ)^twoLevelRoundedExponent m a b

def twoLevelRoundedPowerProgram (m : ℝ) (a b : ℕ) : ArithmeticProgram ℝ := do
  let x ← twoLevelIntegerPowerProgram m a
  let n ← scalarHalving x 1 (by norm_num)
  dyadicScaleProgram (n/b+1)

@[simp] theorem twoLevelRoundedPowerProgram_eval (m : ℝ) (a b : ℕ) :
    (twoLevelRoundedPowerProgram m a b).eval = twoLevelRoundedPower m a b := by
  simp [twoLevelRoundedPowerProgram,(scalarHalving_checked (m^a) 1 (by norm_num)).1,
    twoLevelRoundedPower,twoLevelRoundedExponent]

@[simp] theorem twoLevelRoundedPowerProgram_admissible (m : ℝ) (a b : ℕ) :
    (twoLevelRoundedPowerProgram m a b).admissible := by
  simp only [twoLevelRoundedPowerProgram,admissible_bind,twoLevelIntegerPowerProgram_admissible,
    twoLevelIntegerPowerProgram_eval,dyadicScaleProgram_admissible,and_true,true_and]
  exact (scalarHalving_checked (m^a) 1 (by norm_num)).2.2

theorem twoLevelRoundedPowerProgram_work (m : ℝ) (a b : ℕ) :
    (twoLevelRoundedPowerProgram m a b).work =
      a+2*leastHalvings (m^a) 1 (by norm_num)+1+twoLevelRoundedExponent m a b := by
  simp only [twoLevelRoundedPowerProgram,work_bind,twoLevelIntegerPowerProgram_work,
    twoLevelIntegerPowerProgram_eval,dyadicScaleProgram_work,
    (scalarHalving_checked (m^a) 1 (by norm_num)).1,
    (scalarHalving_checked (m^a) 1 (by norm_num)).2.1,twoLevelRoundedExponent]
  omega

theorem twoLevelRoundedPowerProgram_work_le (m : ℝ) (a b : ℕ) :
    (twoLevelRoundedPowerProgram m a b).work ≤
      a+3*leastHalvings (m^a) 1 (by norm_num)+2 := by
  rw [twoLevelRoundedPowerProgram_work]
  unfold twoLevelRoundedExponent
  have h := Nat.div_le_self (leastHalvings (m^a) 1 (by norm_num)) b
  omega

theorem twoLevelRoundedPower_positive (m : ℝ) (a b : ℕ) :
    0 < twoLevelRoundedPower m a b := by unfold twoLevelRoundedPower; positivity

theorem twoLevelRoundedExponent_bounds (m : ℝ) (a b : ℕ) (hb : 1 ≤ b) :
    leastHalvings (m^a) 1 (by norm_num) ≤ b*twoLevelRoundedExponent m a b ∧
      b*twoLevelRoundedExponent m a b ≤ leastHalvings (m^a) 1 (by norm_num)+b := by
  unfold twoLevelRoundedExponent
  let n := leastHalvings (m^a) 1 (by norm_num)
  have hmod := Nat.mod_lt n (show 0 < b by omega)
  have hdiv := Nat.div_add_mod n b
  change n ≤ b*(n/b+1) ∧ b*(n/b+1) ≤ n+b
  rw [Nat.mul_add,Nat.mul_one]
  constructor <;> omega

/-- A factor of four is uniform in both numerator and denominator. -/
theorem twoLevelRoundedPower_bounds (m : ℝ) (a b : ℕ) (hm : 1 ≤ m) (hb : 1 ≤ b) :
    m^(-(a:ℝ)/(b:ℝ))/4 ≤ twoLevelRoundedPower m a b ∧
      twoLevelRoundedPower m a b ≤ m^(-(a:ℝ)/(b:ℝ)) := by
  let n := leastHalvings (m^a) 1 (by norm_num)
  let k := twoLevelRoundedExponent m a b
  have hm0 : 0 < m := by linarith
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : 1 ≤ m^a := one_le_pow₀ hm
  have hx0 : 0 < m^a := by positivity
  have hstop : m^a ≤ (2 : ℝ)^n := by
    have hs := leastHalvings_spec (m^a) 1 (by norm_num)
    exact (div_le_iff₀ (by positivity)).mp hs |>.trans_eq (one_mul _)
  have hloglow := Real.log_le_log hx0 hstop
  rw [Real.log_pow,Real.log_pow] at hloglow
  have hloghigh : (n : ℝ) ≤ 1+(a : ℝ)*Real.log m/Real.log 2 := by
    have ht := leastHalvings_log_bound (m^a) 1 (by norm_num)
    simpa only [div_one,max_eq_right hx,Real.log_pow] using ht
  have hk := twoLevelRoundedExponent_bounds m a b hb
  have hkn : (n : ℝ) ≤ (b : ℝ)*k := by exact_mod_cast hk.1
  have hnk : (b : ℝ)*k ≤ (n : ℝ)+b := by exact_mod_cast hk.2
  have hklo : (a : ℝ)*Real.log m ≤ (b : ℝ)*(k : ℝ)*Real.log 2 := by
    nlinarith
  have hkhi : (b : ℝ)*(k : ℝ)*Real.log 2 ≤ (a : ℝ)*Real.log m+2*b*Real.log 2 := by
    have hn := (le_div_iff₀ hl2).mp (show (n : ℝ)-1 ≤ (a : ℝ)*Real.log m/Real.log 2 by linarith)
    nlinarith
  have hval := twoLevelRoundedPower_positive m a b
  have hlogval : Real.log (twoLevelRoundedPower m a b) = -(k : ℝ)*Real.log 2 := by
    unfold twoLevelRoundedPower
    rw [one_div,Real.log_inv,Real.log_pow]
    dsimp [k]
    ring
  have hid : 0 < m^(-(a:ℝ)/(b:ℝ)) := Real.rpow_pos_of_pos hm0 _
  constructor
  · apply (Real.log_le_log_iff (by positivity) hval).mp
    rw [Real.log_div hid.ne' (by norm_num),Real.log_rpow hm0,hlogval,
      show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
    have he : -(a:ℝ)/(b:ℝ)*Real.log m = -((a:ℝ)*Real.log m)/(b:ℝ) := by ring
    rw [he]
    apply (mul_le_mul_iff_of_pos_right hb0).mp
    nlinarith [div_mul_cancel₀ (-((a : ℝ)*Real.log m)) hb0.ne']
  · apply (Real.log_le_log_iff hval hid).mp
    rw [Real.log_rpow hm0,hlogval]
    have he : -(a:ℝ)/(b:ℝ)*Real.log m = -((a:ℝ)*Real.log m)/(b:ℝ) := by ring
    rw [he]
    exact (le_div_iff₀ hb0).mpr (by nlinarith)

theorem twoLevelRoundedPower_ratio_le (m : ℝ) (a b c d : ℕ)
    (hm : 1 ≤ m) (hb : 1 ≤ b) (hd : 1 ≤ d) :
    twoLevelRoundedPower m a b/twoLevelRoundedPower m c d ≤
      4*m^(-(a:ℝ)/(b:ℝ)+(c:ℝ)/(d:ℝ)) := by
  have hm0 : 0 < m := by linarith
  have ha := twoLevelRoundedPower_bounds m a b hm hb
  have hc := twoLevelRoundedPower_bounds m c d hm hd
  calc
    _ ≤ m^(-(a:ℝ)/(b:ℝ))/(m^(-(c:ℝ)/(d:ℝ))/4) :=
      div_le_div₀ (Real.rpow_nonneg hm0.le _) ha.2 (by positivity) hc.1
    _ = 4*(m^(-(a:ℝ)/(b:ℝ))/m^(-(c:ℝ)/(d:ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_sub hm0]; congr 2 <;> ring

theorem twoLevelRoundedPowerProgram_work_log (m : ℝ) (a b : ℕ) (hm : 1 ≤ m) :
    ((twoLevelRoundedPowerProgram m a b).work : ℝ) ≤
      (a : ℝ)+5+3*a*Real.log m/Real.log 2 := by
  have hw : ((twoLevelRoundedPowerProgram m a b).work : ℝ) ≤
      (a : ℝ)+3*leastHalvings (m^a) 1 (by norm_num)+2 := by
    exact_mod_cast twoLevelRoundedPowerProgram_work_le m a b
  have hx : 1 ≤ m^a := one_le_pow₀ hm
  have hl : (leastHalvings (m^a) 1 (by norm_num) : ℝ) ≤
      1+(a : ℝ)*Real.log m/Real.log 2 := by
    simpa only [div_one,max_eq_right hx,Real.log_pow] using
      leastHalvings_log_bound (m^a) 1 (by norm_num)
  calc
    _ ≤ (a : ℝ)+3*(1+(a : ℝ)*Real.log m/Real.log 2)+2 := by linarith
    _ = _ := by ring

end
end HierarchicalAbsoluteSpectral
