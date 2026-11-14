import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Scalar obligations in `hierarchical-absolute-spectral.pdf`.
The names and constants follow equations (9), (13), (17), and (22).
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false

noncomputable section

def defectConstant : ℕ → ℝ
  | 0 => 36
  | j + 1 => 100 * (defectConstant j + 1)

def accuracyScale (L : ℕ) : ℝ := 10^6 * (defectConstant L + 1)

theorem defectConstant_ge_one (L : ℕ) : 1 ≤ defectConstant L := by
  induction L with
  | zero => norm_num [defectConstant]
  | succ L ih => simp only [defectConstant]; linarith

theorem defectConstant_closed (L : ℕ) :
    defectConstant L = (36 + 100 / 99) * (100 : ℝ)^L - 100 / 99 := by
  induction L with
  | zero => norm_num [defectConstant]
  | succ L ih => rw [defectConstant, ih, pow_succ]; ring

/-- The exact scalar identity used to obtain the ideal quadratic defect in Lemma 5. -/
theorem absolute_root_defect (x η : ℝ) (hη : 0 < η) :
    (Real.sqrt (x^2 + η^2) + η) -
        x^2 / (Real.sqrt (x^2 + η^2) + η) = 2 * η := by
  have hs := Real.sq_sqrt (show 0 ≤ x^2 + η^2 by positivity)
  have hp : 0 < Real.sqrt (x^2 + η^2) + η := by positivity
  field_simp
  nlinarith

/-- The scalar inequality in the min--max portion of Lemma 6. -/
theorem near_scalar_inequality (κ α c : ℝ)
    (hκ : 1 ≤ κ) (hκ' : κ ≤ 5) (hα : 0 < α)
    (hα' : α ≤ 1 / (100 * κ)) (hc : -1 ≤ c) (hc' : c ≤ α) :
    c ≤ (α / (1 - κ * α^2)) * (1 - κ * c^2) := by
  have hκpos : 0 < κ := by linarith
  have hαsmall : α ≤ 1 / 100 := by
    have := (le_div_iff₀ (by positivity : 0 < 100 * κ)).mp hα'
    nlinarith
  have hκα : κ * α ≤ 1 / 100 := by
    have := (le_div_iff₀ (by positivity : 0 < 100 * κ)).mp hα'
    nlinarith
  have hd : 0 < 1 - κ * α^2 := by nlinarith
  have hx : 0 ≤ α - c := by linarith
  have hy : 0 ≤ 1 + κ * α * c := by nlinarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).mpr
  have := mul_nonneg hx hy
  nlinarith

/-- Algebraic heart of the strong transfer, with each symbol a quadratic form value. -/
theorem relaxed_strong_transfer_scalar
    (F K KFΚ D κ C h b : ℝ)
    (hquad : 0 ≤ KFΚ) (hb : 0 ≤ b) (hκb : κ * b ≤ 1)
    (hinvariant : F - κ * KFΚ ≤ C * h * D)
    (hstrong : KFΚ - 2 * K ≤ b * F) :
    -(b * C * h * D) ≤ 2 * K := by
  have := mul_nonneg (sub_nonneg.mpr hκb) hquad
  have := mul_le_mul_of_nonneg_left hinvariant hb
  nlinarith

/-- Rearranging the final physical quadratic inequality in Lemma 6. -/
theorem physical_transfer_scalar (s t normSq u ε : ℝ)
    (hu : u < 1)
    (hphysical : t * normSq - s ≥ -(u + ε) * t * normSq - u * s) :
    s ≤ ((1 + u + ε) / (1 - u)) * t * normSq := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1 - u)).mpr
  nlinarith

/-- The combined physical, near-threshold and mass error budget in Section 5.
The hypotheses are looser than u<=7theta/10^6, x<=4theta/10^6,
epsilon=theta/10^9 used in the manuscript.
-/
theorem final_error_budget (θ u x ε : ℝ)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hu : 0 ≤ u) (hu' : u ≤ θ / 1000)
    (hx : 0 ≤ x) (hx' : x ≤ θ / 1000)
    (he : 0 ≤ ε) (he' : ε ≤ θ / 1000) :
    ((1 + u + ε) / (1 - u)) * ((1 + x) / (1 - x)) * (1 / (1 - ε)) ≤
      (1 + θ)^2 := by
  have hdu : 0 < 1 - u := by linarith
  have hdx : 0 < 1 - x := by linarith
  have hde : 0 < 1 - ε := by linarith
  have hphys : (1 + u + ε) / (1 - u) ≤ 1 + θ / 100 := by
    apply (div_le_iff₀ hdu).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ') hu]
  have hnear : (1 + x) / (1 - x) ≤ 1 + θ / 100 := by
    apply (div_le_iff₀ hdx).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ') hx]
  have hmass : 1 / (1 - ε) ≤ 1 + θ / 100 := by
    apply (div_le_iff₀ hde).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ') he]
  calc
    _ ≤ ((1 + θ / 100) * (1 + θ / 100)) * (1 + θ / 100) :=
      mul_le_mul (mul_le_mul hphys hnear (by positivity) (by positivity))
        hmass (by positivity) (by positivity)
    _ ≤ (1 + θ)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hθ') (sq_nonneg θ)]

theorem threshold_error_budget (θ u x ε t σ : ℝ)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hu : 0 ≤ u) (hu' : u ≤ θ / 1000)
    (hx : 0 ≤ x) (hx' : x ≤ θ / 1000)
    (he : 0 ≤ ε) (he' : ε ≤ θ / 1000)
    (ht : t ≤ ((1+x)/(1-x)) * (1/(1-ε)) * σ^2) :
    ((1+u+ε)/(1-u)) * t ≤ ((1+θ)*σ)^2 := by
  have hdu : 0 < 1-u := by linarith
  have hphys : 0 ≤ (1+u+ε)/(1-u) := by positivity
  have hbudget := final_error_budget θ u x ε hθ hθ' hu hu' hx hx' he he'
  calc
    _ ≤ ((1+u+ε)/(1-u)) * (((1+x)/(1-x)) * (1/(1-ε)) * σ^2) :=
      mul_le_mul_of_nonneg_left ht hphys
    _ = (((1+u+ε)/(1-u)) * ((1+x)/(1-x)) * (1/(1-ε))) * σ^2 := by ring
    _ ≤ (1+θ)^2 * σ^2 := mul_le_mul_of_nonneg_right hbudget (sq_nonneg σ)
    _ = ((1+θ)*σ)^2 := by ring

def dStar : ℝ := (3 * Real.sqrt 5 - 5) / 10
def alphaStar : ℝ := (3 * Real.sqrt 5 - 5) / 2
def savingStar : ℝ := (7 - 3 * Real.sqrt 5) / 8

theorem optimized_parameters :
    5 * dStar * (1 + dStar) = 1 ∧
    alphaStar * (1 + dStar) = 1 ∧
    1 - alphaStar = 4 * savingStar ∧
    dStar / (4 * (1 + dStar)) = savingStar ∧
    1 / (4 * (1 + dStar)^2) - dStar / (1 + dStar) = savingStar := by
  have hs : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
  have hp := Real.sqrt_nonneg (5 : ℝ)
  have hd : 0 < 1 + dStar := by dsimp [dStar]; linarith
  have hbalance : 5 * dStar * (1 + dStar) = 1 := by dsimp [dStar]; nlinarith
  have hK : dStar / (4 * (1 + dStar)) = savingStar := by
    apply (div_eq_iff (by positivity : 4 * (1 + dStar) ≠ 0)).mpr
    dsimp [dStar, savingStar]
    nlinarith
  refine ⟨hbalance, ?_, ?_, hK, ?_⟩
  · dsimp [dStar, alphaStar]; nlinarith
  · dsimp [alphaStar, savingStar]; ring
  · rw [← hK]
    field_simp
    nlinarith [hbalance]

theorem optimized_parameter_in_family :
    1/8 < dStar ∧ dStar < (Real.sqrt 2 - 1)/2 := by
  have h5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp5 := Real.sqrt_nonneg (5:ℝ)
  have hp2 := Real.sqrt_nonneg (2:ℝ)
  have hlo : (223:ℝ)/100 < Real.sqrt 5 := by nlinarith
  have hhi : Real.sqrt 5 < (224:ℝ)/100 := by nlinarith
  have htwo : (14:ℝ)/10 < Real.sqrt 2 := by nlinarith
  dsimp [dStar]
  constructor <;> linarith

end
end HierarchicalAbsoluteSpectral
