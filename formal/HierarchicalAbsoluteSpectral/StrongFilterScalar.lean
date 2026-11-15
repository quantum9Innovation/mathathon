import HierarchicalAbsoluteSpectral.GaussianCapture
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Algebra.Order.Archimedean.Basic

/-! The manuscript's actual Chebyshev filter, with a finite stopping degree
and an explicit square-root-gap logarithmic upper bound. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Polynomial Polynomial.Chebyshev Set

def strongFilterCoordinate (α x : ℝ) : ℝ := 2*x/(1+α)-1

def strongFilterDenominator (α : ℝ) (v : ℕ) : ℝ :=
  (T ℝ (v : ℤ)).eval (strongFilterCoordinate α (1+2*α))

theorem chebyshev_monotone_above_one (v : ℕ) (x y : ℝ)
    (hx : 1 ≤ x) (hxy : x ≤ y) : (T ℝ (v : ℤ)).eval x ≤ (T ℝ (v : ℤ)).eval y := by
  have hy := hx.trans hxy
  have hrep (z : ℝ) (hz : 1 ≤ z) :
      (T ℝ (v : ℤ)).eval z = Real.cosh ((v : ℝ)*Real.arcosh z) := by
    calc
      _ = (T ℝ (v : ℤ)).eval (Real.cosh (Real.arcosh z)) := by rw [Real.cosh_arcosh hz]
      _ = _ := by simpa using T_real_cosh (Real.arcosh z) (v : ℤ)
  rw [hrep x hx, hrep y hy, Real.cosh_le_cosh,
    abs_of_nonneg (mul_nonneg (by positivity) (Real.arcosh_nonneg hx)),
    abs_of_nonneg (mul_nonneg (by positivity) (Real.arcosh_nonneg hy))]
  exact mul_le_mul_of_nonneg_left
    ((Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr hxy) (by positivity)

theorem strongFilterCoordinate_gap (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    1+α ≤ strongFilterCoordinate α (1+2*α) := by
  unfold strongFilterCoordinate
  apply (le_sub_iff_add_le).mpr
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

theorem strongFilter_arcosh_lower (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt α/2 ≤ Real.arcosh (strongFilterCoordinate α (1+2*α)) := by
  let z := Real.sqrt α
  have hz : 0 < z := Real.sqrt_pos.mpr hα
  have hz1 : z ≤ 1 := by
    nlinarith [Real.sq_sqrt hα.le, Real.sqrt_nonneg α]
  have hlog : z/2 ≤ Real.log (1+z) := by
    have hl := Real.le_log_one_add_of_nonneg hz.le
    have hzfrac : z/2 ≤ 2*z/(z+2) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    exact hzfrac.trans (by simpa [add_comm] using hl)
  have harg : 1+z ≤ (1+α)+Real.sqrt ((1+α)^2-1) := by
    have hs : z ≤ Real.sqrt ((1+α)^2-1) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    linarith
  have har : Real.log (1+z) ≤ Real.arcosh (1+α) := by
    unfold Real.arcosh
    exact Real.log_le_log (by positivity) harg
  have hmono : Real.arcosh (1+α) ≤
      Real.arcosh (strongFilterCoordinate α (1+2*α)) :=
    (Real.arcosh_le_arcosh (by positivity)
      (by have := strongFilterCoordinate_gap α hα hα1; linarith)).mpr
      (strongFilterCoordinate_gap α hα hα1)
  exact hlog.trans (har.trans hmono)

theorem strongFilterDenominator_ge_one (α : ℝ) (hα : 0 < α) (v : ℕ) :
    1 ≤ strongFilterDenominator α v := by
  apply one_le_eval_T_real
  unfold strongFilterCoordinate
  apply (le_sub_iff_add_le).mpr
  apply (le_div_iff₀ (by positivity)).mpr
  linarith

theorem strongFilterDenominator_stopping_exists (α D : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hD : 1 ≤ D) :
    ∃ v : ℕ, D ≤ strongFilterDenominator α v ∧
      (v : ℝ) ≤ 2*Real.log (2*D)/Real.sqrt α+1 := by
  let N := Nat.ceil (2*Real.log (2*D)/Real.sqrt α)
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hL : 0 ≤ Real.log (2*D) := Real.log_nonneg (by linarith)
  have hn : 2*Real.log (2*D)/Real.sqrt α ≤ (N : ℝ) := Nat.le_ceil _
  have hnlog : Real.log (2*D) ≤ (N : ℝ)*(Real.sqrt α/2) := by
    have ht := (div_le_iff₀ hs).mp hn
    nlinarith
  have hprod : Real.log (2*D) ≤
      (N : ℝ)*Real.arcosh (strongFilterCoordinate α (1+2*α)) :=
    hnlog.trans (mul_le_mul_of_nonneg_left (strongFilter_arcosh_lower α hα hα1) (by positivity))
  have hx : 1 ≤ strongFilterCoordinate α (1+2*α) :=
    (by linarith : (1 : ℝ) ≤ 1+α).trans (strongFilterCoordinate_gap α hα hα1)
  have he : 2*D ≤ Real.exp ((N : ℝ)*Real.arcosh (strongFilterCoordinate α (1+2*α))) := by
    rw [← Real.exp_log (by linarith : 0 < 2*D)]
    exact Real.exp_le_exp.mpr hprod
  refine ⟨N, ?_, ?_⟩
  · unfold strongFilterDenominator
    rw [← Real.cosh_arcosh hx, T_real_cosh, Real.cosh_eq]
    push_cast
    nlinarith [Real.exp_pos (-((N : ℝ)*Real.arcosh (strongFilterCoordinate α (1+2*α))))]
  · exact (Nat.ceil_lt_add_one (by positivity)).le

def strongFilterDegree (α D : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hD : 1 ≤ D) : ℕ :=
  Nat.find (Exists.imp (fun _ h => h.1) (strongFilterDenominator_stopping_exists α D hα hα1 hD))

theorem strongFilterDegree_stops (α D : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hD : 1 ≤ D) :
    D ≤ strongFilterDenominator α (strongFilterDegree α D hα hα1 hD) := by
  unfold strongFilterDegree
  exact Nat.find_spec (p := fun v : ℕ => D ≤ strongFilterDenominator α v) _

theorem strongFilterDegree_bound (α D : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hD : 1 ≤ D) :
    (strongFilterDegree α D hα hα1 hD : ℝ) ≤ 2*Real.log (2*D)/Real.sqrt α+1 := by
  obtain ⟨v,hv,hvbound⟩ := strongFilterDenominator_stopping_exists α D hα hα1 hD
  have hm : strongFilterDegree α D hα hα1 hD ≤ v := Nat.find_min' _ hv
  exact (by exact_mod_cast hm : (strongFilterDegree α D hα hα1 hD : ℝ) ≤ v).trans hvbound

def strongFilterPolynomial (α : ℝ) (v : ℕ) : ℝ[X] :=
  C ((strongFilterDenominator α v)⁻¹) *
    (T ℝ (v : ℤ)).comp (C (2/(1+α))*X-1)

theorem strongFilterPolynomial_eval (α : ℝ) (v : ℕ) (x : ℝ) :
    (strongFilterPolynomial α v).eval x =
      (T ℝ (v : ℤ)).eval (strongFilterCoordinate α x)/strongFilterDenominator α v := by
  have hc : (C (2/(1+α))*X-1 : ℝ[X]).eval x = strongFilterCoordinate α x := by
    simp [strongFilterCoordinate]
    ring
  simp only [strongFilterPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, hc]
  ring

theorem strongFilter_tail_bound (α : ℝ) (hα : 0 < α) (v : ℕ)
    (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1+α) :
    |(strongFilterPolynomial α v).eval x| ≤ 1/strongFilterDenominator α v := by
  have hd : 0 < strongFilterDenominator α v := by
    have := strongFilterDenominator_ge_one α hα v
    linarith
  have hc : |strongFilterCoordinate α x| ≤ 1 := by
    rw [abs_le]
    unfold strongFilterCoordinate
    constructor
    · have : 0 ≤ 2*x/(1+α) := by positivity
      linarith
    · apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
  rw [strongFilterPolynomial_eval, abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right (abs_eval_T_real_le_one _ hc) hd.le

theorem strongFilter_strong_ge_one (α : ℝ) (hα : 0 < α) (v : ℕ)
    (x : ℝ) (hx : 1+2*α ≤ x) :
    1 ≤ (strongFilterPolynomial α v).eval x := by
  have hd : 0 < strongFilterDenominator α v := by
    have := strongFilterDenominator_ge_one α hα v
    linarith
  have hc1 : 1 ≤ strongFilterCoordinate α (1+2*α) := by
    unfold strongFilterCoordinate
    apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have hc2 : strongFilterCoordinate α (1+2*α) ≤ strongFilterCoordinate α x := by
    unfold strongFilterCoordinate
    gcongr
  rw [strongFilterPolynomial_eval]
  apply (le_div_iff₀ hd).mpr
  simpa only [one_mul, strongFilterDenominator] using chebyshev_monotone_above_one v _ _ hc1 hc2

end
end HierarchicalAbsoluteSpectral
