import HierarchicalAbsoluteSpectral.Scalars

/-! The manuscript's literal final tolerances satisfy every scalar premise
of the physical, near-threshold and combined relative-error transfers. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section

def literalFinalAlpha (C h θ : ℝ) : ℝ := θ/(1000000*(C+1)*h)
def literalFinalMass (C θ : ℝ) : ℝ := θ/(1000000*(C+1))
def literalFinalB (C h θ : ℝ) : ℝ := (1+3*literalFinalAlpha C h θ)^2-1
def literalFinalX (C h θ : ℝ) : ℝ := 4*C*literalFinalAlpha C h θ*h
def literalFinalU (C h θ : ℝ) : ℝ := literalFinalB C h θ*C*h

structure LiteralFinalBudget (C h θ : ℝ) : Prop where
  alpha_positive : 0 < literalFinalAlpha C h θ
  alpha_small : literalFinalAlpha C h θ ≤ 1/1000000
  mass_positive : 0 < literalFinalMass C θ
  mass_floor : literalFinalMass C θ ≤ h/100
  mass_error : literalFinalMass C θ ≤ θ/1000
  near_nonneg : 0 ≤ literalFinalX C h θ
  near_error : literalFinalX C h θ ≤ θ/1000
  strong_nonneg : 0 ≤ literalFinalB C h θ
  strong_relaxation : 5*literalFinalB C h θ ≤ 1
  physical_nonneg : 0 ≤ literalFinalU C h θ
  physical_error : literalFinalU C h θ ≤ θ/1000

theorem literal_final_tolerance_budget (C h θ : ℝ)
    (hC : 1 ≤ C) (hh : 0 < h) (hθ : 0 < θ) (hθh : θ ≤ h) :
    LiteralFinalBudget C h θ := by
  let A : ℝ := 1000000*(C+1)
  have hA : 1000000 ≤ A := by dsimp [A]; linarith
  have hAp : 0 < A := by linarith
  have hα : 0 < literalFinalAlpha C h θ := by unfold literalFinalAlpha; positivity
  have hαsmall : literalFinalAlpha C h θ ≤ 1/1000000 := by
    unfold literalFinalAlpha
    apply (div_le_iff₀ (mul_pos hAp hh)).mpr
    change θ ≤ (1/1000000 : ℝ)*(A*h)
    nlinarith [mul_le_mul_of_nonneg_right hA hh.le]
  have he : 0 < literalFinalMass C θ := by unfold literalFinalMass; positivity
  have heh : literalFinalMass C θ ≤ h/100 := by
    change θ/A ≤ h/100
    apply (div_le_div_iff₀ hAp (by norm_num)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hA hh.le]
  have heθ : literalFinalMass C θ ≤ θ/1000 := by
    change θ/A ≤ θ/1000
    exact div_le_div_of_nonneg_left hθ.le (by norm_num) (by linarith)
  have hratio : C/A ≤ 1/1000000 := by
    apply (div_le_iff₀ hAp).mpr
    dsimp [A]
    linarith
  have hv : C*literalFinalAlpha C h θ*h ≤ θ/1000000 := by
    have hid : C*literalFinalAlpha C h θ*h = (C/A)*θ := by
      unfold literalFinalAlpha
      dsimp [A]
      field_simp
      <;> ring
    rw [hid]
    have hh' := mul_le_mul_of_nonneg_right hratio hθ.le
    nlinarith
  have hb0 : 0 ≤ literalFinalB C h θ := by unfold literalFinalB; nlinarith
  have hb : literalFinalB C h θ ≤ 7*literalFinalAlpha C h θ := by
    unfold literalFinalB
    have hprod := mul_nonneg hα.le (show 0 ≤ 1-9*literalFinalAlpha C h θ by linarith)
    nlinarith
  have hu0 : 0 ≤ literalFinalU C h θ := by unfold literalFinalU; positivity
  have hu : literalFinalU C h θ ≤ θ/1000 := by
    have hh' := mul_le_mul_of_nonneg_right hb (show 0 ≤ C*h by positivity)
    change literalFinalB C h θ*C*h ≤ θ/1000
    nlinarith
  refine ⟨hα,hαsmall,he,heh,heθ,?_,?_,hb0,?_,hu0,hu⟩
  · unfold literalFinalX
    positivity
  · unfold literalFinalX
    nlinarith
  · nlinarith

theorem literal_final_combined_error_budget (C h θ : ℝ)
    (hC : 1 ≤ C) (hh : 0 < h) (hθ : 0 < θ) (hθh : θ ≤ h) (hθ1 : θ ≤ 1) :
    ((1+literalFinalU C h θ+literalFinalMass C θ)/(1-literalFinalU C h θ))*
      ((1+literalFinalX C h θ)/(1-literalFinalX C h θ))*(1/(1-literalFinalMass C θ)) ≤ (1+θ)^2 := by
  have hb := literal_final_tolerance_budget C h θ hC hh hθ hθh
  exact final_error_budget θ (literalFinalU C h θ) (literalFinalX C h θ) (literalFinalMass C θ)
    hθ.le hθ1 hb.physical_nonneg hb.physical_error hb.near_nonneg hb.near_error
    hb.mass_positive.le hb.mass_error

theorem LiteralFinalBudget.relaxation {C h θ : ℝ} (hb : LiteralFinalBudget C h θ)
    (κ : ℝ) (hκ : κ ≤ 5) : κ*literalFinalB C h θ ≤ 1 := by
  have hh := mul_le_mul_of_nonneg_right hκ hb.strong_nonneg
  exact hh.trans hb.strong_relaxation

theorem LiteralFinalBudget.near_accuracy {C h θ : ℝ} (hb : LiteralFinalBudget C h θ)
    (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ 5) : literalFinalAlpha C h θ ≤ 1/(100*κ) := by
  apply (le_div_iff₀ (by positivity : 0 < 100*κ)).mpr
  have hh := mul_le_mul_of_nonneg_left hκ hb.alpha_positive.le
  nlinarith [hb.alpha_small]

theorem LiteralFinalBudget.denominators {C h θ : ℝ} (hb : LiteralFinalBudget C h θ)
    (hθ : θ ≤ 1) :
    0 < 1-literalFinalU C h θ ∧ 0 < 1-literalFinalX C h θ ∧ 0 < 1-literalFinalMass C θ := by
  have hu := hb.physical_error
  have hx := hb.near_error
  have he := hb.mass_error
  constructor
  · linarith
  constructor <;> linarith

end
end HierarchicalAbsoluteSpectral
