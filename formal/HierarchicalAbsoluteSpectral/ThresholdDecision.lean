import HierarchicalAbsoluteSpectral.Scalars
import HierarchicalAbsoluteSpectral.ArithmeticProgram

/-!
The deterministic three-way decision logic of the safe threshold oracle.
The compressed values are used only in its proof; the implementation will
receive exact sign tests from the characteristic-coefficient routine.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section

inductive ThresholdDecision where
  | below
  | above
  | near
  deriving DecidableEq

def thresholdDecision {ι : Type*} [Fintype ι] (β : ι → ℝ) (ε : ℝ) : ThresholdDecision :=
  if ∃ i, 1 < β i then .below
  else if ∀ i, β i ≤ 1-2*ε then .above
  else .near

theorem thresholdDecision_below_safe {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ε ell : ℝ) (hell : 0 ≤ ell) (hbound : ∀ i, β i ≤ ell^2)
    (hdecision : thresholdDecision β ε = .below) : 1 < ell := by
  unfold thresholdDecision at hdecision
  split_ifs at hdecision with h
  obtain ⟨i, hi⟩ := h
  have hb := hbound i
  nlinarith

theorem thresholdDecision_above_safe {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ε ell : ℝ) (hell : 0 ≤ ell) (hε : 0 < ε) (hε' : ε ≤ 1/4)
    (hsuccess : ∃ i, (1-ε)*ell^2 ≤ β i)
    (hdecision : thresholdDecision β ε = .above) : ell < 1 := by
  unfold thresholdDecision at hdecision
  split_ifs at hdecision with hOne hLow
  obtain ⟨i, hi⟩ := hsuccess
  have hlo := hLow i
  have hp : 0 < 1-ε := by linarith
  have hs : ell^2 < 1 := by
    have hh : (1-ε)*ell^2 < (1-ε)*1 := by linarith
    exact (mul_lt_mul_iff_right₀ hp).mp hh
  nlinarith

theorem thresholdDecision_near_safe {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (ε ell : ℝ) (hell : 0 ≤ ell) (hε : 0 < ε) (hε' : ε ≤ 1/4)
    (hbound : ∀ i, β i ≤ ell^2) (hsuccess : ∃ i, (1-ε)*ell^2 ≤ β i)
    (hdecision : thresholdDecision β ε = .near) : |1-ell| ≤ 2*ε := by
  unfold thresholdDecision at hdecision
  split_ifs at hdecision with hOne hLow
  have hOne' : ∀ i, β i ≤ 1 := by
    intro i
    exact le_of_not_gt (fun h => hOne ⟨i,h⟩)
  obtain ⟨i, hi⟩ : ∃ i, 1-2*ε < β i := by simpa only [not_forall, not_le] using hLow
  have hsqlo : 1-2*ε < ell^2 := hi.trans_le (hbound i)
  obtain ⟨u, hu⟩ := hsuccess
  have hsuccess' : (1-ε)*ell^2 ≤ 1 := hu.trans (hOne' u)
  have hp : 0 < 1-ε := by linarith
  have hsqup : ell^2 ≤ 1+2*ε := by
    have hbudget : 1 ≤ (1-ε)*(1+2*ε) := by nlinarith
    exact (mul_le_mul_iff_right₀ hp).mp (hsuccess'.trans hbudget)
  have hlo : 1-2*ε ≤ ell := by
    by_contra h
    have ht : ell < 1-2*ε := lt_of_not_ge h
    have hsq := (sq_lt_sq₀ hell (by linarith : 0 ≤ 1-2*ε)).mpr ht
    nlinarith
  have hup : ell ≤ 1+2*ε := by
    by_contra h
    have ht : 1+2*ε < ell := lt_of_not_ge h
    have hsq := (sq_lt_sq₀ (by positivity : 0 ≤ 1+2*ε) hell).mpr ht
    nlinarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem thresholdDecision_near_alpha {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (α ell : ℝ) (hell : 0 ≤ ell) (hα : 0 < α) (hα' : α ≤ 1)
    (hbound : ∀ i, β i ≤ ell^2) (hsuccess : ∃ i, (1-α/100)*ell^2 ≤ β i)
    (hdecision : thresholdDecision β (α/100) = .near) : |1-ell| ≤ α := by
  have h := thresholdDecision_near_safe β (α/100) ell hell (by positivity) (by linarith)
    hbound hsuccess hdecision
  linarith

end
end HierarchicalAbsoluteSpectral
