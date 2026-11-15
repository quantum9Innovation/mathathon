import HierarchicalAbsoluteSpectral.NeumannMass
import HierarchicalAbsoluteSpectral.DegreeSelection

/-! A logarithmic degree for the fixed even Neumann mass polynomial. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open scoped MatrixOrder
variable {k : ℕ}

def neumannCount (ε : ℝ) (hε : 0 < ε) : ℕ :=
  2^(dyadicStoppingLevel (1/2) ε (by norm_num) (by norm_num) hε)

theorem neumannCount_error (ε b : ℝ) (hε : 0 < ε) (hb : 0 ≤ b) (hb' : b ≤ 1/2) :
    b^(2*neumannCount ε hε+1) ≤ ε := by
  have hs := dyadicStoppingLevel_stops (1/2) ε (by norm_num) (by norm_num) hε
  calc
    _ ≤ (1/2:ℝ)^(2*neumannCount ε hε+1) := pow_le_pow_left₀ hb hb' _
    _ ≤ (1/2:ℝ)^(neumannCount ε hε) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ ≤ ε := hs

theorem neumannCount_bound (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    (neumannCount ε hε : ℝ) ≤ 1+4*Real.log (1/ε) := by
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (by norm_num : (0:ℝ) ≤ 1)
    norm_num at h
    linarith
  have hL : 0 < Real.log (1/ε) := by
    apply Real.log_pos
    exact (one_lt_div hε).mpr hε'
  unfold neumannCount
  cases hs : dyadicStoppingLevel (1/2) ε (by norm_num) (by norm_num) hε with
  | zero =>
    norm_num
    linarith [Real.log_neg hε hε']
  | succ s =>
    have hmin : ε < (1/2:ℝ)^(2^s) := by
      apply lt_of_not_ge
      apply Nat.find_min (p := fun t : ℕ => (1/2:ℝ)^(2^t) ≤ ε) _
      change s < dyadicStoppingLevel (1/2) ε (by norm_num) (by norm_num) hε
      omega
    have hl := Real.log_lt_log hε hmin
    rw [Real.log_pow, show (1/2:ℝ) = 2⁻¹ by norm_num, Real.log_inv] at hl
    push_cast at hl ⊢
    have hp := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0:ℝ) ≤ 2^s)
    rw [one_div, Real.log_inv] at hL ⊢
    rw [pow_succ]
    nlinarith

def constructedNeumannMass (G : Core k) (ε : ℝ) (hε : 0 < ε) : Core k :=
  evenNeumannMass G (neumannCount ε hε)

theorem constructedNeumannMass_posDef (G : Core k) (hG : G.IsHermitian)
    (ε : ℝ) (hε : 0 < ε) : (constructedNeumannMass G ε hε).PosDef :=
  evenNeumannMass_posDef G hG _

theorem constructedNeumannMass_relative (G : Core k) (hG : G.PosDef)
    (ε : ℝ) (hε : 0 < ε)
    (hlo : (1/2:ℝ) • (1 : Core k) ≤ G) (hup : G ≤ (3/2:ℝ) • (1 : Core k)) :
    (1-ε) • G⁻¹ ≤ constructedNeumannMass G ε hε ∧
      constructedNeumannMass G ε hε ≤ (1+ε) • G⁻¹ := by
  apply evenNeumannMass_relative_of_bounds G hG _ (1/2) ε (by norm_num)
  · convert hlo using 1; norm_num
  · convert hup using 1; norm_num
  · exact neumannCount_error ε (1/2) hε (by norm_num) (by norm_num)

end
end HierarchicalAbsoluteSpectral
