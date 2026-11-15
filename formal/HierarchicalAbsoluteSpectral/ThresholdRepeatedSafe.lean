import HierarchicalAbsoluteSpectral.ThresholdRepetitions
import HierarchicalAbsoluteSpectral.MinMaxAffine

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator ENNReal
variable {k : ℕ}

def ThresholdDecisionSafe (ell ε : ℝ) : ThresholdDecision → Prop
  | .below => 1 < ell
  | .above => ell < 1
  | .near => |1-ell| ≤ 2*ε

theorem thresholdDecision_safe {ι : Type*} [Fintype ι] (β : ι → ℝ) (ell ε : ℝ)
    (hell : 0 ≤ ell) (hε : 0 < ε) (hε' : ε ≤ 1/4)
    (hbound : ∀ i, β i ≤ ell^2) (hsuccess : ∃ i, (1-ε)*ell^2 ≤ β i) :
    ThresholdDecisionSafe ell ε (thresholdDecision β ε) := by
  cases hd : thresholdDecision β ε with
  | below => exact thresholdDecision_below_safe β ε ell hell hbound hd
  | above => exact thresholdDecision_above_safe β ε ell hell hε hε' hsuccess hd
  | near => exact thresholdDecision_near_safe β ε ell hell hε hε' hbound hsuccess hd

def repeatedComputedDecision (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (j : Fin k) (ε : ℝ) (N : ℕ)
    (G : Fin N → Fin (j.val+1) → Fin k → ℝ) : ThresholdDecision :=
  thresholdDecision (fun i => computedKrylovRitzValue kernels T hT actions q S (G i) j) ε

theorem repeatedComputedDecision_safe_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.PosSemidef) (actions : ∀ b, MatrixAction T b)
    (S Sinv : Core k) (hSinv : Sinv*S = 1) (j : Fin k)
    (htarget : 0 < orderedEigenvalue T hT.isHermitian j)
    (a b U β ε : ℝ) (ha : 0 < a) (hInv : ‖Sinv‖ ≤ 1/a)
    (hS : ‖S‖ ≤ b) (hba : b/a ≤ U) (hU : 1 ≤ U)
    (hβ : 0 < β) (hβ' : β ≤ 1) (hε : 0 < ε) (hε' : ε ≤ 1/4) (q : ℕ)
    (hstop : 10*gaussianCaptureRadius k U β/ε ≤ strongFilterDenominator (ε/100) q)
    (N : ℕ) :
    (repeatedGaussianColumns k (j.val+1) N).real {G |
      ThresholdDecisionSafe (orderedEigenvalue T hT.isHermitian j) ε
        (repeatedComputedDecision kernels T hT.isHermitian actions q S j ε N G)} ≥ 1-β^N := by
  let bad := krylovCaptureBad T hT.isHermitian S j a β
  have hm : MeasurableSet bad := krylovCaptureBad_measurable T hT.isHermitian S j a β
  have hall : MeasurableSet {G : Fin N → Fin (j.val+1) → Fin k → ℝ | ∀ i, G i ∈ bad} := by
    simpa only [Set.setOf_forall, Set.preimage] using
      MeasurableSet.iInter (fun i => hm.preimage (measurable_pi_apply i))
  have hbad := independent_trials_failure_le k (j.val+1) N bad β hβ.le
    (krylovCaptureBad_probability T hT.isHermitian S Sinv hSinv j a β ha hInv hβ hβ')
  have hgood : (repeatedGaussianColumns k (j.val+1) N).real
      {G | ∀ i, G i ∈ bad}ᶜ ≥ 1-β^N := by
    rw [measureReal_compl hall, probReal_univ]
    linarith
  apply hgood.trans
  apply measureReal_mono _ (by finiteness)
  intro G hG
  have hex : ∃ i, G i ∉ bad := by simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] using hG
  obtain ⟨i,hi⟩ := hex
  apply thresholdDecision_safe _ _ ε htarget.le hε hε'
  · exact fun i => computedKrylovRitzValue_always_safe kernels T hT actions q S (G i) j
  · exact ⟨i,computedKrylovRitzValue_of_not_bad kernels T hT actions S j htarget
      a b U β ε ha hS hba hU hβ hβ' hε (by linarith) q hstop (G i) hi⟩

end
end HierarchicalAbsoluteSpectral
