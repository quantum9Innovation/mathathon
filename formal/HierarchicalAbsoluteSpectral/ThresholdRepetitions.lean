import HierarchicalAbsoluteSpectral.ThresholdKrylovGaussian
import HierarchicalAbsoluteSpectral.ThresholdSearchCap

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

def repeatedGaussianColumns (k r N : ℕ) : Measure (Fin N → Fin r → Fin k → ℝ) :=
  Measure.pi (fun _ => gaussianColumns k r)

instance repeatedGaussianColumns_isProbability (k r N : ℕ) :
    IsProbabilityMeasure (repeatedGaussianColumns k r N) := by
  unfold repeatedGaussianColumns
  infer_instance

theorem independent_trials_all_bad (k r N : ℕ) (bad : Set (Fin r → Fin k → ℝ)) :
    (repeatedGaussianColumns k r N).real {G | ∀ i, G i ∈ bad} =
      ((gaussianColumns k r).real bad)^N := by
  have heq : {G : Fin N → Fin r → Fin k → ℝ | ∀ i, G i ∈ bad} =
      Set.pi Set.univ (fun _ => bad) := by
    ext G
    simp
  rw [measureReal_def, heq, repeatedGaussianColumns, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow, measureReal_def]

theorem independent_trials_failure_le (k r N : ℕ) (bad : Set (Fin r → Fin k → ℝ))
    (β : ℝ) (hβ : 0 ≤ β) (hbad : (gaussianColumns k r).real bad ≤ β) :
    (repeatedGaussianColumns k r N).real {G | ∀ i, G i ∈ bad} ≤ β^N := by
  rw [independent_trials_all_bad]
  exact pow_le_pow_left₀ (measureReal_nonneg) hbad _

/-- The repetition count is computed by the actual scalar halving program.
This gives an explicit finite count without using a logarithm primitive. -/
theorem repetition_halving_cap (δ : ℝ) (hδ : 0 < δ) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1/2) :
    β^(leastHalvings 1 δ hδ) ≤ δ := by
  have hp := pow_le_pow_left₀ hβ hβ' (leastHalvings 1 δ hδ)
  have hs := leastHalvings_spec 1 δ hδ
  have heq : (1/2 : ℝ)^(leastHalvings 1 δ hδ) = 1/(2:ℝ)^(leastHalvings 1 δ hδ) := by
    simp only [div_pow, one_pow]
  exact hp.trans (heq ▸ hs)

end
end HierarchicalAbsoluteSpectral
