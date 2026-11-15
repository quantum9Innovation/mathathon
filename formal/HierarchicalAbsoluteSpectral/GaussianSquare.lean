import HierarchicalAbsoluteSpectral.GaussianColumnEvent
import Mathlib.MeasureTheory.Measure.Prod

/-! An actual finite Gaussian square-matrix small-ball bound. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal

theorem gaussianColumns_fiber_bound (m n : ℕ) (i : Fin (n+1))
    (E : Set (Fin (n+1) → Fin m → ℝ)) (hE : MeasurableSet E) (b : ℝ≥0∞)
    (hf : ∀ B : Fin n → Fin m → ℝ,
      gaussianVector m {g | i.insertNth g B ∈ E} ≤ b) :
    gaussianColumns m (n+1) E ≤ b := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Fin m → ℝ) i
  have hp := MeasurePreserving.symm e
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianVector m) i)
  have hm : MeasurableSet (e.symm ⁻¹' E) := e.symm.measurable hE
  calc
    _ = ((gaussianVector m).prod (gaussianColumns m n)) (e.symm ⁻¹' E) := by
      exact (hp.measure_preimage_emb e.symm.measurableEmbedding E).symm
    _ = ∫⁻ B, gaussianVector m ((fun g => (g,B)) ⁻¹' (e.symm ⁻¹' E))
        ∂gaussianColumns m n := Measure.prod_apply_symm hm
    _ ≤ ∫⁻ _B : Fin n → Fin m → ℝ, b ∂gaussianColumns m n := by
      apply lintegral_mono
      intro B
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact hf B
    _ = b := by simp

theorem gaussianColumnBad_probability (n : ℕ) (i : Fin (n+1))
    (s : ℝ) (hs : 0 ≤ s) :
    gaussianColumns (n+1) (n+1) (gaussianColumnBad i s) ≤ ENNReal.ofReal (2*s) := by
  apply gaussianColumns_fiber_bound (n+1) n i _ (gaussianColumnBad_measurable i s)
  intro B
  obtain ⟨u,hu,hBu⟩ := rectangular_unit_normal n B
  have horth : ∀ j, ∑ a, B j a*u a = 0 := by
    intro j
    exact congrFun hBu j
  exact (measure_mono (gaussianColumnBad_fiber_subset i s hs B u hu horth)).trans
    (by simpa only [sub_zero] using gaussianVector_projection_small_ball (n+1) u hu 0 s hs)

def gaussianSquareBad (n : ℕ) (s : ℝ) : Set (Fin n → Fin n → ℝ) :=
  ⋃ i, gaussianColumnBad i s

theorem gaussianSquareBad_iff (n : ℕ) (s : ℝ) (G : Fin n → Fin n → ℝ) :
    G ∈ gaussianSquareBad n s ↔
      ∃ x : Fin n → ℝ, ‖x‖ = 1 ∧ columnOutputEnergy G x ≤ s^2 := by
  constructor
  · rintro ⟨_,⟨i,rfl⟩,x,hx,hxi,hE⟩
    refine ⟨x, le_antisymm hx ?_, hE⟩
    simpa [Real.norm_eq_abs, hxi] using norm_le_pi_norm x i
  · rintro ⟨x,hx,hE⟩
    obtain ⟨i,hi⟩ := infinity_unit_has_unit_coordinate x hx
    exact mem_iUnion.mpr ⟨i,x,hx.le,hi,hE⟩

theorem gaussianSquareBad_measurable (n : ℕ) (s : ℝ) :
    MeasurableSet (gaussianSquareBad n s) :=
  MeasurableSet.iUnion (fun i => gaussianColumnBad_measurable i s)

/-- The probability of a unit-infinity coefficient vector with Euclidean
output norm at most s is at most 2*n*s. In particular this bounds singularity
and gives an explicit quantitative right inverse on the complementary event. -/
theorem gaussianSquare_small_ball (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    gaussianColumns n n (gaussianSquareBad n s) ≤ ENNReal.ofReal (2*n*s) := by
  cases n with
  | zero => simp [gaussianSquareBad]
  | succ n =>
      calc
        _ ≤ ∑ i : Fin (n+1), gaussianColumns (n+1) (n+1) (gaussianColumnBad i s) :=
          measure_iUnion_fintype_le _ _
        _ ≤ ∑ _i : Fin (n+1), ENNReal.ofReal (2*s) :=
          Finset.sum_le_sum (fun i _ => gaussianColumnBad_probability n i s hs)
        _ = ENNReal.ofReal (2*(↑(n+1) : ℝ)*s) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          congr 1
          ring

end
end HierarchicalAbsoluteSpectral
