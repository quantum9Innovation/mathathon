import HierarchicalAbsoluteSpectral.GaussianCaptureBounds

/-!
Joint head/tail capture for the actual covariance-conditioned finite Gaussian
array. The head inverse is explicitly constructed from selected columns;
the tail estimate uses a union bound, without head/tail independence.
-/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix WithLp
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator

def gaussianCaptureRadius (k : ℕ) (U β : ℝ) : ℝ := (100*k*U/β)^3

theorem gaussianLinearColumns_matrix {h k r : ℕ}
    (A : Matrix (Fin h) (Fin k) ℝ) (G : Fin r → Fin k → ℝ) :
    columnsMatrix (gaussianLinearColumns A G) = A*columnsMatrix G := by
  ext i j
  simp [columnsMatrix, gaussianLinearColumns, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem gaussian_restricted_head_small_ball {h k r : ℕ}
    (A : Matrix (Fin h) (Fin k) ℝ) (e : Fin h ↪ Fin r)
    (a s : ℝ) (ha : 0 < a) (hs : 0 ≤ s)
    (hA : ∀ u : Fin h → ℝ, (∑ b, (u b)^2) = 1 →
      a^2 ≤ ∑ j, (∑ b, A b j*u b)^2) :
    (gaussianColumns k r).real
      {G | gaussianLinearColumns A (fun j => G (e j)) ∈ gaussianSquareBad h s} ≤ 2*h*s/a := by
  have hp := gaussianColumns_restrict_measurePreserving k h r e
  have hm : MeasurableSet (gaussianLinearColumns A ⁻¹' gaussianSquareBad h s) :=
    gaussianLinearColumns_measurable A (gaussianSquareBad_measurable h s)
  have heq := hp.measure_preimage hm.nullMeasurableSet
  have hb := gaussianLinearSquare_small_ball h k A a s ha hs hA
  rw [← heq] at hb
  have ht := ENNReal.toReal_mono (by finiteness) hb
  rw [ENNReal.toReal_ofReal (show 0 ≤ 2*(h : ℝ)*s/a by positivity)] at ht
  exact ht

theorem gaussian_capture_scalar_bound (k : ℕ) (a b U β : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (hba : b/a ≤ U) (hU : 1 ≤ U)
    (hβ : 0 < β) (hβ1 : β ≤ 1) :
    (b*(2*k/β))*(4*(k : ℝ)^2/(a*β)) ≤ gaussianCaptureRadius k U β := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hU0 : 0 ≤ U := by linarith
  have hU3 : U ≤ U^3 := by
    have hUU : 1 ≤ U*U := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hUU hU0]
  calc
    _ = 8*(k : ℝ)^3*(b/a)/β^2 := by field_simp <;> ring
    _ ≤ 8*(k : ℝ)^3*U/β^2 := by gcongr
    _ = (8*β)*(k : ℝ)^3*U/β^3 := by field_simp <;> ring
    _ ≤ 1000000*(k : ℝ)^3*U^3/β^3 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (by linarith : 8*β ≤ (1000000 : ℝ)) (by positivity)
      · exact hU3
      · exact hU0
      · positivity
    _ = _ := by unfold gaussianCaptureRadius; ring

def gaussianCaptureBad {h k r : ℕ}
    (A : Matrix (Fin h) (Fin k) ℝ) (e : Fin h ↪ Fin r) (a β : ℝ) :
    Set (Fin r → Fin k → ℝ) :=
  {G | gaussianLinearColumns A (fun j => G (e j)) ∈
      gaussianSquareBad h (a*β/(4*k))} ∪
    {G | (2*k/β)^2 ≤ gaussianEnergy G}

theorem gaussianCaptureBad_measurable {h k r : ℕ}
    (A : Matrix (Fin h) (Fin k) ℝ) (e : Fin h ↪ Fin r) (a β : ℝ) :
    MeasurableSet (@gaussianCaptureBad h k r A e a β) := by
  apply MeasurableSet.union
  · exact ((gaussianLinearColumns_measurable A).comp (by fun_prop))
      (gaussianSquareBad_measurable _ _)
  · exact (isClosed_le continuous_const (by unfold gaussianEnergy; fun_prop)).measurableSet

theorem gaussianCaptureBad_probability {h k r : ℕ}
    (A : Matrix (Fin h) (Fin k) ℝ) (e : Fin h ↪ Fin r) (a β : ℝ)
    (hk : 1 ≤ k) (hr : r ≤ k) (hh : h ≤ k)
    (ha : 0 < a) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hA : ∀ u : Fin h → ℝ, (∑ b, (u b)^2) = 1 →
      a^2 ≤ ∑ j, (∑ b, A b j*u b)^2) :
    (gaussianColumns k r).real (gaussianCaptureBad A e a β) ≤ β := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hhk : (h : ℝ) ≤ k := by exact_mod_cast hh
  have hrk : (r : ℝ) ≤ k := by exact_mod_cast hr
  have hhead := gaussian_restricted_head_small_ball A e a (a*β/(4*k)) ha (by positivity) hA
  have hhead' : (gaussianColumns k r).real
      {G | gaussianLinearColumns A (fun j => G (e j)) ∈
        gaussianSquareBad h (a*β/(4*k))} ≤ β/2 := by
    apply hhead.trans
    calc
      _ = (h : ℝ)*β/(2*k) := by field_simp <;> ring
      _ ≤ (k : ℝ)*β/(2*k) := by gcongr
      _ = β/2 := by field_simp <;> ring
  have htpos : 0 < (2*(k : ℝ)/β)^2 := by positivity
  have htail := gaussianEnergy_markov k r ((2*k/β)^2) htpos
  have htail' : (gaussianColumns k r).real {G | (2*k/β)^2 ≤ gaussianEnergy G} ≤ β/2 := by
    apply htail.trans
    calc
      _ ≤ (k : ℝ)^2/(2*k/β)^2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
      _ = β^2/4 := by field_simp <;> ring
      _ ≤ β/2 := by nlinarith
  exact (measureReal_union_le _ _).trans (by linarith)

/-- A non-bad raw Gaussian array has an actual full head right inverse and
the manuscript's cubic head/tail graph bound. Empty heads are included. -/
theorem gaussian_capture_of_not_bad {h k r t : ℕ}
    (A : Matrix (Fin h) (Fin k) ℝ) (D : Matrix (Fin t) (Fin k) ℝ)
    (e : Fin h ↪ Fin r) (a b U β : ℝ)
    (hk : 1 ≤ k) (hh : h ≤ k) (ha : 0 < a)
    (hD : ‖D‖ ≤ b) (hba : b/a ≤ U) (hU : 1 ≤ U)
    (hβ : 0 < β) (hβ1 : β ≤ 1)
    (G : Fin r → Fin k → ℝ) (hG : G ∉ gaussianCaptureBad A e a β) :
    columnsMatrix (gaussianLinearColumns A G)*gaussianHeadRightInverse A e G = 1 ∧
      ‖columnsMatrix (gaussianLinearColumns D G)*gaussianHeadRightInverse A e G‖ ≤
        gaussianCaptureRadius k U β := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hh' : (h : ℝ) ≤ k := by exact_mod_cast hh
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb0 : 0 ≤ b := (norm_nonneg D).trans hD
  have hhead : gaussianLinearColumns A (fun j => G (e j)) ∉
      gaussianSquareBad h (a*β/(4*k)) := fun he => hG (Or.inl he)
  have hE : gaussianEnergy G ≤ (2*k/β)^2 := le_of_lt (lt_of_not_ge (fun he => hG (Or.inr he)))
  have hs : 0 < a*β/(4*k) := by positivity
  refine ⟨gaussianHeadRightInverse_identity A e G _ hs hhead, ?_⟩
  have hH := gaussianHeadRightInverse_norm A e G _ hs hhead
  have hsqh : Real.sqrt h ≤ (k : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ h by positivity), Real.sqrt_nonneg (h : ℝ)]
  have hH' : ‖gaussianHeadRightInverse A e G‖ ≤ 4*(k : ℝ)^2/(a*β) := by
    apply hH.trans
    calc
      _ ≤ (k : ℝ)/(a*β/(4*k)) := by gcongr
      _ = _ := by field_simp <;> ring
  have htail : ‖columnsMatrix (gaussianLinearColumns D G)‖ ≤ b*(2*k/β) := by
    rw [gaussianLinearColumns_matrix]
    exact (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hD (columnsMatrix_norm_le_energy G _ (by positivity) hE)
        (norm_nonneg _) ((norm_nonneg D).trans hD))
  calc
    _ ≤ ‖columnsMatrix (gaussianLinearColumns D G)‖*‖gaussianHeadRightInverse A e G‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (b*(2*k/β))*(4*(k : ℝ)^2/(a*β)) :=
      mul_le_mul htail hH' (norm_nonneg _) (by positivity)
    _ ≤ _ := gaussian_capture_scalar_bound k a b U β hk ha hba hU hβ hβ1

/-- The explicit finite product-Gaussian event succeeds with probability at
least 1-beta and guarantees the actual right inverse and graph norm above. -/
theorem gaussian_capture_success_probability {h k r t : ℕ}
    (A : Matrix (Fin h) (Fin k) ℝ) (D : Matrix (Fin t) (Fin k) ℝ)
    (e : Fin h ↪ Fin r) (a b U β : ℝ)
    (hk : 1 ≤ k) (hr : r ≤ k) (hh : h ≤ k) (ha : 0 < a)
    (hD : ‖D‖ ≤ b) (hba : b/a ≤ U) (hU : 1 ≤ U)
    (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hA : ∀ u : Fin h → ℝ, (∑ b, (u b)^2) = 1 →
      a^2 ≤ ∑ j, (∑ b, A b j*u b)^2) :
    (gaussianColumns k r).real {G |
      columnsMatrix (gaussianLinearColumns A G)*gaussianHeadRightInverse A e G = 1 ∧
      ‖columnsMatrix (gaussianLinearColumns D G)*gaussianHeadRightInverse A e G‖ ≤
        gaussianCaptureRadius k U β} ≥ 1-β := by
  have hbad := gaussianCaptureBad_probability A e a β hk hr hh ha hβ hβ1 hA
  have hgood : (gaussianColumns k r).real (gaussianCaptureBad A e a β)ᶜ ≥ 1-β := by
    rw [measureReal_compl (gaussianCaptureBad_measurable A e a β), measureReal_univ_eq_one]
    linarith
  apply hgood.trans
  exact measureReal_mono (fun G hG =>
    gaussian_capture_of_not_bad A D e a b U β hk hh ha hD hba hU hβ hβ1 G hG) (by finiteness)

end
end HierarchicalAbsoluteSpectral
