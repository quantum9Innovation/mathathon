import HierarchicalAbsoluteSpectral.GaussianSquare

/-! Column-distance capture for covariance-conditioned Gaussian starts. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix WithLp
open scoped ENNReal NNReal

theorem gaussianVector_projection_small_ball_of_lower (n : ℕ) (v : Fin n → ℝ)
    (a s : ℝ) (ha : 0 < a) (hs : 0 ≤ s) (hv : a^2 ≤ ∑ j, (v j)^2) :
    gaussianVector n {x | |∑ j, x j*v j| ≤ s} ≤ ENNReal.ofReal (2*s/a) := by
  let q : ℝ := ‖toLp 2 v‖
  have hq2 : ∑ j, (v j)^2 = q^2 := (EuclideanSpace.real_norm_sq_eq (toLp 2 v)).symm
  have hqa : a ≤ q := by
    have hq0 : 0 ≤ q := norm_nonneg _
    nlinarith
  have hq : 0 < q := ha.trans_le hqa
  let u : Fin n → ℝ := q⁻¹ • v
  have hu : ∑ j, (u j)^2 = 1 := by
    simp only [u, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, hq2]
    field_simp
  have hsub : {x : Fin n → ℝ | |∑ j, x j*v j| ≤ s} ⊆
      {x | |(∑ j, x j*u j)-0| ≤ s/a} := by
    intro x hx
    change |∑ j, x j*u j-0| ≤ s/a
    change |∑ j, x j*v j| ≤ s at hx
    have heq : (∑ j, x j*u j) = q⁻¹*(∑ j, x j*v j) := by
      simp only [u, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [sub_zero, heq, abs_mul, abs_of_pos (inv_pos.mpr hq)]
    calc
      _ ≤ q⁻¹*s := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hq.le)
      _ ≤ a⁻¹*s := mul_le_mul_of_nonneg_right (inv_anti₀ ha hqa) hs
      _ = s/a := by ring
  exact (measure_mono hsub).trans
    (by simpa [mul_div_assoc] using
      gaussianVector_projection_small_ball n u hu 0 (s/a) (div_nonneg hs ha.le))

def gaussianLinearColumns {h k r : ℕ} (A : Matrix (Fin h) (Fin k) ℝ)
    (G : Fin r → Fin k → ℝ) : Fin r → Fin h → ℝ :=
  fun j => A *ᵥ G j

theorem gaussianLinearColumns_measurable {h k r : ℕ}
    (A : Matrix (Fin h) (Fin k) ℝ) : Measurable (@gaussianLinearColumns h k r A) := by
  unfold gaussianLinearColumns Matrix.mulVec dotProduct
  fun_prop

theorem gaussianLinearColumns_insertNth {h k n : ℕ}
    (A : Matrix (Fin h) (Fin k) ℝ) (i : Fin (n+1))
    (g : Fin k → ℝ) (B : Fin n → Fin k → ℝ) :
    gaussianLinearColumns A (i.insertNth g B) =
      i.insertNth (A *ᵥ g) (gaussianLinearColumns A B) := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j,rfl⟩ <;>
    simp [gaussianLinearColumns]

theorem gaussianLinearColumnBad_probability (k n : ℕ)
    (A : Matrix (Fin (n+1)) (Fin k) ℝ) (i : Fin (n+1))
    (a s : ℝ) (ha : 0 < a) (hs : 0 ≤ s)
    (hA : ∀ u : Fin (n+1) → ℝ, (∑ b, (u b)^2) = 1 →
      a^2 ≤ ∑ j, (∑ b, A b j*u b)^2) :
    gaussianColumns k (n+1)
      (gaussianLinearColumns A ⁻¹' gaussianColumnBad i s) ≤ ENNReal.ofReal (2*s/a) := by
  apply gaussianColumns_fiber_bound k n i _
    ((gaussianLinearColumns_measurable A) (gaussianColumnBad_measurable i s))
  intro B
  obtain ⟨u,hu,hBu⟩ := rectangular_unit_normal n (gaussianLinearColumns A B)
  have horth : ∀ j, ∑ b, gaussianLinearColumns A B j b*u b = 0 := by
    intro j
    exact congrFun hBu j
  let v : Fin k → ℝ := fun j => ∑ b, A b j*u b
  have hsub : {g : Fin k → ℝ | gaussianLinearColumns A (i.insertNth g B) ∈
      gaussianColumnBad i s} ⊆ {g | |∑ j, g j*v j| ≤ s} := by
    intro g hg
    change gaussianLinearColumns A (i.insertNth g B) ∈ gaussianColumnBad i s at hg
    change |∑ j, g j*v j| ≤ s
    rw [gaussianLinearColumns_insertNth] at hg
    have hb := gaussianColumnBad_fiber_subset i s hs (gaussianLinearColumns A B) u hu horth hg
    change |∑ b, (A *ᵥ g) b*u b| ≤ s at hb
    have heq : (∑ b, (A *ᵥ g) b*u b) = ∑ j, g j*v j := by
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, v]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro b hb
      ring
    simpa only [heq] using hb
  exact (measure_mono hsub).trans
    (gaussianVector_projection_small_ball_of_lower k v a s ha hs (hA u hu))

theorem gaussianLinearSquare_small_ball (h k : ℕ)
    (A : Matrix (Fin h) (Fin k) ℝ) (a s : ℝ) (ha : 0 < a) (hs : 0 ≤ s)
    (hA : ∀ u : Fin h → ℝ, (∑ b, (u b)^2) = 1 →
      a^2 ≤ ∑ j, (∑ b, A b j*u b)^2) :
    gaussianColumns k h
      (gaussianLinearColumns A ⁻¹' gaussianSquareBad h s) ≤ ENNReal.ofReal (2*h*s/a) := by
  cases h with
  | zero => simp [gaussianSquareBad]
  | succ n =>
      calc
        _ ≤ ∑ i : Fin (n+1), gaussianColumns k (n+1)
            (gaussianLinearColumns A ⁻¹' gaussianColumnBad i s) := by
          simpa only [gaussianSquareBad, Set.preimage_iUnion] using
            measure_iUnion_fintype_le (gaussianColumns k (n+1))
              (fun i => gaussianLinearColumns A ⁻¹' gaussianColumnBad i s)
        _ ≤ ∑ _i : Fin (n+1), ENNReal.ofReal (2*s/a) :=
          Finset.sum_le_sum (fun i _ => gaussianLinearColumnBad_probability k n A i a s ha hs hA)
        _ = ENNReal.ofReal (2*(↑(n+1) : ℝ)*s/a) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          congr 1
          ring

end
end HierarchicalAbsoluteSpectral
