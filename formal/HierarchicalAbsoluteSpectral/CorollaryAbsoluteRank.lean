import HierarchicalAbsoluteSpectral.MainStatementsFixed
import HierarchicalAbsoluteSpectral.MassSpectrumSingular

/-! The absolute-error slack rank is a mathematical statistic of the input.
It is never an input to the adaptive arithmetic program. In particular its
definition includes zero and uses the existing zero-indexed singular value. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
variable {n m p : ℕ}

theorem tailSingularValue_antitone (M : Matrix (Fin n) (Fin p) ℝ) :
    Antitone (tailSingularValue M) := M.toEuclideanLin.singularValues_antitone

theorem tailSingularValue_mul_core_zero
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    tailSingularValue (A*B) m = 0 := by
  apply (A*B).toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr
  rw [Matrix.toLpLin_mul]
  have hsub : LinearMap.range (A.toEuclideanLin.comp B.toEuclideanLin) ≤
      LinearMap.range A.toEuclideanLin := LinearMap.range_comp_le_range _ _
  have hr : Module.finrank ℝ (LinearMap.range A.toEuclideanLin) ≤ m := by
    simpa using A.toEuclideanLin.finrank_range_le
  exact (Submodule.finrank_mono hsub).trans hr

theorem absoluteSlackRank_exists
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (e θ : ℝ) (he : 0 < e) (hθ : 0 ≤ θ) :
    ∃ s : ℕ, s ≤ m ∧ tailSingularValue (A*B) s ≤ e/(1+θ) := by
  refine ⟨m,le_rfl,?_⟩
  rw [tailSingularValue_mul_core_zero]
  positivity

/-- Least rank in `{0,...,m}` whose next singular value is at most the
supplied absolute tolerance divided by the relative slack. -/
def absoluteSlackRank
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (e θ : ℝ) (he : 0 < e) (hθ : 0 ≤ θ) : ℕ :=
  Nat.find (absoluteSlackRank_exists A B e θ he hθ)

theorem absoluteSlackRank_le_core
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (e θ : ℝ) (he : 0 < e) (hθ : 0 ≤ θ) :
    absoluteSlackRank A B e θ he hθ ≤ m :=
  (Nat.find_spec (absoluteSlackRank_exists A B e θ he hθ)).1

theorem absoluteSlackRank_tail
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (e θ : ℝ) (he : 0 < e) (hθ : 0 ≤ θ) :
    tailSingularValue (A*B) (absoluteSlackRank A B e θ he hθ) ≤ e/(1+θ) :=
  (Nat.find_spec (absoluteSlackRank_exists A B e θ he hθ)).2

theorem absoluteSlackRank_minimal
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (e θ : ℝ) (he : 0 < e) (hθ : 0 ≤ θ) (s : ℕ) (hs : s ≤ m)
    (htail : tailSingularValue (A*B) s ≤ e/(1+θ)) :
    absoluteSlackRank A B e θ he hθ ≤ s :=
  Nat.find_min' (absoluteSlackRank_exists A B e θ he hθ) ⟨hs,htail⟩

theorem absoluteSlackRank_tail_of_le
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (e θ : ℝ) (he : 0 < e) (hθ : 0 ≤ θ) {s : ℕ}
    (hs : absoluteSlackRank A B e θ he hθ ≤ s) :
    (1+θ)*tailSingularValue (A*B) s ≤ e := by
  have hp : 0 < 1+θ := by linarith
  have ht := (tailSingularValue_antitone (A*B) hs).trans
    (absoluteSlackRank_tail A B e θ he hθ)
  simpa only [mul_comm] using (le_div_iff₀ hp).mp ht

theorem absoluteSlackRank_eq_zero_iff
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (e θ : ℝ) (he : 0 < e) (hθ : 0 ≤ θ) :
    absoluteSlackRank A B e θ he hθ = 0 ↔
      tailSingularValue (A*B) 0 ≤ e/(1+θ) := by
  constructor
  · intro h
    simpa only [h] using absoluteSlackRank_tail A B e θ he hθ
  · intro h
    exact Nat.eq_zero_of_le_zero (absoluteSlackRank_minimal A B e θ he hθ 0 (Nat.zero_le _) h)

theorem absoluteSlackRank_mono_theta
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (e θ₁ θ₂ : ℝ) (he : 0 < e) (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂)
    (hθ : θ₁ ≤ θ₂) :
    absoluteSlackRank A B e θ₁ he hθ₁ ≤ absoluteSlackRank A B e θ₂ he hθ₂ := by
  apply absoluteSlackRank_minimal A B e θ₁ he hθ₁ _
    (absoluteSlackRank_le_core A B e θ₂ he hθ₂)
  exact (absoluteSlackRank_tail A B e θ₂ he hθ₂).trans
    (div_le_div_of_nonneg_left he.le (by linarith : 0 < 1+θ₁) (by linarith))

end
end HierarchicalAbsoluteSpectral
