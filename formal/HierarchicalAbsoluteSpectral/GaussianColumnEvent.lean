import HierarchicalAbsoluteSpectral.GaussianBasics
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
The column-distance argument is formulated with a compact infinity-unit
sphere in the coefficient space. This avoids a measurable choice of a
normal vector: each fixed fiber may use its own deterministic normal.
-/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix WithLp
open scoped ENNReal NNReal RealInnerProductSpace

def columnCombination {m n : ℕ} (G : Fin n → Fin m → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun j => ∑ i, x i*G i j

def columnOutputEnergy {m n : ℕ} (G : Fin n → Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j, (columnCombination G x j)^2

def gaussianColumnBad {m n : ℕ} (i : Fin n) (s : ℝ) : Set (Fin n → Fin m → ℝ) :=
  {G | ∃ x : Fin n → ℝ, ‖x‖ ≤ 1 ∧ |x i| = 1 ∧ columnOutputEnergy G x ≤ s^2}

theorem gaussianColumnBad_isClosed {m n : ℕ} (i : Fin n) (s : ℝ) :
    IsClosed (@gaussianColumnBad m n i s) := by
  let B := Metric.closedBall (0 : Fin n → ℝ) 1
  letI : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let C : Set ((Fin n → Fin m → ℝ) × B) :=
    {p | |p.2.val i| = 1 ∧ columnOutputEnergy p.1 p.2.val ≤ s^2}
  have hC : IsClosed C := by
    change IsClosed ({p : (Fin n → Fin m → ℝ) × B | |p.2.val i| = 1} ∩
      {p | columnOutputEnergy p.1 p.2.val ≤ s^2})
    apply IsClosed.inter
    · exact isClosed_eq
        (continuous_abs.comp ((continuous_apply i).comp
          (continuous_subtype_val.comp continuous_snd))) continuous_const
    · apply isClosed_le _ continuous_const
      change Continuous (fun p : (Fin n → Fin m → ℝ) × B =>
        ∑ j, (∑ a, p.2.val a*p.1 a j)^2)
      apply continuous_finset_sum
      intro j hj
      apply Continuous.pow
      apply continuous_finset_sum
      intro a ha
      exact ((continuous_apply a).comp (continuous_subtype_val.comp continuous_snd)).mul
        ((continuous_apply j).comp ((continuous_apply a).comp continuous_fst))
  have himg : Prod.fst '' C = @gaussianColumnBad m n i s := by
    ext G
    constructor
    · rintro ⟨⟨G',x⟩, hx, rfl⟩
      refine ⟨x.val, ?_, hx⟩
      have hmem : x.val ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := x.property
      simpa only [Metric.mem_closedBall, dist_zero_right] using hmem
    · rintro ⟨x,hx,hxi,hE⟩
      refine ⟨(G, ⟨x, ?_⟩), ⟨hxi,hE⟩, rfl⟩
      simpa [B, Metric.mem_closedBall, dist_zero_right] using hx
  rw [← himg]
  exact isClosedMap_fst_of_compactSpace C hC

theorem gaussianColumnBad_measurable {m n : ℕ} (i : Fin n) (s : ℝ) :
    MeasurableSet (@gaussianColumnBad m n i s) :=
  (gaussianColumnBad_isClosed i s).measurableSet

theorem infinity_unit_has_unit_coordinate {n : ℕ} (x : Fin n → ℝ) (hx : ‖x‖ = 1) :
    ∃ i, |x i| = 1 := by
  by_contra! h
  have hl : ‖x‖ < 1 := (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr fun i => by
    have hi : |x i| ≤ 1 := by simpa [Real.norm_eq_abs, hx] using norm_le_pi_norm x i
    exact lt_of_le_of_ne hi (h i)
  linarith

/-- A deterministic unit normal to any n vectors in R^(n+1). -/
theorem rectangular_unit_normal (n : ℕ) (B : Matrix (Fin n) (Fin (n+1)) ℝ) :
    ∃ u : Fin (n+1) → ℝ, (∑ j, (u j)^2) = 1 ∧ B *ᵥ u = 0 := by
  let f := B.mulVecLin
  have hker : f.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨v,hv,hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hv0 : B *ᵥ v = 0 := hv
  let q : ℝ := ‖toLp 2 v‖
  have hq : q ≠ 0 := by
    intro h
    have hv' : (toLp 2 v : EuclideanSpace ℝ (Fin (n+1))) = 0 := norm_eq_zero.mp h
    apply hvne
    simpa using congrArg ofLp hv'
  have hq2 : ∑ j, (v j)^2 = q^2 := (EuclideanSpace.real_norm_sq_eq (toLp 2 v)).symm
  let u : Fin (n+1) → ℝ := q⁻¹ • v
  refine ⟨u, ?_, ?_⟩
  · simp only [u, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, hq2]
    field_simp
  · change f (q⁻¹ • v) = 0
    rw [map_smul, show f v = 0 from hv0, smul_zero]

theorem columnCombination_normal_identity {m n : ℕ}
    (i : Fin (n+1)) (g : Fin m → ℝ) (B : Fin n → Fin m → ℝ)
    (u : Fin m → ℝ) (x : Fin (n+1) → ℝ)
    (horth : ∀ j, ∑ a, B j a*u a = 0) :
    (∑ a, columnCombination (i.insertNth g B) x a*u a) = x i*(∑ a, g a*u a) := by
  unfold columnCombination
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Fin.sum_univ_succAbove _ i]
  simp_rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, mul_assoc,
    ← Finset.mul_sum, horth, mul_zero, Finset.sum_const_zero, add_zero]

/-- Every point in a bad-column fiber lies in a one-dimensional slab. -/
theorem gaussianColumnBad_fiber_subset {n : ℕ} (i : Fin (n+1)) (s : ℝ) (hs : 0 ≤ s)
    (B : Fin n → Fin (n+1) → ℝ) (u : Fin (n+1) → ℝ)
    (hu : ∑ a, (u a)^2 = 1) (horth : ∀ j, ∑ a, B j a*u a = 0) :
    {g : Fin (n+1) → ℝ | i.insertNth g B ∈ gaussianColumnBad i s} ⊆
      {g | |∑ a, g a*u a| ≤ s} := by
  rintro g ⟨x,hx,hxi,hE⟩
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (columnCombination (i.insertNth g B) x) u
  rw [hu, mul_one, columnCombination_normal_identity i g B u x horth] at hc
  have hxi2 : (x i)^2 = 1 := by nlinarith [sq_abs (x i)]
  rw [mul_pow, hxi2, one_mul] at hc
  have hsq : (∑ a, g a*u a)^2 ≤ s^2 := hc.trans hE
  exact (sq_le_sq₀ (abs_nonneg _) hs).mp (by simpa using hsq)

end
end HierarchicalAbsoluteSpectral
