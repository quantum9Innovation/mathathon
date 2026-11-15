import HierarchicalAbsoluteSpectral.ThresholdKrylov
import HierarchicalAbsoluteSpectral.StrongFilterDiagonal

set_option backward.isDefEq.respectTransparency false

/-! The additive Ritz lower bound follows from a constructed polynomial
graph. This file isolates the finite weighted energy argument, including the
middle spectral band where no tail attenuation is required. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp Polynomial
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {k h r : ℕ}

theorem sum_injected_coordinates (e : Fin h ↪ Fin k) (y : Fin k → ℝ) :
    (∑ i, if ∃ s, e s = i then (y i)^2 else 0) = ∑ s, (y (e s))^2 := by
  classical
  rw [← Finset.sum_filter]
  have hset : Finset.univ.filter (fun i => ∃ s, e s = i) = Finset.univ.image e := by
    ext i
    simp
  rw [hset, Finset.sum_image]
  exact fun a ha b hb hab => e.injective hab

theorem diagonal_ritz_energy (d : Fin k → ℝ) (e : Fin h ↪ Fin k)
    (bad : Fin k → Prop) [DecidablePred bad] (target ε : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) (htarget : 0 ≤ target)
    (hd : ∀ i, 0 ≤ d i) (hhead : ∀ s, target ≤ d (e s))
    (hheadgood : ∀ s, ¬bad (e s))
    (hgood : ∀ i, ¬bad i → (1-ε)*target^2 ≤ (d i)^2)
    (z : Fin h → ℝ) (y : Fin k → ℝ) (hcoords : ∀ s, y (e s) = z s)
    (hsmall : (∑ i, if bad i then (y i)^2 else 0) ≤ ε*∑ s, (z s)^2) :
    (1-ε)*target^2*(∑ i, (y i)^2) ≤ ∑ i, (d i)^2*(y i)^2 := by
  classical
  have hpoint (i : Fin k) :
      ε*target^2*(if ∃ s, e s = i then (y i)^2 else 0)-
        target^2*(if bad i then (y i)^2 else 0) ≤
      ((d i)^2-(1-ε)*target^2)*(y i)^2 := by
    by_cases hh : ∃ s, e s = i
    · obtain ⟨s,rfl⟩ := hh
      simp only [show ∃ s', e s' = e s from ⟨s,rfl⟩, ↓reduceIte, hheadgood s]
      have hs := sq_le_sq₀ htarget (hd (e s)) |>.mpr (hhead s)
      nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (y (e s)))]
    · by_cases hb : bad i
      · simp only [hh, hb, ↓reduceIte, mul_zero, zero_sub]
        have hp : 0 ≤ (d i)^2+ε*target^2 := by positivity
        nlinarith [mul_nonneg hp (sq_nonneg (y i))]
      · simp only [hh, hb, ↓reduceIte, mul_zero, sub_self]
        exact mul_nonneg (sub_nonneg.mpr (hgood i hb)) (sq_nonneg _)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, sub_mul] at hs
  rw [sum_injected_coordinates e y] at hs
  simp only [hcoords] at hs
  have hb := mul_le_mul_of_nonneg_left hsmall (sq_nonneg target)
  nlinarith only [hs,hb]

def diagonalFilteredGraph (d : Fin k → ℝ) (p : ℝ[X]) (e : Fin h ↪ Fin k)
    (Ω : Matrix (Fin k) (Fin r) ℝ) (H : Matrix (Fin r) (Fin h) ℝ) :
    Matrix (Fin k) (Fin h) ℝ :=
  Matrix.diagonal (fun i => p.eval (d i))*Ω*H*
    Matrix.diagonal (fun s => (p.eval (d (e s)))⁻¹)

theorem diagonalFilteredGraph_head (d : Fin k → ℝ) (p : ℝ[X]) (e : Fin h ↪ Fin k)
    (Ω : Matrix (Fin k) (Fin r) ℝ) (H : Matrix (Fin r) (Fin h) ℝ)
    (hhead : (Ω.submatrix e id)*H = 1) (hp : ∀ s, p.eval (d (e s)) ≠ 0)
    (s c : Fin h) : diagonalFilteredGraph d p e Ω H (e s) c = (1 : Core h) s c := by
  have hh := congrFun (congrFun hhead s) c
  change (∑ b, Ω (e s) b*H b c) = (1 : Core h) s c at hh
  unfold diagonalFilteredGraph
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, mul_assoc]
  rw [← Finset.mul_sum, hh]
  by_cases hsc : s = c
  · subst c
    simp [hp s]
  · simp [Matrix.one_apply, hsc]

theorem diagonalFilteredGraph_injective (d : Fin k → ℝ) (p : ℝ[X]) (e : Fin h ↪ Fin k)
    (Ω : Matrix (Fin k) (Fin r) ℝ) (H : Matrix (Fin r) (Fin h) ℝ)
    (hhead : (Ω.submatrix e id)*H = 1) (hp : ∀ s, p.eval (d (e s)) ≠ 0) :
    Function.Injective (diagonalFilteredGraph d p e Ω H).toEuclideanLin := by
  intro z w hw
  apply PiLp.ext
  intro s
  have hh := congrArg (fun v : EuclideanSpace ℝ (Fin k) => v (e s)) hw
  simpa [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    diagonalFilteredGraph_head d p e Ω H hhead hp, Matrix.one_apply, ite_mul] using hh

end
end HierarchicalAbsoluteSpectral
