import HierarchicalAbsoluteSpectral.ThresholdKrylovGraph

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp Polynomial
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {k r : ℕ}

def krylovHeadEmbedding (j : Fin k) : Fin (j.val+1) ↪ Fin k :=
  ⟨spectralHeadIndex j, fun a b hab => Fin.ext (congrArg (fun i : Fin k => i.val) hab)⟩

theorem ritz_filter_tail_budget (ε R : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1) (hR : 1 ≤ R)
    (q : ℕ) (hstop : 10*R/ε ≤ strongFilterDenominator (ε/100) q) :
    (1/strongFilterDenominator (ε/100) q)*R ≤ ε/10 := by
  have hd : 0 < strongFilterDenominator (ε/100) q :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
      (strongFilterDenominator_ge_one (ε/100) (by positivity) q)
  have hs := (div_le_iff₀ hε).mp hstop
  rw [one_div, inv_mul_eq_div]
  exact (div_le_iff₀ hd).mpr (by nlinarith)

theorem diagonal_inner_square (d : Fin k → ℝ) (v : EuclideanSpace ℝ (Fin k)) :
    ⟪v,(Matrix.diagonal (fun i => (d i)^2)).toEuclideanLin v⟫_ℝ =
      ∑ i, (d i)^2*(v i)^2 := by
  rw [← quadratic_eq_inner]
  simp only [quadratic, Matrix.mulVec_diagonal, dotProduct, Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The explicit normalized polynomial/Gaussian graph has the desired
Rayleigh bound. The only random-event inputs are the concrete selected-head
inverse identity and graph norm supplied by `gaussian_capture_of_not_bad`. -/
theorem diagonal_krylov_graph_rayleigh
    (d : Fin k → ℝ) (hd : Antitone d) (hd0 : ∀ i, 0 ≤ d i)
    (j : Fin k) (htarget : 0 < d j) (ε R : ℝ)
    (hε : 0 < ε) (hε' : ε ≤ 1) (hR : 1 ≤ R) (q : ℕ)
    (hstop : 10*R/ε ≤ strongFilterDenominator (ε/100) q)
    (Ω : Matrix (Fin k) (Fin r) ℝ) (H : Matrix (Fin r) (Fin (j.val+1)) ℝ)
    (hhead : (Ω.submatrix (krylovHeadEmbedding j) id)*H = 1) (hΩ : ‖Ω*H‖ ≤ R)
    (z : EuclideanSpace ℝ (Fin (j.val+1))) :
    let Y := diagonalFilteredGraph d (ritzFilterPolynomial ε (d j) q) (krylovHeadEmbedding j) Ω H
    (1-ε)*(d j)^2*⟪Y.toEuclideanLin z,Y.toEuclideanLin z⟫_ℝ ≤
      ⟪Y.toEuclideanLin z,(Matrix.diagonal (fun i => (d i)^2)).toEuclideanLin (Y.toEuclideanLin z)⟫_ℝ := by
  let e := krylovHeadEmbedding j
  let p := ritzFilterPolynomial ε (d j) q
  let Y := diagonalFilteredGraph d p e Ω H
  let bad := fun i => (1+2*(ε/100))*d i ≤ (1+ε/100)*d j
  have hheadval (s : Fin (j.val+1)) : d j ≤ d (e s) :=
    hd (show e s ≤ j by exact Nat.le_of_lt_succ s.isLt)
  have hp : ∀ s, 1 ≤ p.eval (d (e s)) :=
    fun s => ritzFilterPolynomial_head ε (d j) q hε htarget (d (e s)) (hheadval s)
  have hbadhead (s : Fin (j.val+1)) : ¬bad (e s) := by
    dsimp [bad]
    have hh := hheadval s
    nlinarith
  have htail : ∀ i, bad i → |p.eval (d i)| ≤ 1/strongFilterDenominator (ε/100) q :=
    fun i hi => ritzFilterPolynomial_tail ε (d j) q hε htarget (d i) (hd0 i) hi
  have hden : 0 < strongFilterDenominator (ε/100) q := by
    have hh := strongFilterDenominator_ge_one (ε/100) (by positivity) q
    linarith
  have hsmall := filteredGraph_low_energy d p e Ω H bad
    (1/strongFilterDenominator (ε/100) q) R ε (le_of_lt (div_pos zero_lt_one hden)) hε.le hε'
    hp htail hΩ (ritz_filter_tail_budget ε R hε hε' hR q hstop) z
  have hcoords (s : Fin (j.val+1)) : Y.toEuclideanLin z (e s) = z s := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      diagonalFilteredGraph_head d p e Ω H hhead
        (fun s => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (hp s))),
      Matrix.one_apply, ite_mul, Y]
  dsimp only
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq, diagonal_inner_square]
  exact diagonal_ritz_energy d e bad (d j) ε hε.le hε' htarget.le hd0 hheadval hbadhead
    (fun i hi => ritzFilterPolynomial_middle ε (d j) (d i) hε hε' htarget.le (hd0 i) hi)
    (ofLp z) (ofLp (Y.toEuclideanLin z)) hcoords hsmall

end
end HierarchicalAbsoluteSpectral
