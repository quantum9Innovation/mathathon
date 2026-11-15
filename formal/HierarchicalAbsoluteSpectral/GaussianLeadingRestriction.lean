import HierarchicalAbsoluteSpectral.GaussianLeadingMinors
import HierarchicalAbsoluteSpectral.GaussianRestriction

/-! A fixed ambient Gaussian array supplies every deterministically selected
leading square block, including the empty block, with its exact Gaussian law. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix

theorem gaussianVector_restrict_measurePreserving (n r : ℕ) (e : Fin r ↪ Fin n) :
    MeasurePreserving (fun g : Fin n → ℝ => fun j => g (e j))
      (gaussianVector n) (gaussianVector r) := by
  have hi : iIndepFun (fun j : Fin n => fun g : Fin n → ℝ => g j)
      (gaussianVector n) :=
    iIndepFun_pi (X := fun _ => id) (μ := fun _ : Fin n => gaussianReal 0 1)
      (fun _ => aemeasurable_id)
  refine ⟨by fun_prop, ?_⟩
  have hm := (hi.precomp e.injective).map_fun_eq_pi_map
    (fun _ => (measurable_pi_apply _).aemeasurable)
  change (gaussianVector n).map (fun g => fun j => g (e j)) =
    Measure.pi (fun _ : Fin r => gaussianReal 0 1)
  rw [hm]
  congr 1
  funext j
  exact (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) (e j)).map_eq

def leadingSquareGaussianEmbedding {n r : ℕ} (hr : r ≤ n) : Fin (r*r) ↪ Fin (n*n) :=
  (finProdFinEquiv.symm.toEmbedding.trans
    ((Fin.castLEEmb hr).prodMap (Fin.castLEEmb hr))).trans finProdFinEquiv.toEmbedding

theorem gaussian_congruence_leading_submatrix_regular_and_invertible_ae
    {n r : ℕ} (hr : r ≤ n) (H : Core r)
    (hH : H.toEuclideanLin.IsSymmetric) (hdet : IsUnit H.det) :
    ∀ᵐ g ∂gaussianVector (n*n),
      let S := (gaussianSquareMatrix n g).submatrix (Fin.castLEEmb hr) (Fin.castLEEmb hr)
      LeadingPrincipalRegular (Sᵀ*H*S) ∧ IsUnit S.det := by
  have hm := gaussianVector_restrict_measurePreserving (n*n) (r*r)
    (leadingSquareGaussianEmbedding hr)
  have ha := hm.quasiMeasurePreserving.ae
    (gaussian_congruence_leading_regular_and_invertible_ae H hH hdet)
  filter_upwards [ha] with g hg
  have heq : gaussianSquareMatrix r (fun j => g (leadingSquareGaussianEmbedding hr j)) =
      (gaussianSquareMatrix n g).submatrix (Fin.castLEEmb hr) (Fin.castLEEmb hr) := by
    ext i j
    simp [gaussianSquareMatrix, leadingSquareGaussianEmbedding]
  rw [heq] at hg
  exact hg

end
end HierarchicalAbsoluteSpectral
