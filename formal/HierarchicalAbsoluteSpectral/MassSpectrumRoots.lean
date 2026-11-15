import HierarchicalAbsoluteSpectral.MassSpectrum

/-! Analytical mass normalizations. These definitions are used only in proofs;
the arithmetic algorithm never evaluates a matrix square root. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {k : ℕ}

def massInverseFactor (B : Core k) : Core k := (CFC.sqrt B)⁻¹

theorem massRoot_isUnit (B : Core k) (hB : B.PosDef) : IsUnit (CFC.sqrt B).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply (isUnit_pow_iff (by decide : (2:ℕ) ≠ 0)).mp
  rw [CFC.sq_sqrt B hB.posSemidef.nonneg]
  exact hB.isUnit

theorem massInverseFactor_isUnit (B : Core k) (hB : B.PosDef) :
    IsUnit (massInverseFactor B).det := Matrix.isUnit_nonsing_inv_det _ (massRoot_isUnit B hB)

theorem massInverseFactor_metric (B : Core k) (hB : B.PosDef) :
    inverseMetric (massInverseFactor B) = B := by
  have ht : (CFC.sqrt B)ᵀ = CFC.sqrt B := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
  rw [inverseMetric, massInverseFactor, Matrix.nonsing_inv_nonsing_inv _ (massRoot_isUnit B hB),
    ht, ← pow_two, CFC.sq_sqrt B hB.posSemidef.nonneg]

def massEigenvalue (Q B : Core k) (hQ : Q.IsHermitian) (j : Fin k) : ℝ :=
  orderedEigenvalue ((massInverseFactor B)ᵀ*Q*massInverseFactor B)
    (normalized_isHermitian _ Q (by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.eq)) j

theorem massEigenvalue_compare (Q B₁ B₂ : Core k) (hQ : Q.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef) (ε : ℝ)
    (hε : 0 ≤ ε) (hε' : ε < 1)
    (hlo : (1-ε) • B₁ ≤ B₂) (hhi : B₂ ≤ (1+ε) • B₁) (j : Fin k) :
    massEigenvalue Q B₁ hQ.isHermitian j/(1+ε) ≤ massEigenvalue Q B₂ hQ.isHermitian j ∧
    massEigenvalue Q B₂ hQ.isHermitian j ≤ massEigenvalue Q B₁ hQ.isHermitian j/(1-ε) := by
  apply generalizedEigenvalue_mass_compare Q (massInverseFactor B₁) (massInverseFactor B₂)
    hQ (massInverseFactor_isUnit B₁ hB₁) (massInverseFactor_isUnit B₂ hB₂) ε hε hε'
  · simpa only [massInverseFactor_metric B₁ hB₁, massInverseFactor_metric B₂ hB₂] using hlo
  · simpa only [massInverseFactor_metric B₁ hB₁, massInverseFactor_metric B₂ hB₂] using hhi

theorem massEigenvalue_eq_of_factor (Q B R : Core k) (hQ : Q.PosSemidef)
    (hB : B.PosDef) (hR : IsUnit R.det) (hmetric : inverseMetric R = B) (j : Fin k) :
    massEigenvalue Q B hQ.isHermitian j =
      orderedEigenvalue (Rᵀ*Q*R) (normalized_isHermitian R Q hQ.isHermitian.eq) j := by
  apply le_antisymm
  · have hh := generalizedEigenvalue_lower Q (massInverseFactor B) R hQ
      (massInverseFactor_isUnit B hB) hR 1 (by norm_num)
      (by rw [hmetric, one_smul, massInverseFactor_metric B hB]) j
    simpa only [massEigenvalue, div_one] using hh
  · have hh := generalizedEigenvalue_lower Q R (massInverseFactor B) hQ
      hR (massInverseFactor_isUnit B hB) 1 (by norm_num)
      (by rw [hmetric, one_smul, massInverseFactor_metric B hB]) j
    simpa only [massEigenvalue, div_one] using hh

theorem massRoot_transpose (G : Core k) : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (CFC.sqrt_nonneg G).posSemidef.isHermitian.eq

theorem massRoot_metric (G : Core k) (hG : G.PosDef) :
    inverseMetric (CFC.sqrt G) = G⁻¹ := by
  rw [inverseMetric, Matrix.transpose_nonsing_inv, massRoot_transpose,
    ← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg]

/-- The canonical generalized eigenvalue for mass `G^-1` is exactly the
sorted eigenvalue of the manuscript's `H = sqrt(G) Q sqrt(G)`. -/
theorem massEigenvalue_inverse (Q G : Core k) (hQ : Q.PosSemidef)
    (hG : G.PosDef) (j : Fin k) :
    massEigenvalue Q G⁻¹ hQ.isHermitian j =
      orderedEigenvalue (CFC.sqrt G*Q*CFC.sqrt G)
        (by simpa only [massRoot_transpose] using
          normalized_isHermitian (CFC.sqrt G) Q hQ.isHermitian.eq) j := by
  have hh := massEigenvalue_eq_of_factor Q G⁻¹ (CFC.sqrt G) hQ hG.inv
    (massRoot_isUnit G hG) (massRoot_metric G hG) j
  simpa only [massRoot_transpose] using hh

end
end HierarchicalAbsoluteSpectral
