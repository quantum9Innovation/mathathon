import HierarchicalAbsoluteSpectral.PhysicalPencil
import HierarchicalAbsoluteSpectral.StrongAction

/-!
Assemble the deterministic transfer from a support factorization and a
filtered inverse-factor pencil. In particular, none of the physical mass,
physical D, pencil-identity or quadratic-strong-action bounds is assumed.
Randomized support/filter/threshold construction is proved separately.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p k w u : ℕ}

theorem support_filter_spectral_error
    (r : ℕ)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (Z : Matrix (Fin n) (Fin k) ℝ) (Bbar : Matrix (Fin k) (Fin p) ℝ)
    (hsupport : A*B = Z*Bbar)
    (R Bm Q₀ : Core k) (hR : IsUnit R.det) (hBm : Bmᵀ = Bm)
    (U : Matrix (Fin k) (Fin u) ℝ) (V : Matrix (Fin n) (Fin w) ℝ)
    (W : Matrix (Fin w) (Fin u) ℝ) (hw : w ≤ r) (hV : Vᵀ*V = 1)
    (hcolumns : Z*(R⁻¹)ᵀ*U = V*W)
    (κ C h t ε θ x c : ℝ)
    (hC : 0 ≤ C) (hh : 0 ≤ h) (ht : 0 ≤ t) (hc : 1 ≤ c)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (he : 0 ≤ ε) (he' : ε ≤ θ/1000)
    (hx : 0 ≤ x) (hx' : x ≤ θ/1000)
    (hκb : κ*(c^2-1) ≤ 1) (hu : (c^2-1)*C*h ≤ θ/1000)
    (hGpos : (Zᵀ*Z).PosDef) (hG : Zᵀ*Z ≤ (2:ℝ) • (1 : Core k))
    (hQ : Q₀ ≤ (2:ℝ) • (Bbar*Bbarᵀ))
    (hmass : Bm ≤ (1+ε) • (Zᵀ*Z)⁻¹)
    (hinvariant : inverseMetric R - κ •
        ((t • Bm - Bbar*Bbarᵀ) * (inverseMetric R)⁻¹ * (t • Bm - Bbar*Bbarᵀ)) ≤
      (C*h) • (t • (1 : Core k) + Q₀))
    (hfilter : ‖(1-U*Uᵀ) * (1-normalizedPencil R (t • Bm-Bbar*Bbarᵀ))‖ ≤ c)
    (htail : t ≤ ((1+x)/(1-x)) * (1/(1-ε)) * (tailSingularValue (A*B) r)^2) :
    (V * (Vᵀ * (A*B))).rank ≤ r ∧
    ‖A*B - V * (Vᵀ * (A*B))‖ ≤ (1+θ) * tailSingularValue (A*B) r := by
  let K : Core k := t • Bm - Bbar*Bbarᵀ
  have hK : Kᵀ = K := by simp [K, Matrix.transpose_mul, hBm]
  have hphysicalMass := physical_mass_bound Z Bm ε he hGpos hmass
  have hphysicalD := physical_D_bound Z Bbar Q₀ t ht hG hQ
  have hphysicalIdentity := physical_pencil_identity Z Bbar Bm t
  rw [← hsupport] at hphysicalD hphysicalIdentity
  have hstrong := physical_strong_action_certificate Z R K U V W c hR hK
    (by linarith) hcolumns hfilter
  apply hierarchical_spectral_error r A B V hw hV Z (inverseMetric R) K
    (t • (1 : Core k)+Q₀) Bm κ C h (c^2-1) t ε θ x (inverseMetric_posDef R hR)
    hK (by nlinarith) hC hh ht hθ hθ' hκb hu hx hx' he he' hinvariant
    hphysicalIdentity hphysicalMass hphysicalD hstrong htail

end
end HierarchicalAbsoluteSpectral
