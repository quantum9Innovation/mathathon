import HierarchicalAbsoluteSpectral.MatrixInequalities
import HierarchicalAbsoluteSpectral.Carry
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
The deterministic spectral-error conclusion, in the actual L2 operator norm.
`tailSingularValue M r` is sigma_(r+1)(M) in the paper: Mathlib numbers
singular values from zero and extends them by zero beyond the dimension.

The final theorem is explicitly conditional on the hierarchy/filter/threshold
certificates. It is NOT a proof that the randomized algorithm constructs them
within the advertised runtime. See `VERIFICATION.txt` for the exact boundary.
-/

set_option maxHeartbeats 1000000

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false

noncomputable section
open Matrix WithLp
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {n m p r k w : ℕ}

def tailSingularValue (M : Matrix (Fin n) (Fin p) ℝ) (r : ℕ) : ℝ :=
  M.toEuclideanLin.singularValues r

theorem tailSingularValue_nonneg (M : Matrix (Fin n) (Fin p) ℝ) (r : ℕ) :
    0 ≤ tailSingularValue M r := M.toEuclideanLin.singularValues_nonneg r

theorem quadratic_one_norm (x : EuclideanSpace ℝ (Fin n)) :
    quadratic (1 : Core n) (ofLp x) = ‖x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [quadratic, dotProduct, pow_two]

theorem quadratic_mul_transpose (M : Matrix (Fin n) (Fin p) ℝ) (x : Fin n → ℝ) :
    quadratic (M * Mᵀ) x = quadratic (1 : Core p) (Mᵀ *ᵥ x) := by
  unfold quadratic
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.one_mulVec]

/-- A bound on every adjoint Rayleigh quotient bounds the spectral norm. -/
theorem spectral_norm_le_of_rayleigh
    (M : Matrix (Fin n) (Fin p) ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hbound : ∀ x, quadratic (M * Mᵀ) x ≤ a^2 * quadratic 1 x) :
    ‖M‖ ≤ a := by
  have ht : ‖Mᵀ‖ ≤ a := by
    rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ ha
    intro x
    change ‖toLp 2 (Mᵀ *ᵥ ofLp x)‖ ≤ a * ‖x‖
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).mp
    have hx := hbound (ofLp x)
    rw [quadratic_mul_transpose, quadratic_one_norm x] at hx
    have hq := quadratic_one_norm (toLp 2 (Mᵀ *ᵥ ofLp x))
    rw [hq] at hx
    simpa only [mul_pow] using hx
  simpa only [← conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose] using ht

/-- The Rayleigh-quotient step at the end of Lemma 6, including physical projection. -/
theorem projection_error_of_complement_bound
    (M : Matrix (Fin n) (Fin p) ℝ) (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) (a : ℝ) (ha : 0 ≤ a)
    (hbound : ∀ x, Uᵀ *ᵥ x = 0 →
      quadratic (M * Mᵀ) x ≤ a^2 * quadratic 1 x) :
    ‖M - U * (Uᵀ * M)‖ ≤ a := by
  let P : Core n := U * Uᵀ
  let E : Core n := 1 - P
  have hP : P * P = P := by
    dsimp [P]
    calc
      U * Uᵀ * (U * Uᵀ) = U * ((Uᵀ * U) * Uᵀ) := by simp [Matrix.mul_assoc]
      _ = U * Uᵀ := by rw [hU, Matrix.one_mul]
  have hET : Eᵀ = E := by simp [E, P, transpose_mul]
  have hE : E * E = E := by
    dsimp [E]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hP]
    module
  have horth : Uᵀ * E = 0 := by
    simp [E, P, Matrix.mul_sub, ← Matrix.mul_assoc, hU]
  have hPpos : P.PosSemidef := by
    simpa [P] using Matrix.posSemidef_self_mul_conjTranspose U
  have hcontract (x : Fin n → ℝ) : quadratic 1 (E *ᵥ x) ≤ quadratic 1 x := by
    have heq : quadratic 1 (E *ᵥ x) = quadratic E x := by
      rw [← hET, ← quadratic_congruence]
      rw [hET, Matrix.mul_one, hE]
    rw [heq]
    have := quadratic_nonneg hPpos x
    simpa [E] using sub_le_self (quadratic (1 : Core n) x) this
  have hres : M - U * (Uᵀ * M) = E * M := by
    simp [E, P, Matrix.sub_mul, Matrix.mul_assoc]
  rw [hres]
  apply spectral_norm_le_of_rayleigh _ a ha
  intro x
  have hxorth : Uᵀ *ᵥ (E *ᵥ x) = 0 := by rw [Matrix.mulVec_mulVec, horth, Matrix.zero_mulVec]
  have hx := hbound (E *ᵥ x) hxorth
  have hq : quadratic ((E * M) * (E * M)ᵀ) x = quadratic (M * Mᵀ) (E *ᵥ x) := by
    calc
      _ = quadratic (E * (M * Mᵀ) * Eᵀ) x := by
        congr 1
        simp [transpose_mul, Matrix.mul_assoc]
      _ = quadratic (M * Mᵀ) (E *ᵥ x) := by rw [quadratic_congruence, hET]
  rw [hq]
  exact hx.trans (mul_le_mul_of_nonneg_left (hcontract x) (sq_nonneg a))

/-- A transparent deterministic endpoint of Theorem 1.

The supplied certificates are (9), the exact pencil identity, the two physical
mass bounds, the strong dual-complement certificate, and the final scalar
threshold budget. All norms in the conclusion are spectral (L2 operator) norms.
No randomized construction or operation count is asserted by this theorem.
-/
theorem hierarchical_approximation_of_certificates
    (r : ℕ)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) (hU : Uᵀ * U = 1)
    (Z : Matrix (Fin n) (Fin k) ℝ) (F K D Bm : Core k)
    (κ C h b t ε θ : ℝ)
    (hF : F.PosDef) (hK : Kᵀ = K)
    (hb : 0 ≤ b) (hC : 0 ≤ C) (hh : 0 ≤ h) (ht : 0 ≤ t)
    (hθ : 0 ≤ θ) (hκb : κ * b ≤ 1) (hu : b * C * h < 1)
    (hinvariant : F - κ • (K * F⁻¹ * K) ≤ (C * h) • D)
    (hidentity : Z * K * Zᵀ = t • (Z * Bm * Zᵀ) - (A * B) * (A * B)ᵀ)
    (hmass : Z * Bm * Zᵀ ≤ (1 + ε) • (1 : Core n))
    (hD : Z * D * Zᵀ ≤ (2 * t) • (1 : Core n) + (2 : ℝ) • ((A * B) * (A * B)ᵀ))
    (hstrong : ∀ x, Uᵀ *ᵥ x = 0 →
      quadratic (K * F⁻¹ * K) (Zᵀ *ᵥ x) - 2 * quadratic K (Zᵀ *ᵥ x) ≤
        b * quadratic F (Zᵀ *ᵥ x))
    (hbudget : ((1 + b * C * h + ε) / (1 - b * C * h)) * t ≤
      ((1 + θ) * tailSingularValue (A * B) r)^2) :
    (U * (Uᵀ * (A * B))).rank ≤ r ∧
    ‖A * B - U * (Uᵀ * (A * B))‖ ≤ (1 + θ) * tailSingularValue (A * B) r := by
  refine ⟨(output_rank_le _ _).trans hw,
    projection_error_of_complement_bound _ U hU _ ?_ ?_⟩
  · exact mul_nonneg (by linarith) (tailSingularValue_nonneg _ _)
  · intro x hx
    have hphysical := physical_transfer_rayleigh (A * B) Z F K D Bm κ C h b t ε
      hF hK hb hC hh ht hκb hu hinvariant hidentity hmass hD x (hstrong x hx)
    exact hphysical.trans (mul_le_mul_of_nonneg_right hbudget
      (quadratic_nonneg (Matrix.PosSemidef.one) x))

/-- The deterministic spectral conclusion, using the paper's three separate
error sources. `htail` is the near-threshold bound followed by mass comparison.
The numerical tolerances are deliberately weaker than the paper's constants.

The final two lines match the paper: width/rank at most r and spectral error
at most `(1+theta)*sigma_(r+1)(AB)`, including zero optimal tails.
-/
theorem hierarchical_spectral_error
    (r : ℕ)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) (hU : Uᵀ * U = 1)
    (Z : Matrix (Fin n) (Fin k) ℝ) (F K D Bm : Core k)
    (κ C h b t ε θ x : ℝ)
    (hF : F.PosDef) (hK : Kᵀ = K)
    (hb : 0 ≤ b) (hC : 0 ≤ C) (hh : 0 ≤ h) (ht : 0 ≤ t)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hκb : κ * b ≤ 1)
    (hu : b*C*h ≤ θ/1000) (hx : 0 ≤ x) (hx' : x ≤ θ/1000)
    (he : 0 ≤ ε) (he' : ε ≤ θ/1000)
    (hinvariant : F - κ • (K * F⁻¹ * K) ≤ (C * h) • D)
    (hidentity : Z * K * Zᵀ = t • (Z * Bm * Zᵀ) - (A * B) * (A * B)ᵀ)
    (hmass : Z * Bm * Zᵀ ≤ (1 + ε) • (1 : Core n))
    (hD : Z * D * Zᵀ ≤ (2 * t) • (1 : Core n) + (2 : ℝ) • ((A * B) * (A * B)ᵀ))
    (hstrong : ∀ v, Uᵀ *ᵥ v = 0 →
      quadratic (K * F⁻¹ * K) (Zᵀ *ᵥ v) - 2 * quadratic K (Zᵀ *ᵥ v) ≤
        b * quadratic F (Zᵀ *ᵥ v))
    (htail : t ≤ ((1+x)/(1-x)) * (1/(1-ε)) * (tailSingularValue (A * B) r)^2) :
    (U * (Uᵀ * (A * B))).rank ≤ r ∧
    ‖A * B - U * (Uᵀ * (A * B))‖ ≤ (1+θ) * tailSingularValue (A * B) r := by
  apply hierarchical_approximation_of_certificates r A B U hw hU Z F K D Bm
    κ C h b t ε θ hF hK hb hC hh ht hθ hκb (by linarith) hinvariant hidentity hmass hD hstrong
  exact threshold_error_budget θ (b*C*h) x ε t (tailSingularValue (A * B) r)
    hθ hθ' (by positivity) hu hx hx' he he' htail

end
end HierarchicalAbsoluteSpectral
