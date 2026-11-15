import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLift
import HierarchicalAbsoluteSpectral.CoarseAlgebraRangeProgram
import HierarchicalAbsoluteSpectral.Spectral

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem exactGramOrthonormalTranspose_contraction {n k : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (hZ : Zᵀ*Z = 1) (x : Fin n → ℝ) :
    quadratic (1 : Core k) (Zᵀ *ᵥ x) ≤ quadratic (1 : Core n) x := by
  let P := Z*Zᵀ
  let E : Core n := 1-P
  have hP : P*P = P := by
    change Z*Zᵀ*(Z*Zᵀ) = Z*Zᵀ
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Zᵀ Z Zᵀ, hZ, Matrix.one_mul]
  have hEt : Eᵀ = E := by simp [E,P,Matrix.transpose_mul]
  have hE : E*E = E := by
    dsimp only [E]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP]
    module
  have hEpos : E.PosSemidef := by
    have hp := Matrix.posSemidef_self_mul_conjTranspose E
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hEt, hE] using hp
  have hnonneg := quadratic_nonneg hEpos x
  have hq : quadratic P x = quadratic (1 : Core k) (Zᵀ *ᵥ x) := by
    simpa only [Matrix.mul_one] using quadratic_congruence (1 : Core k) Z x
  change 0 ≤ quadratic (1-P) x at hnonneg
  rw [quadratic_sub, hq] at hnonneg
  linarith

theorem exactGramAppendixLift_rayleigh {n p k : ℕ}
    (M : Matrix (Fin n) (Fin p) ℝ) (Z : Matrix (Fin n) (Fin k) ℝ)
    (Hc : Core k) (t : ℝ) (ht : 0 ≤ t) (hZ : Zᵀ*Z = 1)
    (hcov : M*Mᵀ = Z*Hc*Zᵀ)
    (out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc))
    (s : ExactGramNegativeSelection out.diagonal)
    (x : Fin n → ℝ) (hx : (Z*out.inverseᵀ.submatrix id s.selected)ᵀ *ᵥ x = 0) :
    quadratic (M*Mᵀ) x ≤ t*quadratic (1 : Core n) x := by
  have hnonneg := exactGramDualLift_complement Z out s x hx
  simp only [quadratic_sub, quadratic_smul] at hnonneg
  calc
    _ = quadratic Hc (Zᵀ *ᵥ x) := by rw [hcov, quadratic_congruence]
    _ ≤ t*quadratic (1 : Core k) (Zᵀ *ᵥ x) := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (exactGramOrthonormalTranspose_contraction Z hZ x) ht

theorem exactGramAppendixLift_range_error {n m p k : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (t : ℝ) (ht : 0 ≤ t)
    (hZ : (A*T)ᵀ*(A*T) = 1) (hcov : (A*B)*(A*B)ᵀ = (A*T)*Hc*(A*T)ᵀ)
    (out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc))
    (s : ExactGramNegativeSelection out.diagonal)
    (qr : OrthogonalRange (A*exactGramDualSmall T out s)) :
    ‖A*B - qr.basis*(qr.basisᵀ*(A*B))‖ ≤ Real.sqrt t := by
  apply projection_error_of_complement_bound (A*B) qr.basis qr.orthogonal
    (Real.sqrt t) (Real.sqrt_nonneg _) 
  intro x hx
  have hY : A*exactGramDualSmall T out s = (A*T)*out.inverseᵀ.submatrix id s.selected := by
    simp only [exactGramDualSmall, Matrix.mul_assoc]
  have hz : ((A*T)*out.inverseᵀ.submatrix id s.selected)ᵀ *ᵥ x = 0 := by
    rw [← hY, qr.spans, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have hb := exactGramAppendixLift_rayleigh (A*B) (A*T) Hc t ht hZ hcov out s x hz
  simpa only [Real.sq_sqrt ht] using hb

/-- An ordinary congruence basis is dualized in the reverse order.
For a random congruence `S` and an LDL factor `L=P^-T`, this is `S^-T L`. -/
theorem exactGramAppendixLift_dual_orientation {k : ℕ} {K : Core k}
    (out : FiniteCongruenceDiagonal K) (S Sinv P Pinv : Core k)
    (hS : Sinv*S = 1) (hP : Pinv*P = 1) (hfactor : out.basis = S*P) :
    out.inverseᵀ = Sinvᵀ*Pinvᵀ := by
  have hi : (Pinv*Sinv)*out.basis = 1 := by
    rw [hfactor]
    calc
      _ = Pinv*(Sinv*S)*P := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hS, Matrix.mul_one, hP]
  have he : out.inverse = Pinv*Sinv := by
    calc
      _ = (Pinv*Sinv*out.basis)*out.inverse := by rw [hi, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, out.right_inverse, Matrix.mul_one]
  rw [he, Matrix.transpose_mul]

end
end HierarchicalAbsoluteSpectral
