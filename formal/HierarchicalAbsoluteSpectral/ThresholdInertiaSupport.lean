import HierarchicalAbsoluteSpectral.ThresholdInertiaBridge
import HierarchicalAbsoluteSpectral.CoarseAlgebraRangeProgram

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
variable {n r z : ℕ}

/-- The computed range compression of a symmetric matrix has no zero mode.
The supplied `V` is the literal range witness produced by the range program. -/
theorem inertia_support_compression (D : Core n) (hD : Dᵀ = D)
    (Q : Matrix (Fin n) (Fin r) ℝ) (V : Matrix (Fin n) (Fin r) ℝ)
    (hQ : Qᵀ*Q = 1) (hQD : Q*Qᵀ*D = D) (hQV : Q = D*V) :
    D = Q*(Qᵀ*D*Q)*Qᵀ ∧ IsUnit (Qᵀ*D*Q).det := by
  have hDQ : D*(Q*Qᵀ) = D := by
    have hh := congrArg Matrix.transpose hQD
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,hD,Matrix.mul_assoc] using hh
  have hfactor : D = Q*(Qᵀ*D*Q)*Qᵀ := by
    calc
      _ = (Q*Qᵀ*D)*(Q*Qᵀ) := by rw [hQD,hDQ]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hright : (Qᵀ*D*Q)*(Qᵀ*V) = 1 := by
    calc
      _ = Qᵀ*(D*(Q*Qᵀ))*V := by simp only [Matrix.mul_assoc]
      _ = Qᵀ*(D*V) := by rw [hDQ,Matrix.mul_assoc]
      _ = 1 := by rw [← hQV,hQ]
  refine ⟨hfactor,?_⟩
  letI := Matrix.detInvertibleOfRightInverse (Qᵀ*D*Q) (Qᵀ*V) hright
  exact isUnit_of_invertible _

/-- The computed range of the complementary projector supplies an exact
orthogonal complement, with the expected total dimension. -/
theorem inertia_support_complement (Q : Matrix (Fin n) (Fin r) ℝ)
    (N : Matrix (Fin n) (Fin z) ℝ) (W : Matrix (Fin n) (Fin z) ℝ)
    (hQ : Qᵀ*Q = 1) (hN : Nᵀ*N = 1)
    (hNP : N*Nᵀ*(1-Q*Qᵀ) = 1-Q*Qᵀ) (hNW : N = (1-Q*Qᵀ)*W) :
    Qᵀ*N = 0 ∧ N*Nᵀ = 1-Q*Qᵀ ∧ r+z = n := by
  let P : Core n := 1-Q*Qᵀ
  have hP : P*P = P := by
    dsimp only [P]
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one]
    have hh : (Q*Qᵀ)*(Q*Qᵀ) = Q*Qᵀ := by
      calc
        _ = Q*(Qᵀ*Q)*Qᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hQ]; simp
    rw [hh]
    module
  have hPT : Pᵀ = P := by simp [P,Matrix.transpose_mul]
  have hQN : Qᵀ*N = 0 := by
    rw [hNW]
    have hh : Qᵀ*(1-Q*Qᵀ) = 0 := by
      simp only [Matrix.mul_sub,Matrix.mul_one,← Matrix.mul_assoc,hQ,Matrix.one_mul,sub_self]
    rw [← Matrix.mul_assoc,hh,Matrix.zero_mul]
  have hPN : P*N = N := by
    calc
      _ = P*(P*W) := by rw [hNW]
      _ = P*W := by rw [← Matrix.mul_assoc,hP]
      _ = N := hNW.symm
  have hNT : Nᵀ*P = Nᵀ := by
    have hh := congrArg Matrix.transpose hPN
    simpa only [Matrix.transpose_mul,hPT] using hh
  have hNN : N*Nᵀ = P := by
    calc
      _ = N*Nᵀ*P := by rw [Matrix.mul_assoc,hNT]
      _ = P := hNP
  have hsum : Q*Qᵀ+N*Nᵀ = 1 := by rw [hNN]; dsimp [P]; module
  have ht := congrArg Matrix.trace hsum
  rw [Matrix.trace_add,Matrix.trace_mul_comm Q Qᵀ,Matrix.trace_mul_comm N Nᵀ,hQ,hN] at ht
  simp only [Matrix.trace_one,Fintype.card_fin] at ht
  refine ⟨hQN,hNN,?_⟩
  exact_mod_cast ht

end
end HierarchicalAbsoluteSpectral
