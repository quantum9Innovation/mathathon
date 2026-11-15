import HierarchicalAbsoluteSpectral.CoarseAlgebraInertiaSupportData
import HierarchicalAbsoluteSpectral.CoarseAlgebraRangeCost
import HierarchicalAbsoluteSpectral.ThresholdInertiaSupport

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n : ℕ}

def inertiaSupportProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D : Core n) (hD : Dᵀ = D) : ArithmeticProgram (InertiaSupport D) := do
  let qr ← certify (orthogonalRangeProgram kernels D)
  let Q := qr.val.basis
  have hQcoords : ∃ V : Matrix (Fin n) (Fin qr.val.dimension) ℝ, Q = D*V := by
    dsimp only [Q]
    rw [qr.property]
    exact orthogonalRangeProgram_basis_in_range kernels D
  have hComp : D = Q*(Qᵀ*D*Q)*Qᵀ ∧ IsUnit (Qᵀ*D*Q).det := by
    obtain ⟨V,hQV⟩ := hQcoords
    exact inertia_support_compression D hD Q V qr.val.orthogonal qr.val.projection_exact hQV
  let QQ ← certify ((kernels n qr.val.dimension n).program Q Qᵀ)
  let P ← certify (blockSubProgram (1 : Core n) QQ.val)
  have hP : P.val = 1-Q*Qᵀ := by
    simp only [P.property,blockSubProgram_eval,QQ.property,ArithmeticKernel.program_eval]
  let nr ← certify (orthogonalRangeProgram kernels P.val)
  let N := nr.val.basis
  have hNcoords : ∃ W : Matrix (Fin n) (Fin nr.val.dimension) ℝ, N = P.val*W := by
    dsimp only [N]
    rw [nr.property]
    exact orthogonalRangeProgram_basis_in_range kernels P.val
  have hNP : N*Nᵀ*(1-Q*Qᵀ) = 1-Q*Qᵀ := by
    calc
      _ = N*Nᵀ*P.val := congrArg (N*Nᵀ*·) hP.symm
      _ = P.val := nr.val.projection_exact
      _ = _ := hP
  have hComplement : Qᵀ*N = 0 ∧ N*Nᵀ = 1-Q*Qᵀ ∧ qr.val.dimension+nr.val.dimension = n := by
    obtain ⟨W,hNW⟩ := hNcoords
    have hNW' : N = (1-Q*Qᵀ)*W := hNW.trans (congrArg (·*W) hP)
    exact inertia_support_complement Q N W qr.val.orthogonal nr.val.orthogonal hNP hNW'
  let H1 ← certify ((kernels qr.val.dimension n n).program Qᵀ D)
  let H ← certify ((kernels qr.val.dimension n qr.val.dimension).program H1.val Q)
  have hH : H.val = Qᵀ*D*Q := by
    simp only [H.property,ArithmeticKernel.program_eval,H1.property]
  have hSum : Q*Qᵀ+N*Nᵀ = 1 := by rw [hComplement.2.1]; module
  have hHunit : IsUnit H.val.det := by rw [hH]; exact hComp.2
  have hDecomp : D = Q*H.val*Qᵀ := by
    exact hComp.1.trans (congrArg (fun A => Q*A*Qᵀ) hH.symm)
  ArithmeticProgram.pure {
    dimension := qr.val.dimension
    nullity := nr.val.dimension
    dimension_le := qr.val.dimension_le_rows
    total := hComplement.2.2
    basis := Q
    complement := N
    basis_orthogonal := qr.val.orthogonal
    complement_orthogonal := nr.val.orthogonal
    cross_zero := hComplement.1
    projectors := hSum
    compressed := H.val
    compressed_eq := hH
    compressed_isUnit := hHunit
    decomposition := hDecomp }

theorem inertiaSupportProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D : Core n) (hD : Dᵀ = D) : (inertiaSupportProgram kernels D hD).admissible := by
  simp only [inertiaSupportProgram,admissible_bind,certify_admissible,
    orthogonalRangeProgram_admissible,ArithmeticKernel.program_admissible,
    blockSubProgram_admissible,admissible_pure,and_self]

theorem inertiaSupportProgram_work_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D : Core n) (hD : Dᵀ = D) (hn : 1 ≤ n) :
    (inertiaSupportProgram kernels D hD).work ≤
      2*psdGramCost kernels n+7*kernelEnvelope kernels n+n*n := by
  simp only [inertiaSupportProgram,work_bind,certify_work,ArithmeticKernel.program_work,
    blockSubProgram_work,work_pure]
  calc
    _ ≤ (2*kernelEnvelope kernels n+psdGramCost kernels n)+(kernelEnvelope kernels n+
        (n*n+((2*kernelEnvelope kernels n+psdGramCost kernels n)+
          (kernelEnvelope kernels n+(kernelEnvelope kernels n+0))))) := by
      gcongr
      all_goals first | exact orthogonalRangeProgram_work_le kernels _ hn le_rfl | apply kernelEnvelope_le | skip
      all_goals first | omega | exact OrthogonalRange.dimension_le_rows _
    _ = _ := by omega

end
end HierarchicalAbsoluteSpectral
