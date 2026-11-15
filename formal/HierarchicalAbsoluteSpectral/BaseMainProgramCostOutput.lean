import HierarchicalAbsoluteSpectral.BaseMainQueryCost
import HierarchicalAbsoluteSpectral.MainStatementsExact
import HierarchicalAbsoluteSpectral.MainStatementsStrong

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p k r w : ℕ}
attribute [local irreducible] orthogonalRangeProgram
  physicalRangeProgram exactPhysicalOutputProgram projectionOutputProgram
  strongPhysicalRangeProgram automaticStrongPhysicalRangeProgram strongProjectionOutputProgram

def kernelColumnWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) : ℕ :=
  Finset.univ.sup (fun d : Fin (c+1) => (kernels a b d.val).cost)

theorem kernelColumnWorkCap_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (a b c d : ℕ) (hd : d ≤ c) : (kernels a b d).cost ≤ kernelColumnWorkCap kernels a b c := by
  exact Finset.le_sup (f := fun i : Fin (c+1) => (kernels a b i.val).cost)
    (Finset.mem_univ (⟨d,by omega⟩ : Fin (c+1)))

def exactRangeWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b : ℕ) : ℕ :=
  (kernels b a b).cost+psdGramCost kernels b+kernelColumnWorkCap kernels a b b

theorem exactRangeWorkCap_correct (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {a b : ℕ} (Y : Matrix (Fin a) (Fin b) ℝ) :
    (orthogonalRangeProgram kernels Y).work ≤ exactRangeWorkCap kernels a b := by
  let G := ((kernels b a b).program Yᵀ Y).certify.eval.val
  have hG : G.PosSemidef := by
    have he : G=Yᵀ*Y := by simp only [G,certify_eval,ArithmeticKernel.program_eval]
    rw [he]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self Y
  let pair := (psdGramProgram kernels b G hG).eval
  have hp := psdGramProgram_work_le kernels b G hG
  have hk := kernelColumnWorkCap_le kernels a b b pair.dimension pair.dimension_le_fin
  simp only [orthogonalRangeProgram,work_bind,certify_work,ArithmeticKernel.program_work,work_pure,add_zero]
  change (kernels b a b).cost+((psdGramProgram kernels b G hG).work+(kernels a b pair.dimension).cost) ≤ _
  dsimp [exactRangeWorkCap]
  omega

def projectionOutputWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (n m p r : ℕ) : ℕ :=
  Finset.univ.sup (fun w : Fin (r+1) =>
    (kernels w.val n m).cost+(kernels w.val m p).cost+(kernels n w.val p).cost)

theorem projectionOutputWorkCap_correct
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin w) ℝ) (hw : w ≤ r) :
    (projectionOutputProgram kernels A B U hw).work ≤ projectionOutputWorkCap kernels n m p r := by
  rw [projectionOutputProgram_work]
  exact Finset.le_sup (f := fun i : Fin (r+1) =>
    (kernels i.val n m).cost+(kernels i.val m p).cost+(kernels n i.val p).cost)
      (Finset.mem_univ (⟨w,by omega⟩ : Fin (r+1)))

theorem physicalRangeProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z w) (U : Matrix (Fin k) (Fin w) ℝ) :
    (physicalRangeProgram kernels PZ U).work ≤ PZ.cost+exactRangeWorkCap kernels n w := by
  have hp := PZ.work_le U
  have hr := exactRangeWorkCap_correct kernels (PZ.program U).certify.eval.val
  simp only [physicalRangeProgram,work_bind,certify_work,work_pure,add_zero]
  omega

theorem exactPhysicalOutputProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z w)
    (U : Matrix (Fin k) (Fin w) ℝ) (hw : w ≤ r) :
    (exactPhysicalOutputProgram kernels A B PZ U hw).work ≤
      PZ.cost+exactRangeWorkCap kernels n w+projectionOutputWorkCap kernels n m p r := by
  have hp := physicalRangeProgram_work_bound kernels PZ U
  have ho := projectionOutputWorkCap_correct kernels A B
    (physicalRangeProgram kernels PZ U).eval.basis
      ((physicalRangeProgram kernels PZ U).eval.dimension_le_cols.trans hw)
  simp only [exactPhysicalOutputProgram,work_bind]
  omega

theorem strongPhysicalRangeProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {T : Core k} {Z : Matrix (Fin n) (Fin k) ℝ}
    (PT : MatrixAction T r) (PZ : MatrixAction Z r) (α : ℝ) (v : ℕ) (hα : 0 < α)
    (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    (strongPhysicalRangeProgram kernels PT PZ α v hα Ξ).work ≤
      9+3*v+(v+1)*(PT.cost+6*k*r)+k*r+PZ.cost+exactRangeWorkCap kernels n r := by
  have hf := (strongFilterAction PT α v hα).work_le Ξ
  have hz := PZ.work_le ((strongFilterAction PT α v hα).program Ξ).certify.eval.val
  have hr := exactRangeWorkCap_correct kernels
    (PZ.program ((strongFilterAction PT α v hα).program Ξ).certify.eval.val).certify.eval.val
  simp only [strongPhysicalRangeProgram,work_bind,certify_work,work_pure,add_zero]
  change _ ≤ (strongFilterAction PT α v hα).cost+PZ.cost+exactRangeWorkCap kernels n r
  omega

theorem automaticStrongPhysicalRangeProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {T : Core k} {Z : Matrix (Fin n) (Fin k) ℝ}
    (PT : MatrixAction T r) (PZ : MatrixAction Z r)
    (U β α : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    let v := strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1
    (automaticStrongPhysicalRangeProgram kernels PT PZ U β α hk hU hβ hβ1 hα hα1 Ξ).work ≤
      4*v+14+(9+3*v+(v+1)*(PT.cost+6*k*r)+k*r+PZ.cost+exactRangeWorkCap kernels n r) := by
  intro v
  have hs := strongGaussianDegreeProgram_specification k U β α hk hU hβ hβ1 hα hα1
  have hp := strongPhysicalRangeProgram_work_bound kernels PT PZ α
    (strongGaussianDegreeProgram k U β α hk hU hβ hβ1 hα hα1).eval hα Ξ
  rw [hs.1] at hp
  have he := congrArg (fun v => (strongPhysicalRangeProgram kernels PT PZ α v hα Ξ).work) hs.1
  simp only [automaticStrongPhysicalRangeProgram,work_bind,work_pure,add_zero,hs.2.1]
  rw [he]
  simpa only [v] using Nat.add_le_add_left hp
    (4*strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1+14)

theorem strongProjectionOutputProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {T : Core k} {Z : Matrix (Fin n) (Fin k) ℝ}
    (PT : MatrixAction T r) (PZ : MatrixAction Z r)
    (U β α : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    let v := strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1
    (strongProjectionOutputProgram kernels A B PT PZ U β α hk hU hβ hβ1 hα hα1 Ξ).work ≤
      4*v+14+(9+3*v+(v+1)*(PT.cost+6*k*r)+k*r+PZ.cost+exactRangeWorkCap kernels n r)+
        projectionOutputWorkCap kernels n m p r := by
  intro v
  have hs := automaticStrongPhysicalRangeProgram_work_bound kernels PT PZ U β α hk hU hβ hβ1 hα hα1 Ξ
  have ho := projectionOutputWorkCap_correct kernels A B
    (automaticStrongPhysicalRangeProgram kernels PT PZ U β α hk hU hβ hβ1 hα hα1 Ξ).eval.2.basis
    (automaticStrongPhysicalRangeProgram kernels PT PZ U β α hk hU hβ hβ1 hα hα1 Ξ).eval.2.dimension_le_cols
  simp only [strongProjectionOutputProgram,work_bind]
  dsimp only [v]
  omega

end
end HierarchicalAbsoluteSpectral
