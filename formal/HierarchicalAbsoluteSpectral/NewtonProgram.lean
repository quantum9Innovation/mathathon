import HierarchicalAbsoluteSpectral.CholeskyProgram
import HierarchicalAbsoluteSpectral.NewtonMatrix

/-! Finite arithmetic execution of matrix inverse Newton iteration.
Inverses are computed by balanced Cholesky, never supplied as an oracle. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {k : ℕ}

def positiveInverseProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D : Core k) (hD : D.PosDef) : ArithmeticProgram {X : Core k // X = D⁻¹} := do
  let p ← choleskyProgram kernels k D hD
  let V ← certify ((kernels k k k).program p.inverse p.inverseᵀ)
  ArithmeticProgram.pure ⟨V.val, by
    rw [V.property, ArithmeticKernel.program_eval]
    calc
      _ = p.upper⁻¹*(p.upper⁻¹)ᵀ := by rw [p.inverse_eq]
      _ = (p.upperᵀ*p.upper)⁻¹ := by rw [Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]
      _ = D⁻¹ := congrArg Inv.inv p.gram⟩

theorem positiveInverseProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D : Core k) (hD : D.PosDef) :
    (positiveInverseProgram kernels D hD).work = choleskyCost kernels k+(kernels k k k).cost := by
  simp only [positiveInverseProgram, work_bind, choleskyProgram_work, certify_work,
    ArithmeticKernel.program_work, work_pure, add_zero]

theorem positiveInverseProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D : Core k) (hD : D.PosDef) : (positiveInverseProgram kernels D hD).admissible := by
  simp only [positiveInverseProgram, admissible_bind, choleskyProgram_admissible,
    certify_admissible, ArithmeticKernel.program_admissible, admissible_pure, and_self]

def upperNewtonLoopProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (M : Core k) (hpos : ∀ n, (upperNewtonMatrix M n).PosDef) :
    (q : ℕ) → ArithmeticProgram {X : Core k // X = upperNewtonMatrix M q}
  | 0 => ArithmeticProgram.pure ⟨(2:ℝ) • 1, rfl⟩
  | q+1 => do
    let X ← upperNewtonLoopProgram kernels M hpos q
    have hX : X.val.PosDef := X.property.symm ▸ hpos q
    let Xi ← positiveInverseProgram kernels X.val hX
    let Z ← certify ((kernels k k k).program M Xi.val)
    let U ← certify (blockAddProgram X.val Z.val)
    let V ← certify (blockScaleProgram (1/2) U.val)
    ArithmeticProgram.pure ⟨V.val, by
      simp only [V.property, blockScaleProgram_eval, U.property, blockAddProgram_eval,
        Z.property, ArithmeticKernel.program_eval, Xi.property, X.property,
        upperNewtonMatrix]⟩

theorem upperNewtonLoopProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (M : Core k) (hpos : ∀ n, (upperNewtonMatrix M n).PosDef) (q : ℕ) :
    (upperNewtonLoopProgram kernels M hpos q).work =
      q*(choleskyCost kernels k+2*(kernels k k k).cost+2*k*k) := by
  induction q with
  | zero => simp [upperNewtonLoopProgram]
  | succ q ih =>
    simp only [upperNewtonLoopProgram, work_bind, positiveInverseProgram_work,
      certify_work, ArithmeticKernel.program_work, blockAddProgram_work,
      blockScaleProgram_work, work_pure, ih]
    ring

theorem upperNewtonLoopProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (M : Core k) (hpos : ∀ n, (upperNewtonMatrix M n).PosDef) (q : ℕ) :
    (upperNewtonLoopProgram kernels M hpos q).admissible := by
  induction q with
  | zero => trivial
  | succ q ih =>
    simp only [upperNewtonLoopProgram, admissible_bind, positiveInverseProgram_admissible,
      certify_admissible, ArithmeticKernel.program_admissible, blockAddProgram_admissible,
      blockScaleProgram_admissible, admissible_pure, ih, and_self]

def baseNewtonProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (S : Core k) (hS : S.IsHermitian) (h : ℝ) (hh : 0 < h) (q : ℕ) :
    ArithmeticProgram {F : Core k // F = baseNewtonMetric S h q} := do
  let η ← certify (ArithmeticProgram.mul 8 h)
  let η2 ← certify (ArithmeticProgram.mul η.val η.val)
  let SS ← certify ((kernels k k k).program S S)
  let M ← certify (blockAddProgram SS.val (Matrix.diagonal (fun _ => η2.val)))
  have hη : η.val = 8*h := η.property
  have hM : M.val = S*S+(8*h)^2 • (1 : Core k) := by
    simp only [M.property, blockAddProgram_eval, SS.property, ArithmeticKernel.program_eval,
      η2.property, eval_mul, hη, ← pow_two]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hpos : ∀ n, (upperNewtonMatrix M.val n).PosDef := by
    intro n
    rw [hM]
    exact baseNewtonIterate_posDef S hS h hh n
  let X ← upperNewtonLoopProgram kernels M.val hpos q
  let F ← certify (blockAddProgram X.val (Matrix.diagonal (fun _ => η.val)))
  ArithmeticProgram.pure ⟨F.val, by
    simp only [F.property, blockAddProgram_eval, X.property, hM, hη,
      baseNewtonMetric, baseNewtonIterate]
    ext i j
    by_cases hij : i = j <;> simp [hij]⟩

theorem baseNewtonProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (S : Core k) (hS : S.IsHermitian) (h : ℝ) (hh : 0 < h) (q : ℕ) :
    (baseNewtonProgram kernels S hS h hh q).work =
      2+(kernels k k k).cost+2*k*k+
        q*(choleskyCost kernels k+2*(kernels k k k).cost+2*k*k) := by
  simp only [baseNewtonProgram, work_bind, certify_work, work_mul,
    ArithmeticKernel.program_work, blockAddProgram_work, upperNewtonLoopProgram_work, work_pure]
  ring

theorem baseNewtonProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (S : Core k) (hS : S.IsHermitian) (h : ℝ) (hh : 0 < h) (q : ℕ) :
    (baseNewtonProgram kernels S hS h hh q).admissible := by
  simp only [baseNewtonProgram, admissible_bind, certify_admissible,
    ArithmeticKernel.program_admissible, blockAddProgram_admissible,
    upperNewtonLoopProgram_admissible, admissible_pure, and_true]
  constructor <;> trivial

end
end HierarchicalAbsoluteSpectral
