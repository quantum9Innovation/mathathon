import HierarchicalAbsoluteSpectral.CorollaryTwoLevelProgram
import HierarchicalAbsoluteSpectral.MainPreparedProgram
import HierarchicalAbsoluteSpectral.BaseMainTotalCost
import HierarchicalAbsoluteSpectral.BaseMainRandomizedCost

/-! The final two-level caller charges both its dyadic parameters and all
derived main-algorithm tolerances and repetition counts. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure
variable {N m r : ℕ}

def TwoLevelProblem.preparedScalarCaller
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (out : TwoLevelScalarParameters (m:ℝ))
    (g : MainRandomTape I.fixed) : ArithmeticProgram (FixedRankOutput N N r) :=
  preparedFixedDepthProgram kernels (I.fixedFromScalars out) ((I.fixedFromScalars_eq out).symm ▸ g)

theorem TwoLevelProblem.preparedScalarCaller_eq
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (out : TwoLevelScalarParameters (m:ℝ))
    (g : MainRandomTape I.fixed) :
    I.preparedScalarCaller kernels out g = preparedFixedDepthProgram kernels I.fixed g := by
  rw [out.eq_canonical]
  rfl

def preparedTwoLevelProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    ArithmeticProgram (FixedRankOutput N N r) := do
  let out ← twoLevelParametersProgram m
  I.preparedScalarCaller kernels out g

theorem preparedTwoLevelProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (preparedTwoLevelProgram kernels I g).eval = (fixedDepthProgram kernels I.fixed g).eval := by
  simp only [preparedTwoLevelProgram,eval_bind,TwoLevelProblem.preparedScalarCaller_eq,
    preparedFixedDepthProgram_eval]

theorem preparedTwoLevelProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (preparedTwoLevelProgram kernels I g).admissible := by
  simp only [preparedTwoLevelProgram,admissible_bind,twoLevelParametersProgram_admissible,
    true_and,TwoLevelProblem.preparedScalarCaller_eq,preparedFixedDepthProgram_admissible]

theorem preparedTwoLevelProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (preparedTwoLevelProgram kernels I g).work = (twoLevelParametersProgram m).work+
      33+3*I.fixed.queryCap+2*I.fixed.repetitions+(fixedDepthProgram kernels I.fixed g).work := by
  simp only [preparedTwoLevelProgram,work_bind,TwoLevelProblem.preparedScalarCaller_eq,
    preparedFixedDepthProgram_work]
  omega

theorem preparedTwoLevelProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ Ck*(D:ℝ)^p0)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (preparedTwoLevelProgram kernels I g).work ≤ (twoLevelParametersProgram m).work+
      33+3*I.fixed.queryCap+2*I.fixed.repetitions+fixedDepthRealizedWorkCap kernels I.fixed g Ck p0 := by
  rw [preparedTwoLevelProgram_work]
  exact Nat.add_le_add_left (fixedDepthProgram_work_bound kernels Ck p0 hC hp hK I.fixed g) _

theorem preparedTwoLevelProgram_rank_cap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (preparedTwoLevelProgram kernels I g).eval.width ≤ r ∧
      (preparedTwoLevelProgram kernels I g).eval.product.rank ≤ r := by
  rw [preparedTwoLevelProgram_eval]
  exact fixedDepthProgram_rank_cap kernels I.fixed g

theorem preparedTwoLevelProgram_product (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (preparedTwoLevelProgram kernels I g).eval.product =
      (preparedTwoLevelProgram kernels I g).eval.left*(preparedTwoLevelProgram kernels I g).eval.right :=
  (preparedTwoLevelProgram kernels I g).eval.product_eq

/-- The original finite tape is sampled and charged, together with every
arithmetic instruction of the prepared two-level program. -/
def preparedTwoLevelTotalWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) : ℕ :=
  mainRandomizedWork I.fixed (preparedTwoLevelProgram kernels I g).work

theorem preparedTwoLevelTotalWork_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    preparedTwoLevelTotalWork kernels I g =
      (twoLevelParametersProgram m).work+preparedFixedDepthTotalWork kernels I.fixed g := by
  unfold preparedTwoLevelTotalWork preparedFixedDepthTotalWork mainRandomizedWork
  rw [preparedTwoLevelProgram_work,preparedFixedDepthProgram_work]
  omega

theorem preparedTwoLevelTotalWork_bound_deflation
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (kernels a b c).cost ≤ 2*a*b*c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ Ck*(D:ℝ)^p0)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    preparedTwoLevelTotalWork kernels I g ≤ (twoLevelParametersProgram m).work+
      preparedFixedDepthRealizedWorkCap kernels (rangeDeflationWorkCap kernels) I.fixed g Ck p0 := by
  rw [preparedTwoLevelTotalWork_eq]
  exact Nat.add_le_add_left
    (preparedFixedDepthTotalWork_bound_deflation kernels hClassical Ck p0 hC hp hK I.fixed g) _

end
end HierarchicalAbsoluteSpectral
