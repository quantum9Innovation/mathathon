import HierarchicalAbsoluteSpectral.BaseMainFlexibleTotalCost
import HierarchicalAbsoluteSpectral.BaseMainTapeCost
import HierarchicalAbsoluteSpectral.MainPreparedProgram

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
variable {n m p r L : ℕ}

/-- Unit-cost independent Gaussian draws, followed by every executed real
arithmetic/comparison instruction of the actual prepared compiler. -/
def preparedFixedDepthTotalWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) : ℕ :=
  mainRandomizedWork I (preparedFixedDepthProgram kernels I g).work

theorem preparedFixedDepthTotalWork_eq
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    preparedFixedDepthTotalWork kernels I g=
      3*(L+1)*(2^dyadicPaddingLevel n+2^dyadicPaddingLevel p)+2*r*m+
        I.queryCap*I.repetitions*((r+1)*m+2*m*m)+
        (4*L+3*I.queryCap+2*I.repetitions+29)+(fixedDepthProgram kernels I g).work := by
  rw [preparedFixedDepthTotalWork,mainRandomizedWork_eq,preparedFixedDepthProgram_work]
  omega

def preparedFixedDepthRealizedWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (R : ℕ → ℕ → ℕ) (I : FixedProblem n m p r L) (g : MainRandomTape I) (Ck p0 : ℝ) : ℕ :=
  mainRandomizedWork I
    (4*L+3*I.queryCap+2*I.repetitions+29+fixedDepthFlexibleRealizedWorkCap kernels R I g Ck p0)

theorem preparedFixedDepthTotalWork_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (R : ℕ → ℕ → ℕ)
    (hR : ∀ a b (Y : Matrix (Fin a) (Fin b) ℝ), 1 ≤ a →
      (orthogonalRangeProgram kernels Y).work ≤ R a b)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    preparedFixedDepthTotalWork kernels I g ≤
      preparedFixedDepthRealizedWorkCap kernels R I g Ck p0 := by
  have hh := fixedDepthProgram_work_bound_flexible kernels R hR Ck p0 hC hp hK I g
  unfold preparedFixedDepthTotalWork preparedFixedDepthRealizedWorkCap mainRandomizedWork
  rw [preparedFixedDepthProgram_work]
  omega

theorem preparedFixedDepthTotalWork_bound_deflation
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (kernels a b c).cost ≤ 2*a*b*c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    preparedFixedDepthTotalWork kernels I g ≤ preparedFixedDepthRealizedWorkCap kernels
      (rangeDeflationWorkCap kernels) I g Ck p0 :=
  preparedFixedDepthTotalWork_bound kernels (rangeDeflationWorkCap kernels)
    (rangeDeflationWorkCap_correct kernels hClassical) Ck p0 hC hp hK I g

end
end HierarchicalAbsoluteSpectral
