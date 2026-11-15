import HierarchicalAbsoluteSpectral.BaseMainRandomizedCost

/-! Entry access accounting for the explicit-output theorem. The three
returned matrices have exactly the entry counts below, including a zero
returned rank. This is added to all Gaussian and arithmetic instructions. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
variable {n m p r L : ℕ}

def FixedRankOutput.entryCount (out : FixedRankOutput n p r) : ℕ :=
  n*out.width+out.width*p+n*p

theorem FixedRankOutput.entryCount_eq (out : FixedRankOutput n p r) :
    out.entryCount=Fintype.card (Fin n × Fin out.width)+
      Fintype.card (Fin out.width × Fin p)+Fintype.card (Fin n × Fin p) := by
  simp only [FixedRankOutput.entryCount,Fintype.card_prod,Fintype.card_fin]

theorem FixedRankOutput.entryCount_le (out : FixedRankOutput n p r) (hr : r ≤ m) :
    out.entryCount ≤ m*(n+p)+n*p := by
  have hw := out.width_le.trans hr
  have ha := Nat.mul_le_mul_left n hw
  have hb := Nat.mul_le_mul_right p hw
  dsimp only [FixedRankOutput.entryCount]
  nlinarith

/-- Input reads, writes of both factors and every dense output entry,
independent Gaussian draws, and all executed field/root/comparison steps. -/
def preparedFixedDepthExplicitWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) : ℕ :=
  m*(n+p)+(preparedFixedDepthProgram kernels I g).eval.entryCount+
    preparedFixedDepthTotalWork kernels I g

theorem preparedFixedDepthExplicitWork_le
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    preparedFixedDepthExplicitWork kernels I g ≤
      2*m*(n+p)+n*p+preparedFixedDepthTotalWork kernels I g := by
  have hh := ((preparedFixedDepthProgram kernels I g).eval).entryCount_le I.rank_le_core
  unfold preparedFixedDepthExplicitWork
  nlinarith

theorem preparedFixedDepthExplicitWork_bound_deflation
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (kernels a b c).cost ≤ 2*a*b*c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ Ck*(N : ℝ)^p0)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    preparedFixedDepthExplicitWork kernels I g ≤ 2*m*(n+p)+n*p+
      preparedFixedDepthRealizedWorkCap kernels (rangeDeflationWorkCap kernels) I g Ck p0 := by
  exact (preparedFixedDepthExplicitWork_le kernels I g).trans
    (Nat.add_le_add_left (preparedFixedDepthTotalWork_bound_deflation kernels hClassical
      Ck p0 hC hp hK I g) _)

end
end HierarchicalAbsoluteSpectral
