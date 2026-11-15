import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixTheta
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixCoreCost

/-! Complete original-input arithmetic and bookkeeping budgets for the
exact-Gram appendix, including the true Grams, the actual fast charpoly,
capped exact inertia search, random lift, explicit outputs, and all finite
Gaussian coordinates. No certificate-success hypothesis is used. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
open scoped Matrix.Norms.L2Operator

def exactGramAppendixArithmeticBudget (C q : ℝ) (m : ℕ) (ε : ℝ) (hε : 0 < ε) : ℝ :=
  33*(C+1)*(Nat.clog 2 (m+1)+1:ℕ)*((2*(m+1):ℕ):ℝ)^q+
    (76+105*(exactGramAppendixSearchCap m ε hε:ℝ))*(C+1)*(m:ℝ)^q+
    7*(exactGramAppendixSearchCap m ε hε:ℝ)+17

def exactGramAppendixFiniteBudget
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q : ℝ) (n m p r : ℕ) (θ : ℝ) (hθ : 0 < θ) : ℝ :=
  ((kernels m n m).cost:ℝ)+((kernels m p m).cost:ℝ)+
    exactGramAppendixArithmeticBudget C q m (θ/100) (div_pos hθ (by norm_num))+
    5*(matrixProductCost kernels n m r:ℝ)+2*(matrixProductCost kernels p m r:ℝ)+
    (matrixProductCost kernels n r p:ℝ)+
    (exactGramAppendixSearchCap m (θ/100) (div_pos hθ (by norm_num))*(m*m)+1+m*m:ℕ)+
    (n*p:ℕ)+(m*(n+p):ℕ)

theorem exactGramAppendixThetaProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q : ℝ) (hC : 0 < C) (hq : 2 ≤ q)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^q)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (θ : ℝ) (hθ : 0 < θ) (tape : ExactGramAppendixThetaTape kernels A B θ hθ)
    (hm : 1 ≤ m) :
    ((exactGramAppendixThetaProgram kernels A B r θ hθ tape).work:ℝ) ≤
      ((kernels m n m).cost:ℝ)+((kernels m p m).cost:ℝ)+
        exactGramAppendixArithmeticBudget C q m (θ/100) (div_pos hθ (by norm_num))+
        4*(matrixProductCost kernels n m r:ℝ)+(matrixProductCost kernels p m r:ℝ)+
        (matrixProductCost kernels n r p:ℝ) := by
  have hsupport := exactGramAppendixSupportProgram_work_bound kernels C q hC hq hK A B hm
  have hcore := exactGramAppendixCoreProgram_work_bound_rectangular kernels C q
    (matrixProductCost kernels n m r:ℝ) (matrixProductCost kernels p m r:ℝ)
    (matrixProductCost kernels n r p:ℝ) hC hq hK (exactGramAppendixCanonicalSupport kernels A B)
    r (θ/100) (div_pos hθ (by norm_num)) tape hm
    (exactGramAppendixPhysicalBudget_actual kernels n m p r)
  rw [exactGramAppendixThetaProgram_work, exactGramAppendixProgram_work]
  push_cast
  unfold exactGramAppendixArithmeticBudget exactGramAppendixCoreWorkBudget at *
  linarith

/-- A dimension/accuracy logarithmic search bound, with no input spectral
ratio. The characteristic-polynomial initializer starts in a k² bracket. -/
theorem exactGramAppendixThetaSearchCap_le_clog (m : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    exactGramAppendixSearchCap m (θ/100) (div_pos hθ (by norm_num)) ≤
      Nat.clog 2 ⌈100*(m:ℝ)^2/θ⌉₊ := by
  have hratio : (m:ℝ)^2/(θ/100) = 100*(m:ℝ)^2/θ := by ring
  simpa only [hratio] using
    exactGramAppendixSearchCap_le_clog m (θ/100) (div_pos hθ (by norm_num))

/-- The actual returned width determines the two literal factor-write
counts. Their feasible physical product costs absorb these entries. -/
theorem exactGramAppendixThetaProgram_factorWrites_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (θ : ℝ) (hθ : 0 < θ) (tape : ExactGramAppendixThetaTape kernels A B θ hθ) :
    n*(exactGramAppendixThetaProgram kernels A B r θ hθ tape).eval.width+
      (exactGramAppendixThetaProgram kernels A B r θ hθ tape).eval.width*p ≤
      matrixProductCost kernels n m r+matrixProductCost kernels p m r := by
  have hw := exactGramAppendixThetaProgram_width kernels A B r θ hθ tape
  have hl := Nat.mul_le_mul_left n hw
  have hr := Nat.mul_le_mul_right p hw
  have hleft : n*r ≤ matrixProductCost kernels n m r := by
    unfold matrixProductCost
    have hcomm := Nat.mul_comm n r
    omega
  have hright : r*p ≤ matrixProductCost kernels p m r := by
    unfold matrixProductCost
    omega
  exact (Nat.add_le_add hl hr).trans (Nat.add_le_add hleft hright)

/-- This includes every arithmetic instruction on every outcome, all
Gaussian coordinates, both returned factors, every dense product entry,
and dense input reads. -/
theorem exactGramAppendixTotalWork_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q : ℝ) (hC : 0 < C) (hq : 2 ≤ q)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^q)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (θ : ℝ) (hθ : 0 < θ) (tape : ExactGramAppendixThetaTape kernels A B θ hθ)
    (hm : 1 ≤ m) :
    (exactGramAppendixTotalWork kernels A B r θ hθ tape:ℝ) ≤
      exactGramAppendixFiniteBudget kernels C q n m p r θ hθ := by
  have hwork := exactGramAppendixThetaProgram_work_bound kernels C q hC hq hK A B r θ hθ tape hm
  have hdraw : (exactGramAppendixThetaGaussianDraws kernels A B θ hθ:ℝ) ≤
      (exactGramAppendixSearchCap m (θ/100) (div_pos hθ (by norm_num))*(m*m)+1+m*m:ℕ) := by
    exact_mod_cast exactGramAppendixThetaGaussianDraws_le kernels A B θ hθ
  have hfactors : ((n*(exactGramAppendixThetaProgram kernels A B r θ hθ tape).eval.width+
      (exactGramAppendixThetaProgram kernels A B r θ hθ tape).eval.width*p:ℕ):ℝ) ≤
      (matrixProductCost kernels n m r:ℝ)+(matrixProductCost kernels p m r:ℝ) := by
    exact_mod_cast exactGramAppendixThetaProgram_factorWrites_bound kernels A B r θ hθ tape
  unfold exactGramAppendixTotalWork exactGramAppendixFiniteBudget
  push_cast
  push_cast at hdraw hfactors
  linarith

structure ExactGramAppendixGuarantee
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C q : ℝ)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (θ : ℝ) (hθ : 0 < θ) : Prop where
  admissible : ∀ tape, (exactGramAppendixThetaProgram kernels A B r θ hθ tape).admissible
  width : ∀ tape, (exactGramAppendixThetaProgram kernels A B r θ hθ tape).eval.width ≤ r
  error_probability : (exactGramAppendixThetaLaw kernels A B θ hθ)
    {tape | ‖A*B-(exactGramAppendixThetaProgram kernels A B r θ hθ tape).eval.product‖ ≤
      (1+θ/100)*tailSingularValue (A*B) r} = 1
  work : ∀ tape, (exactGramAppendixTotalWork kernels A B r θ hθ tape:ℝ) ≤
    exactGramAppendixFiniteBudget kernels C q n m p r θ hθ

theorem exactGramAppendixGuarantee_of_kernels
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q : ℝ) (hC : 0 < C) (hq : 2 ≤ q)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^q)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (θ : ℝ) (hθ : 0 < θ) (hm : 1 ≤ m) :
    ExactGramAppendixGuarantee kernels C q A B r θ hθ where
  admissible := exactGramAppendixThetaProgram_admissible kernels A B r θ hθ
  width := exactGramAppendixThetaProgram_width kernels A B r θ hθ
  error_probability := exactGramAppendixThetaProgram_error_probability kernels A B r θ hθ
  work := fun tape => exactGramAppendixTotalWork_bound kernels C q hC hq hK A B r θ hθ tape hm

/-- A single family of actual verified fast multiplication circuits
instantiates the complete original-input comparator, simultaneously for
every matrix, rank, positive tolerance, and positive inner dimension. -/
theorem exists_fast_exactGramAppendixComparator (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ), 0 < C ∧
      (∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
        ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^(9/4+ζ)) ∧
      ∀ (n m p : ℕ) (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
        (r : ℕ) (θ : ℝ) (hθ : 0 < θ), 1 ≤ m →
          ExactGramAppendixGuarantee kernels C (9/4+ζ) A B r θ hθ := by
  obtain ⟨kernels,C,hC,hK⟩ := exists_full_shape_arithmetic_kernels ζ hζ
  refine ⟨kernels,C,hC,hK,?_⟩
  intro n m p A B r θ hθ hm
  exact exactGramAppendixGuarantee_of_kernels kernels C (9/4+ζ) hC (by linarith) hK A B r θ hθ hm

end
end HierarchicalAbsoluteSpectral
