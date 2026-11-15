import HierarchicalAbsoluteSpectral.CorollaryTwoLevelParameters
import HierarchicalAbsoluteSpectral.MainStatementsAlgorithm

/-! An original-input caller of the actual fixed-depth program.  It
executes and charges the rounded scalar schedule before passing those
computed values into the same algorithm. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {N m r : ℕ}

structure TwoLevelProblem (N m r : ℕ) where
  A : Matrix (Fin N) (Fin m) ℝ
  B : Matrix (Fin m) (Fin N) ℝ
  delta : ℝ
  core_le_side : m ≤ N
  core_large : twoLevelMinimumCore ≤ m
  rank_positive : 1 ≤ r
  rank_le_power : r ≤ ⌈(m:ℝ)^(14/25:ℝ)⌉₊
  delta_positive : 0 < delta
  delta_lt_one : delta < 1

namespace TwoLevelProblem

theorem core_positive (I : TwoLevelProblem N m r) : 1 ≤ m :=
  (twoLevelMinimumCore_spec m I.core_large).1

theorem rank_le_core (I : TwoLevelProblem N m r) : r ≤ m :=
  I.rank_le_power.trans (twoLevelMinimumCore_spec m I.core_large).2.2.2.2

def fixedFromScalars (I : TwoLevelProblem N m r)
    (out : TwoLevelScalarParameters (m:ℝ)) : FixedProblem N m N r 1 where
  A := I.A
  B := I.B
  theta := out.theta
  delta := I.delta
  accuracy := fun j => if j = 0 then out.h0 else out.h1
  core_le_rows := I.core_le_side
  core_le_cols := I.core_le_side
  rank_positive := I.rank_positive
  rank_le_core := I.rank_le_core
  depth_positive := le_rfl
  theta_positive := by rw [out.theta_eq]; exact (twoLevelParameters_positive m).2.2
  delta_positive := I.delta_positive
  delta_lt_one := I.delta_lt_one
  accuracy_positive j _ := by
    split_ifs
    · rw [out.h0_eq]; exact (twoLevelParameters_positive m).1
    · rw [out.h1_eq]; exact (twoLevelParameters_positive m).2.1
  initial_accuracy_le := by
    simp only [ite_true]
    rw [out.h0_eq]
    exact (twoLevelMinimumCore_spec m I.core_large).2.1
  theta_le_last := by
    simp only [one_ne_zero,ite_false]
    rw [out.theta_eq,out.h1_eq]
    exact (twoLevelMinimumCore_spec m I.core_large).2.2.1
  refinement_ratio j hj := by
    have hj0 : j = 0 := by omega
    subst j
    simp only [Nat.zero_add,one_ne_zero,ite_false,ite_true]
    rw [out.h0_eq,out.h1_eq]
    exact (twoLevelMinimumCore_spec m I.core_large).2.2.2.1

def fixed (I : TwoLevelProblem N m r) : FixedProblem N m N r 1 :=
  I.fixedFromScalars (twoLevelCanonicalParameters m)

theorem fixedFromScalars_eq (I : TwoLevelProblem N m r) (out : TwoLevelScalarParameters (m:ℝ)) :
    I.fixedFromScalars out = I.fixed := by rw [out.eq_canonical]; rfl

@[simp] theorem fixed_theta (I : TwoLevelProblem N m r) : I.fixed.theta = twoLevelTheta m := rfl
@[simp] theorem fixed_accuracy (I : TwoLevelProblem N m r) (j : ℕ) :
    I.fixed.accuracy j = twoLevelAccuracy m j := rfl

def scalarCaller (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (out : TwoLevelScalarParameters (m:ℝ))
    (g : MainRandomTape I.fixed) : ArithmeticProgram (FixedRankOutput N N r) :=
  fixedDepthProgram kernels (I.fixedFromScalars out) ((I.fixedFromScalars_eq out).symm ▸ g)

theorem scalarCaller_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (out : TwoLevelScalarParameters (m:ℝ))
    (g : MainRandomTape I.fixed) :
    scalarCaller kernels I out g = fixedDepthProgram kernels I.fixed g := by
  rw [out.eq_canonical]
  rfl

end TwoLevelProblem

def twoLevelProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    ArithmeticProgram (FixedRankOutput N N r) := do
  let out ← twoLevelParametersProgram m
  I.scalarCaller kernels out g

theorem twoLevelProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (twoLevelProgram kernels I g).eval = (fixedDepthProgram kernels I.fixed g).eval := by
  simp only [twoLevelProgram,eval_bind,TwoLevelProblem.scalarCaller_eq]

theorem twoLevelProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (twoLevelProgram kernels I g).admissible := by
  simp only [twoLevelProgram,admissible_bind,twoLevelParametersProgram_admissible,true_and,
    TwoLevelProblem.scalarCaller_eq,fixedDepthProgram_admissible]

theorem twoLevelProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (twoLevelProgram kernels I g).work =
      (twoLevelParametersProgram m).work+(fixedDepthProgram kernels I.fixed g).work := by
  simp only [twoLevelProgram,work_bind,TwoLevelProblem.scalarCaller_eq]

theorem twoLevelProgram_preparation_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    ((twoLevelProgram kernels I g).work:ℝ) ≤
      ((fixedDepthProgram kernels I.fixed g).work:ℝ)+34+57*Real.log m/Real.log 2 := by
  rw [twoLevelProgram_work,Nat.cast_add]
  have hm : (1:ℝ) ≤ m := by exact_mod_cast I.core_positive
  have h := twoLevelParametersProgram_work_log m hm
  linarith

theorem twoLevelProgram_rank_cap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (twoLevelProgram kernels I g).eval.width ≤ r ∧
      (twoLevelProgram kernels I g).eval.product.rank ≤ r := by
  rw [twoLevelProgram_eval]
  exact fixedDepthProgram_rank_cap kernels I.fixed g

theorem twoLevelProgram_product (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (twoLevelProgram kernels I g).eval.product =
      (twoLevelProgram kernels I g).eval.left*(twoLevelProgram kernels I g).eval.right :=
  (twoLevelProgram kernels I g).eval.product_eq

end
end HierarchicalAbsoluteSpectral
