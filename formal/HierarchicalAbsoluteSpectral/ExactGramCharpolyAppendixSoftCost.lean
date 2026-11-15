import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixCost

/-! The explicit finite budget has the manuscript's soft fast-core shape.
Its only logarithms are dimension and tolerance logarithms. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix

theorem exactGramAppendixArithmeticBudget_draws_bound
    (C q : ℝ) (hC : 0 < C) (hq : 2 ≤ q) (m : ℕ) (hm : 1 ≤ m)
    (ε : ℝ) (hε : 0 < ε) :
    exactGramAppendixArithmeticBudget C q m ε hε+
      (exactGramAppendixSearchCap m ε hε*(m*m)+1+m*m:ℕ) ≤
      200*(C+1)*(Nat.clog 2 (m+1)+exactGramAppendixSearchCap m ε hε+1:ℕ)*
        ((2*(m+1):ℕ):ℝ)^q := by
  let l : ℝ := Nat.clog 2 (m+1)
  let c : ℝ := exactGramAppendixSearchCap m ε hε
  let F : ℝ := (C+1)*((2*(m+1):ℕ):ℝ)^q
  have hl : 0 ≤ l := Nat.cast_nonneg _
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hq0 : 0 ≤ q := by linarith
  have hbase : (1:ℝ) ≤ ((2*(m+1):ℕ):ℝ) := by exact_mod_cast (show 1 ≤ 2*(m+1) by omega)
  have hpow : (1:ℝ) ≤ ((2*(m+1):ℕ):ℝ)^q := Real.one_le_rpow hbase hq0
  have hF : 1 ≤ F := by dsimp only [F]; nlinarith
  have hmPow : (m:ℝ)^q ≤ ((2*(m+1):ℕ):ℝ)^q :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show m ≤ 2*(m+1) by omega)) hq0
  have hmSquare : (m:ℝ)^(2:ℝ) ≤ (m:ℝ)^q :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) hq
  have hcore : (C+1)*(m:ℝ)^q ≤ F :=
    mul_le_mul_of_nonneg_left hmPow (by linarith)
  have hsquare : (m:ℝ)*m ≤ F := by
    rw [Real.rpow_two, pow_two] at hmSquare
    have hto : ((2*(m+1):ℕ):ℝ)^q ≤ F := by dsimp only [F]; nlinarith
    exact (hmSquare.trans hmPow).trans hto
  have hmain : (76+105*c)*(C+1)*(m:ℝ)^q ≤ (76+105*c)*F := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcore (by positivity : 0 ≤ 76+105*c)
  have hscalar : 7*c+17 ≤ (7*c+17)*F := by
    nlinarith [mul_le_mul_of_nonneg_left hF (by positivity : 0 ≤ 7*c+17)]
  have hdraw : (exactGramAppendixSearchCap m ε hε*(m*m)+1+m*m:ℕ) ≤ (c+2)*F := by
    push_cast
    change c*((m:ℝ)*m)+1+(m:ℝ)*m ≤ (c+2)*F
    nlinarith [mul_le_mul_of_nonneg_left hsquare hc]
  have hfirst : 33*(C+1)*(Nat.clog 2 (m+1)+1:ℕ)*((2*(m+1):ℕ):ℝ)^q =
      33*(l+1)*F := by
    dsimp only [l,F]
    push_cast
    ring
  have hsum : 33*(l+1)*F+(76+105*c)*F+(7*c+17)*F+(c+2)*F ≤
      200*(l+c+1)*F := by
    calc
      _ = (33*l+113*c+128)*F := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hall : exactGramAppendixArithmeticBudget C q m ε hε+
      (exactGramAppendixSearchCap m ε hε*(m*m)+1+m*m:ℕ) ≤ 200*(l+c+1)*F := by
    apply le_trans _ hsum
    unfold exactGramAppendixArithmeticBudget
    rw [hfirst]
    change 33*(l+1)*F+(76+105*c)*(C+1)*(m:ℝ)^q+7*c+17+
      (exactGramAppendixSearchCap m ε hε*(m*m)+1+m*m:ℕ) ≤ _
    linarith
  convert hall using 1
  dsimp only [l,c,F]
  push_cast
  ring

def exactGramAppendixSoftBudget
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q : ℝ) (n m p r : ℕ) (θ : ℝ) (hθ : 0 < θ) : ℝ :=
  ((kernels m n m).cost:ℝ)+((kernels m p m).cost:ℝ)+
    200*(C+1)*(Nat.clog 2 (m+1)+exactGramAppendixSearchCap m (θ/100)
      (div_pos hθ (by norm_num))+1:ℕ)*((2*(m+1):ℕ):ℝ)^q+
    5*(matrixProductCost kernels n m r:ℝ)+2*(matrixProductCost kernels p m r:ℝ)+
    (matrixProductCost kernels n r p:ℝ)+(n*p:ℕ)+(m*(n+p):ℕ)

theorem exactGramAppendixFiniteBudget_le_soft
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q : ℝ) (hC : 0 < C) (hq : 2 ≤ q) (n m p r : ℕ) (hm : 1 ≤ m)
    (θ : ℝ) (hθ : 0 < θ) :
    exactGramAppendixFiniteBudget kernels C q n m p r θ hθ ≤
      exactGramAppendixSoftBudget kernels C q n m p r θ hθ := by
  have hb := exactGramAppendixArithmeticBudget_draws_bound C q hC hq m hm
    (θ/100) (div_pos hθ (by norm_num))
  unfold exactGramAppendixFiniteBudget exactGramAppendixSoftBudget
  linarith

theorem exactGramAppendixTotalWork_bound_soft
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q : ℝ) (hC : 0 < C) (hq : 2 ≤ q)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^q)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (θ : ℝ) (hθ : 0 < θ) (tape : ExactGramAppendixThetaTape kernels A B θ hθ)
    (hm : 1 ≤ m) :
    (exactGramAppendixTotalWork kernels A B r θ hθ tape:ℝ) ≤
      exactGramAppendixSoftBudget kernels C q n m p r θ hθ :=
  (exactGramAppendixTotalWork_bound kernels C q hC hq hK A B r θ hθ tape hm).trans
    (exactGramAppendixFiniteBudget_le_soft kernels C q hC hq n m p r hm θ hθ)

end
end HierarchicalAbsoluteSpectral
