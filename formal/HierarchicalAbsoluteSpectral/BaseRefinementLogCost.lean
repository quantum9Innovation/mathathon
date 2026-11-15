import HierarchicalAbsoluteSpectral.BaseMainOperatorCost
import HierarchicalAbsoluteSpectral.RuntimeFamilyLogBudgets
import HierarchicalAbsoluteSpectral.RuntimeFamilyRecurrence

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

theorem inverseRootLevel_log_bound (η τ : ℝ) (hη : 0 < η) (hη1 : η ≤ 1/8)
    (hτ : 0 < τ) (hτ1 : τ < 1/4) :
    (inverseRootLevel η τ hη hτ : ℝ) ≤ 34000*Real.log (1/(τ*η)) := by
  let n := inverseRootLevel η τ hη hτ
  let W := Real.log (1/(τ*η))
  have hW : 1 ≤ W := (inverseRoot_log_budget η τ hη hη1 hτ hτ1).1
  have hdeg := inverseRootLevel_degree_bound_simple η τ hη hη1 hτ hτ1
  have hlog := Real.log_le_log (show (0:ℝ)<(2:ℝ)^n by positivity) hdeg
  change Real.log ((2:ℝ)^n) ≤ Real.log ((17000/η)*W) at hlog
  rw [Real.log_pow,Real.log_mul (by positivity : (17000/η:ℝ)≠0) (by linarith : W≠0),
    Real.log_div (by norm_num : (17000:ℝ)≠0) hη.ne'] at hlog
  have hlogC := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<17000)
  have hlogW := Real.log_le_sub_one_of_pos (by linarith : 0<W)
  have hlogτ : Real.log τ ≤ 0 := Real.log_nonpos hτ.le (by linarith)
  have hsplit : W= -Real.log τ-Real.log η := by
    dsimp [W]
    rw [Real.log_div one_ne_zero (mul_pos hτ hη).ne',Real.log_one,Real.log_mul hτ.ne' hη.ne']
    ring
  have hn : (0:ℝ)≤n := Nat.cast_nonneg _
  have hlow := mul_le_mul_of_nonneg_left family_log_two_lower hn
  change (n:ℝ) ≤ 34000*W
  nlinarith

def refinementLogBudget (ε h B : ℝ) : ℝ :=
  Real.log (1/(refinementTolerance h B*(8*ε)))

theorem refinementActionEnvelope_log_bound
    (P T J : ℕ) (ε h B : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/1024)
    (hh : 0 < h) (hh1 : h ≤ 1/64) (hB : 0 ≤ B) (k b : ℕ) :
    (refinementActionEnvelope P T J ε h B hε hh hB k b:ℝ) ≤
      (100000000000/ε)*(refinementLogBudget ε h B)^2*
        ((P:ℝ)+(T:ℝ)+(J:ℝ)+(k:ℝ)*b+1) := by
  let η := 8*ε
  let τ := refinementTolerance h B
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1/8 := by dsimp [η]; linarith
  have hτ : 0 < τ := by dsimp [τ,refinementTolerance]; positivity
  have hτ1 : τ < 1/4 := by
    dsimp [τ,refinementTolerance]
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<10^6*(1+B))).mpr
    nlinarith
  let n := inverseRootLevel η τ hη hτ
  let W := refinementLogBudget ε h B
  let A : ℝ := (P:ℝ)+(T:ℝ)+(J:ℝ)+(k:ℝ)*b+1
  have hP : (0:ℝ)≤P := Nat.cast_nonneg _
  have hT : (0:ℝ)≤T := Nat.cast_nonneg _
  have hJ : (0:ℝ)≤J := Nat.cast_nonneg _
  have hkb : (0:ℝ)≤(k:ℝ)*b := by positivity
  have hW : 1 ≤ W := (inverseRoot_log_budget η τ hη hη1 hτ hτ1).1
  have hn : (n:ℝ) ≤ 34000*W := inverseRootLevel_log_bound η τ hη hη1 hτ hτ1
  have hdeg : ((2:ℝ)^n) ≤ (2125/ε)*W := by
    have hh' := inverseRootLevel_degree_bound_simple η τ hη hη1 hτ hτ1
    convert hh' using 1 <;> dsimp [η,W,refinementLogBudget,τ] <;> field_simp <;> ring
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hεinv : 1 ≤ 1/ε := (le_div_iff₀ hε).mpr (by linarith)
  have hW2 : 1 ≤ W^2 := by nlinarith
  have hWsq : W ≤ W^2 := by nlinarith
  have hprep : 80*((n:ℝ)+3)*(2:ℝ)^n ≤ (6000000000/ε)*W^2 := by
    have hn' : (n:ℝ)+3 ≤ 34003*W := by linarith
    have hm := mul_le_mul hn' hdeg (by positivity : 0≤(2:ℝ)^n) (by positivity : 0≤34003*W)
    have hm' := mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤80)
    have he : 80*(34003*W*((2125/ε)*W))=(5780510000/ε)*W^2 := by ring
    rw [he] at hm'
    calc
      _ = 80*(((n:ℝ)+3)*(2:ℝ)^n) := by ring
      _ ≤ (5780510000/ε)*W^2 := hm'
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right hε).mpr (by norm_num : (5780510000:ℝ)≤6000000000))
        (sq_nonneg W)
  have hcount : (P:ℝ)+(T:ℝ)+(J:ℝ)+6*(k:ℝ)*b ≤ 6*A := by dsimp [A]; nlinarith
  have hdegsq : (2:ℝ)^n ≤ (2125/ε)*W^2 :=
    hdeg.trans (mul_le_mul_of_nonneg_left hWsq (by positivity))
  have hprod := mul_le_mul hdegsq hcount (by positivity : 0≤(P:ℝ)+(T:ℝ)+(J:ℝ)+6*(k:ℝ)*b)
    (by positivity : 0≤(2125/ε)*W^2)
  have hbase : 7+max (P:ℝ) (T:ℝ)+(k:ℝ)*b ≤ 7*A := by
    have hh' : 7+max P T+k*b ≤ 7*(P+T+J+k*b+1) := by omega
    dsimp [A]
    exact_mod_cast hh'
  have hbase' : 7*A ≤ (7/ε)*W^2*A := by
    have he : 1 ≤ (1/ε)*W^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hεinv) (sub_nonneg.mpr hW2)]
    have hm := mul_le_mul_of_nonneg_right he (by positivity : 0≤7*A)
    calc
      _ ≤ ((1/ε)*W^2)*(7*A) := by simpa only [one_mul] using hm
      _ = _ := by ring
  have hprep' : (6000000000/ε)*W^2 ≤ (6000000000/ε)*W^2*A := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hA (by positivity : 0≤(6000000000/ε)*W^2)
  have he : (refinementActionEnvelope P T J ε h B hε hh hB k b:ℝ)=
      7+80*((n:ℝ)+3)*(2:ℝ)^n+max (P:ℝ) (T:ℝ)+(k:ℝ)*b+
        (2:ℝ)^n*((P:ℝ)+(T:ℝ)+(J:ℝ)+6*(k:ℝ)*b) := by
    unfold refinementActionEnvelope
    change ((7+80*(n+3)*2^n+max P T+k*b+2^n*(P+T+J+6*k*b):ℕ):ℝ)=_
    push_cast
    ring
  rw [he]
  change _ ≤ (100000000000/ε)*W^2*A
  have hsum := add_le_add (add_le_add (hbase.trans hbase') (hprep.trans hprep')) hprod
  calc
    _ = (7+max (P:ℝ) (T:ℝ)+(k:ℝ)*b)+80*((n:ℝ)+3)*(2:ℝ)^n+
      (2:ℝ)^n*((P:ℝ)+(T:ℝ)+(J:ℝ)+6*(k:ℝ)*b) := by ring
    _ ≤ (7/ε)*W^2*A+(6000000000/ε)*W^2*A+((2125/ε)*W^2)*(6*A) := hsum
    _ = (6000012757/ε)*W^2*A := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right hε).mpr (by norm_num : (6000012757:ℝ)≤100000000000))
          (sq_nonneg W)) (by linarith)

end
end HierarchicalAbsoluteSpectral
