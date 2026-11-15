import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! The support function of the weighted quadratic character constraints.
The formula is symmetric in the three shape exponents and is continuous on
the strictly positive octant. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter Topology

def ScaleneQuadraticCap (pX pY pZ : ℝ) : Prop :=
  ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
    4*(pX*y*z+pY*x*z+pZ*x*y) ≤ (x+y+z)^2

def scaleneRationalBound (a b c : ℝ) : ℝ := (a*b+b*c+c*a)^2/(4*a*b*c)

def scaleneCurve (a b c : ℝ) : ℝ :=
  a+b+(max 0 (c*(a+b)-a*b))^2/(4*a*b*c)

def scaleneBound (a b c : ℝ) : ℝ :=
  let m := min a (min b c)
  let s := a+b+c-m
  s+(max 0 (2*m*s-(a*b+b*c+c*a)))^2/(4*a*b*c)

theorem scaleneQuadraticCap_swapXZ {pX pY pZ : ℝ}
    (h : ScaleneQuadraticCap pX pY pZ) : ScaleneQuadraticCap pZ pY pX := by
  intro x y z hx hy hz
  have hh := h z y x hz hy hx
  nlinarith only [hh]

theorem scaleneQuadraticCap_cyclic {pX pY pZ : ℝ}
    (h : ScaleneQuadraticCap pX pY pZ) : ScaleneQuadraticCap pY pZ pX := by
  intro x y z hx hy hz
  have hh := h z x y hz hx hy
  nlinarith only [hh]

theorem scaleneRationalBound_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) : 0 ≤ scaleneRationalBound a b c := by
  exact div_nonneg (sq_nonneg _) (by positivity)

theorem scaleneCurve_of_input_optimal {a b c : ℝ} (h : c*(a+b) ≤ a*b) :
    scaleneCurve a b c = a+b := by
  simp only [scaleneCurve,max_eq_left (by linarith : c*(a+b)-a*b ≤ 0),zero_pow (by omega : 2 ≠ 0),
    zero_div,add_zero]

theorem scaleneCurve_of_dense {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (h : a*b ≤ c*(a+b)) :
    scaleneCurve a b c = scaleneRationalBound a b c := by
  simp only [scaleneCurve,scaleneRationalBound,max_eq_right (by linarith : 0 ≤ c*(a+b)-a*b)]
  field_simp
  ring

theorem scalene_pair_objective_le {pX pY pZ a b c : ℝ}
    (hcap : ScaleneQuadraticCap pX pY pZ) (hpX : 0 ≤ pX)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hca : c ≤ a)
    (hboundary : c*(a+b) ≤ a*b) : a*pY+b*pZ+c*pX ≤ a+b := by
  by_cases hs : 0 < a+b
  · have h := hcap (a+b) b a (by positivity) hb ha
    have hterm := mul_le_mul_of_nonneg_right hboundary hpX
    have hmul : (a+b)*(a*pY+b*pZ+c*pX) ≤ (a+b)*(a+b) := by
      nlinarith only [h,hterm]
    exact le_of_mul_le_mul_left hmul hs
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    simp [ha0,hb0,hc0]

theorem scalene_rational_objective_le {pX pY pZ a b c : ℝ}
    (hcap : ScaleneQuadraticCap pX pY pZ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a*pY+b*pZ+c*pX ≤ scaleneRationalBound a b c := by
  have h := hcap (a*b) (b*c) (c*a) (by positivity) (by positivity) (by positivity)
  apply (le_div_iff₀ (by positivity : 0 < 4*a*b*c)).mpr
  nlinarith only [h]

theorem scalene_curve_objective_le {pX pY pZ a b c : ℝ}
    (hcap : ScaleneQuadraticCap pX pY pZ) (hpX : 0 ≤ pX)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b) :
    a*pY+b*pZ+c*pX ≤ scaleneCurve a b c := by
  by_cases h : c*(a+b) ≤ a*b
  · rw [scaleneCurve_of_input_optimal h]
    exact scalene_pair_objective_le hcap hpX ha hb hc hca h
  · have hcpos : 0 < c := by
      by_contra hn
      have hc0 : c = 0 := le_antisymm (not_lt.mp hn) hc
      have hh : c*(a+b) ≤ a*b := by
        simpa only [hc0,zero_mul] using mul_nonneg ha hb
      exact h hh
    have hapos : 0 < a := hcpos.trans_le hca
    have hbpos : 0 < b := hcpos.trans_le hcb
    rw [scaleneCurve_of_dense hapos hbpos hcpos (not_le.mp h).le]
    exact scalene_rational_objective_le hcap hapos hbpos hcpos

theorem scaleneBound_eq_curve {a b c : ℝ} (hca : c ≤ a) (hcb : c ≤ b) :
    scaleneBound a b c = scaleneCurve a b c := by
  have hs : a+b+c-c = a+b := by ring
  have hd : 2*c*(a+b)-(a*b+b*c+c*a) = c*(a+b)-a*b := by ring
  simp only [scaleneBound,min_eq_right hcb,min_eq_right hca,hs,hd,scaleneCurve]

theorem scaleneBound_swap {a b c : ℝ} : scaleneBound a b c = scaleneBound a c b := by
  have hm : min a (min b c) = min a (min c b) := by rw [min_comm b c]
  have hs : a+b+c = a+c+b := by ring
  have hp : a*b+b*c+c*a = a*c+c*b+b*a := by ring
  have hd : 4*a*b*c = 4*a*c*b := by ring
  simp only [scaleneBound,hm,hs,hp,hd]

theorem scaleneBound_cyclic {a b c : ℝ} : scaleneBound a b c = scaleneBound b c a := by
  have hm : min a (min b c) = min b (min c a) := by
    simp only [min_assoc,min_comm,min_left_comm]
  have hs : a+b+c = b+c+a := by ring
  have hp : a*b+b*c+c*a = b*c+c*a+a*b := by ring
  have hd : 4*a*b*c = 4*b*c*a := by ring
  simp only [scaleneBound,hm,hs,hp,hd]

theorem scaleneBound_swapFirst {a b c : ℝ} : scaleneBound a b c = scaleneBound b a c :=
  scaleneBound_cyclic.trans scaleneBound_swap

theorem scalene_objective_le {pX pY pZ a b c : ℝ}
    (hcap : ScaleneQuadraticCap pX pY pZ) (hpX : 0 ≤ pX)
    (hpY : 0 ≤ pY) (hpZ : 0 ≤ pZ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a*pY+b*pZ+c*pX ≤ scaleneBound a b c := by
  by_cases hca : c ≤ a
  · by_cases hcb : c ≤ b
    · rw [scaleneBound_eq_curve hca hcb]
      exact scalene_curve_objective_le hcap hpX ha hb hc hca hcb
    · have hba : b ≤ a := (not_le.mp hcb).le.trans hca
      have hbc : b ≤ c := (not_le.mp hcb).le
      rw [scaleneBound_swap,scaleneBound_eq_curve hba hbc]
      have h := scalene_curve_objective_le (scaleneQuadraticCap_swapXZ hcap) hpZ
        ha hc hb hba hbc
      nlinarith only [h]
  · have hac : a ≤ c := (not_le.mp hca).le
    by_cases hab : a ≤ b
    · rw [scaleneBound_cyclic,scaleneBound_eq_curve hab hac]
      have h := scalene_curve_objective_le (scaleneQuadraticCap_cyclic hcap) hpY
        hb hc ha hab hac
      nlinarith only [h]
    · have hba : b ≤ a := (not_le.mp hab).le
      have hbc : b ≤ c := hba.trans hac
      rw [scaleneBound_swap,scaleneBound_eq_curve hba hbc]
      have h := scalene_curve_objective_le (scaleneQuadraticCap_swapXZ hcap) hpZ
        ha hc hb hba hbc
      nlinarith only [h]

theorem scaleneBound_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ scaleneBound a b c := by
  have hm : min a (min b c) ≤ c := (min_le_right _ _).trans (min_le_right _ _)
  have hs : 0 ≤ a+b+c-min a (min b c) := by linarith
  exact add_nonneg hs (div_nonneg (sq_nonneg _) (by positivity))

theorem scaleneBound_of_sorted {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hba : b ≤ a) (hcb : c ≤ b) :
    scaleneBound a b c = if c*(a+b) ≤ a*b then a+b else scaleneRationalBound a b c := by
  rw [scaleneBound_eq_curve (hcb.trans hba) hcb]
  split_ifs with h
  · exact scaleneCurve_of_input_optimal h
  · have hcpos : 0 < c := by
      by_contra hn
      have hc0 : c = 0 := le_antisymm (not_lt.mp hn) hc
      exact h (by simpa only [hc0,zero_mul] using mul_nonneg ha hb)
    exact scaleneCurve_of_dense (hcpos.trans_le (hcb.trans hba))
      (hcpos.trans_le hcb) hcpos (not_le.mp h).le

theorem continuousAt_scaleneBound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ContinuousAt (fun t : ℝ × ℝ × ℝ => scaleneBound t.1 t.2.1 t.2.2) (a,b,c) := by
  unfold scaleneBound
  fun_prop (disch := positivity)

/-- A small increase in each dimension costs arbitrarily little exponent.
This is used to absorb logarithmic sketch sizes and fixed width factors. -/
theorem exists_scalene_shape_slack {a b c ε : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ scaleneBound (a+δ) (b+δ) (c+δ) < scaleneBound a b c+ε := by
  have hcont : ContinuousAt (fun δ : ℝ => scaleneBound (a+δ) (b+δ) (c+δ)) 0 := by
    unfold scaleneBound
    fun_prop (disch := positivity)
  have hnear : ∀ᶠ δ : ℝ in nhds 0,
      scaleneBound (a+δ) (b+δ) (c+δ) < scaleneBound a b c+ε :=
    hcont.eventually (eventually_lt_nhds (by simpa using
      (lt_add_of_pos_right (scaleneBound a b c) hε)))
  obtain ⟨r,hr,hrad⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨r/2,by positivity,hrad ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity : 0 ≤ r/2)]
  linarith

theorem scaleneBound_coarse : scaleneBound (57/50) 1 1 = (3362:ℝ)/1425 := by
  norm_num [scaleneBound]

theorem scaleneBound_true : scaleneBound (59/50) 1 (14/25) = (9006001:ℝ)/4130000 := by
  norm_num [scaleneBound]

theorem scaleneBound_fine : scaleneBound (7/6) 1 (14/25) = (867:ℝ)/400 := by
  norm_num [scaleneBound]

end
end HierarchicalAbsoluteSpectral
