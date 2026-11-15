import Matmul.IntegerProfileLaws
import Matmul.DiscretePotential
import HierarchicalAbsoluteSpectral.CoarseAlgebraScaleneConcavity

/-! Weighted quadratic constraints for actual integral tensor characters.
The input profiles are the coefficient-level convolution tensors, and every
concavity and tripling inequality comes from their integral degenerations. -/

namespace HierarchicalAbsoluteSpectral.ScaleneCharacter

open Matmul Matmul.ConvolutionCharacter Matmul.IntegerProfileLaws
open Matmul.IntegralCharacter
open Filter Topology

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

@[simp] theorem pairedXY_self (φ : IntegralCharacter) (r s : ℕ) :
    pairedXY φ φ r s = valueXY φ r s := by
  rw [pairedXY, ← pow_two, Real.sqrt_sq (valueXY_nonneg φ r s)]

@[simp] theorem pairedXZ_self (φ : IntegralCharacter) (r s : ℕ) :
    pairedXZ φ φ r s = valueXZ φ r s := by
  rw [pairedXZ, ← pow_two, Real.sqrt_sq (valueXZ_nonneg φ r s)]

theorem poweredXY_second_difference (φ : IntegralCharacter) (hp : 0 < φ.pX)
    (a k : ℕ) (ha : 1 ≤ a) (hk : 2 ≤ k) :
    valueXY φ a (k+1) ^ (1/φ.pX) + valueXY φ a (k-1) ^ (1/φ.pX) ≤
      2 * valueXY φ a k ^ (1/φ.pX) := by
  have h := pairedXY_second_difference φ φ (by simpa using hp) a k ha hk
  simpa using h

theorem poweredXY_concave (φ : IntegralCharacter) (hp : 0 < φ.pX)
    (a : ℕ) (ha : 1 ≤ a) :
    Antitone (fun k => valueXY φ a (k+2) ^ (1/φ.pX) -
      valueXY φ a (k+1) ^ (1/φ.pX)) := by
  apply antitone_positive_increments_of_second_difference
    (f := fun k => valueXY φ a k ^ (1/φ.pX))
  intro k hk
  exact poweredXY_second_difference φ hp a k ha hk

theorem poweredXZ_concave (φ : IntegralCharacter) (hp : 0 < φ.pX)
    (a : ℕ) (ha : 1 ≤ a) :
    Antitone (fun k => valueXZ φ a (k+2) ^ (1/φ.pX) -
      valueXZ φ a (k+1) ^ (1/φ.pX)) := by
  simpa only [swapYZ_pX, swapYZ_valueXY] using
    poweredXY_concave (swapYZCharacter φ) (by simpa only [swapYZ_pX] using hp) a ha

theorem poweredXY_tripling (φ : IntegralCharacter) (hp : 0 < φ.pX)
    (a k : ℕ) (ha : 1 ≤ a) (hk : 1 ≤ k) :
    2 * valueXY φ a k ^ (1/φ.pX) + valueXZ φ a k ^ (1/φ.pX) ≤
      valueXY φ a (3*k+a-1) ^ (1/φ.pX) := by
  have h := pairedXY_tripling φ φ (by simpa using hp) a k ha hk
  simpa using h

theorem poweredXZ_tripling (φ : IntegralCharacter) (hp : 0 < φ.pX)
    (a k : ℕ) (ha : 1 ≤ a) (hk : 1 ≤ k) :
    2 * valueXZ φ a k ^ (1/φ.pX) + valueXY φ a k ^ (1/φ.pX) ≤
      valueXZ φ a (3*k+a-1) ^ (1/φ.pX) := by
  simpa only [swapYZ_pX, swapYZ_valueXY, swapYZ_valueXZ] using
    poweredXY_tripling (swapYZCharacter φ) (by simpa only [swapYZ_pX] using hp) a k ha hk

def pairIncrement (φ : IntegralCharacter) (a u v r s : ℕ) : ℝ :=
  (s:ℝ)*(Real.log (valueXY φ a (u+r))-Real.log (valueXY φ a u)) +
  (r:ℝ)*(Real.log (valueXZ φ a (v+s))-Real.log (valueXZ φ a v))

theorem paired_log_growth (φ : IntegralCharacter) (a u v r s : ℕ)
    (ha : 1 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    4*φ.pX*(r:ℝ)*s/((u:ℝ)+v+r+s+a-1) ≤ pairIncrement φ a u v r s := by
  by_cases hp : 0 < φ.pX
  · have h := ScaleneConcavity.coupled_log_increment (a := a) (u := u) (v := v)
      (r := r) (s := s) ha hu hv
      (fun k hk => Real.rpow_pos_of_pos (valueXY_pos φ a k ha hk) _)
      (fun k hk => Real.rpow_pos_of_pos (valueXZ_pos φ a k ha hk) _)
      (poweredXY_concave φ hp a ha) (poweredXZ_concave φ hp a ha)
      (fun k hk => poweredXY_tripling φ hp a k ha hk)
      (fun k hk => poweredXZ_tripling φ hp a k ha hk)
    have hm := mul_le_mul_of_nonneg_left h hp.le
    rw [Real.log_rpow (valueXY_pos φ a (u+r) ha (by omega)),
      Real.log_rpow (valueXY_pos φ a u ha hu),
      Real.log_rpow (valueXZ_pos φ a (v+s) ha (by omega)),
      Real.log_rpow (valueXZ_pos φ a v ha hv)] at hm
    have he : φ.pX*((s:ℝ)*((1/φ.pX)*Real.log (valueXY φ a (u+r))-
        (1/φ.pX)*Real.log (valueXY φ a u))+
        (r:ℝ)*((1/φ.pX)*Real.log (valueXZ φ a (v+s))-
        (1/φ.pX)*Real.log (valueXZ φ a v))) = pairIncrement φ a u v r s := by
      dsimp [pairIncrement]
      field_simp [hp.ne']
    rw [he] at hm
    have heL : φ.pX*(4*(r:ℝ)*s/((u:ℝ)+v+r+s+a-1)) =
        4*φ.pX*(r:ℝ)*s/((u:ℝ)+v+r+s+a-1) := by ring
    rw [heL] at hm
    exact hm
  · have hp0 : φ.pX = 0 := le_antisymm (not_lt.mp hp) φ.pX_nonneg
    rw [hp0]
    simp only [mul_zero, zero_mul, zero_div]
    unfold pairIncrement
    apply add_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _)
      exact sub_nonneg.mpr (Real.log_le_log (valueXY_pos φ a u ha hu)
        (valueXY_mono_second φ a u (u+r) (by omega)))
    · apply mul_nonneg (Nat.cast_nonneg _)
      exact sub_nonneg.mpr (Real.log_le_log (valueXZ_pos φ a v ha hv)
        (valueXZ_mono_second φ a v (v+s) (by omega)))

def axisIncrement (φ : IntegralCharacter) (a n r s : ℕ) : ℝ :=
  (s:ℝ)*(Real.log (valueXY φ a ((n+1)*r))-Real.log (valueXY φ a (n*r))) +
  (r:ℝ)*(Real.log (valueXZ φ a ((n+1)*s))-Real.log (valueXZ φ a (n*s)))

theorem axis_log_growth (φ : IntegralCharacter) (a n r s : ℕ) (S : ℝ)
    (ha : 1 ≤ a) (hn : 1 ≤ n) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hD : (n:ℝ)*r+(n:ℝ)*s+r+s+a-1 ≤ ((n:ℝ)+1)*S) :
    4*φ.pX*(r:ℝ)*s/(((n:ℝ)+1)*S) ≤ axisIncrement φ a n r s := by
  have h := paired_log_growth φ a (n*r) (n*s) r s ha
    (one_le_mul hn hr) (one_le_mul hn hs)
  simp only [Nat.cast_mul] at h
  have hden : 0 < (n:ℝ)*r+(n:ℝ)*s+r+s+a-1 := by
    have hnr : (1:ℝ) ≤ n*r := by exact_mod_cast one_le_mul hn hr
    have hns : (1:ℝ) ≤ n*s := by exact_mod_cast one_le_mul hn hs
    have haR : (1:ℝ) ≤ a := by exact_mod_cast ha
    have hrR : (0:ℝ) ≤ r := Nat.cast_nonneg _
    have hsR : (0:ℝ) ≤ s := Nat.cast_nonneg _
    linarith
  have hp0 := φ.pX_nonneg
  have hl := div_le_div_of_nonneg_left
    (show 0 ≤ 4*φ.pX*(r:ℝ)*s by positivity) hden hD
  have heq_r : n*r+r = (n+1)*r := by simp [Nat.add_mul]
  have heq_s : n*s+s = (n+1)*s := by simp [Nat.add_mul]
  simpa only [Nat.cast_mul, pairIncrement, axisIncrement, heq_r, heq_s] using hl.trans h

def potential (φ : IntegralCharacter) (x y z n : ℕ) : ℝ :=
  2*(z:ℝ)*Real.log (valueXY φ (n*x) (n*y)) +
  2*(y:ℝ)*Real.log (valueXZ φ (n*x) (n*z)) +
  2*(x:ℝ)*Real.log (valueYZ φ (n*y) (n*z))

theorem profile_log_upper {V S : ℝ} {n : ℕ} (hV : 0 < V)
    (hn : 1 ≤ n) (hS : 0 < S) (hbound : V ≤ (n:ℝ)*S) :
    Real.log V ≤ Real.log n + Real.log S := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h := Real.log_le_log hV hbound
  rwa [Real.log_mul hnR.ne' hS.ne'] at h

theorem potential_upper (φ : IntegralCharacter) (x y z n : ℕ)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) (hn : 1 ≤ n) :
    potential φ x y z n ≤ 2*((x:ℝ)+y+z)*Real.log n +
      2*((x:ℝ)+y+z)*Real.log ((x:ℝ)+y+z) := by
  have hnx : 1 ≤ n*x := one_le_mul hn hx
  have hny : 1 ≤ n*y := one_le_mul hn hy
  have hnz : 1 ≤ n*z := one_le_mul hn hz
  have hS : 0 < (x:ℝ)+y+z := by
    have hxR : (1:ℝ) ≤ x := by exact_mod_cast hx
    have hyR : (0:ℝ) ≤ y := Nat.cast_nonneg _
    have hzR : (0:ℝ) ≤ z := Nat.cast_nonneg _
    linarith
  have hxy := valueXY_le φ (n*x) (n*y) hnx hny
  have hxz := valueXZ_le φ (n*x) (n*z) hnx hnz
  have hyz := valueYZ_le φ (n*y) (n*z) hny hnz
  push_cast at hxy hxz hyz
  have hN : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hX : (0:ℝ) ≤ x := Nat.cast_nonneg _
  have hY : (0:ℝ) ≤ y := Nat.cast_nonneg _
  have hZ : (0:ℝ) ≤ z := Nat.cast_nonneg _
  have hLxy := profile_log_upper (valueXY_pos φ (n*x) (n*y) hnx hny) hn hS
    (show valueXY φ (n*x) (n*y) ≤ (n:ℝ)*((x:ℝ)+y+z) by
      nlinarith [mul_nonneg hN hZ])
  have hLxz := profile_log_upper (valueXZ_pos φ (n*x) (n*z) hnx hnz) hn hS
    (show valueXZ φ (n*x) (n*z) ≤ (n:ℝ)*((x:ℝ)+y+z) by
      nlinarith [mul_nonneg hN hY])
  have hLyz := profile_log_upper (valueYZ_pos φ (n*y) (n*z) hny hnz) hn hS
    (show valueYZ φ (n*y) (n*z) ≤ (n:ℝ)*((x:ℝ)+y+z) by
      nlinarith [mul_nonneg hN hX])
  have h1 := mul_le_mul_of_nonneg_left hLxy (show 0 ≤ 2*(z:ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hLxz (show 0 ≤ 2*(y:ℝ) by positivity)
  have h3 := mul_le_mul_of_nonneg_left hLyz (show 0 ≤ 2*(x:ℝ) by positivity)
  unfold potential
  nlinarith only [h1,h2,h3]

theorem potential_step (φ : IntegralCharacter) (x y z n : ℕ)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) (hn : 1 ≤ n) :
    8*(φ.pX*(y:ℝ)*z+φ.pY*(x:ℝ)*z+φ.pZ*(x:ℝ)*y) /
        (((n:ℝ)+1)*((x:ℝ)+y+z)) ≤
      potential φ x y z (n+1)-potential φ x y z n := by
  let S : ℝ := (x:ℝ)+y+z
  have hnx : 1 ≤ n*x := one_le_mul hn hx
  have hny : 1 ≤ n*y := one_le_mul hn hy
  have hnz : 1 ≤ n*z := one_le_mul hn hz
  have hn1x : 1 ≤ (n+1)*x := one_le_mul (by omega) hx
  have hn1y : 1 ≤ (n+1)*y := one_le_mul (by omega) hy
  have hn1z : 1 ≤ (n+1)*z := one_le_mul (by omega) hz
  have hx0 := axis_log_growth φ (n*x) n y z S hnx hn hy hz (by
    dsimp [S]; push_cast; nlinarith [show (0:ℝ) ≤ x from Nat.cast_nonneg x])
  have hx1 := axis_log_growth φ ((n+1)*x) n y z S hn1x hn hy hz (by
    dsimp [S]; push_cast; nlinarith)
  have hy0 := axis_log_growth (swapXYCharacter φ) (n*y) n x z S hny hn hx hz (by
    dsimp [S]; push_cast; nlinarith [show (0:ℝ) ≤ y from Nat.cast_nonneg y])
  have hy1 := axis_log_growth (swapXYCharacter φ) ((n+1)*y) n x z S hn1y hn hx hz (by
    dsimp [S]; push_cast; nlinarith)
  have hz0 := axis_log_growth φ.cyclicCharacter (n*z) n x y S hnz hn hx hy (by
    dsimp [S]; push_cast; nlinarith [show (0:ℝ) ≤ z from Nat.cast_nonneg z])
  have hz1 := axis_log_growth φ.cyclicCharacter ((n+1)*z) n x y S hn1z hn hx hy (by
    dsimp [S]; push_cast; nlinarith)
  simp only [swapXY_pX, cyclic_pX] at hy0 hy1 hz0 hz1
  have ht := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hx0 hx1) hy0) hy1) hz0) hz1
  have hleft :
      4*φ.pX*(y:ℝ)*z/(((n:ℝ)+1)*S) + 4*φ.pX*(y:ℝ)*z/(((n:ℝ)+1)*S) +
      4*φ.pY*(x:ℝ)*z/(((n:ℝ)+1)*S) + 4*φ.pY*(x:ℝ)*z/(((n:ℝ)+1)*S) +
      4*φ.pZ*(x:ℝ)*y/(((n:ℝ)+1)*S) + 4*φ.pZ*(x:ℝ)*y/(((n:ℝ)+1)*S) =
        8*(φ.pX*(y:ℝ)*z+φ.pY*(x:ℝ)*z+φ.pZ*(x:ℝ)*y)/(((n:ℝ)+1)*S) := by ring
  rw [hleft] at ht
  have hright :
      axisIncrement φ (n*x) n y z + axisIncrement φ ((n+1)*x) n y z +
      axisIncrement (swapXYCharacter φ) (n*y) n x z +
      axisIncrement (swapXYCharacter φ) ((n+1)*y) n x z +
      axisIncrement φ.cyclicCharacter (n*z) n x y +
      axisIncrement φ.cyclicCharacter ((n+1)*z) n x y =
        potential φ x y z (n+1)-potential φ x y z n := by
    simp only [axisIncrement, potential, swapXY_valueXY, swapXY_valueXZ,
      cyclic_valueXY, cyclic_valueXZ]
    ring
  rw [hright] at ht
  exact ht

theorem weighted_quadratic_cap_nat (φ : IntegralCharacter) (x y z : ℕ)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    4*(φ.pX*(y:ℝ)*z+φ.pY*(x:ℝ)*z+φ.pZ*(x:ℝ)*y) ≤ ((x:ℝ)+y+z)^2 := by
  let S : ℝ := (x:ℝ)+y+z
  let B : ℝ := φ.pX*(y:ℝ)*z+φ.pY*(x:ℝ)*z+φ.pZ*(x:ℝ)*y
  let A : ℝ := 8*B/S
  have hS : 0 < S := by
    dsimp [S]
    have hxR : (1:ℝ) ≤ x := by exact_mod_cast hx
    have hyR : (0:ℝ) ≤ y := Nat.cast_nonneg _
    have hzR : (0:ℝ) ≤ z := Nat.cast_nonneg _
    linarith
  have hB : 0 ≤ B := by
    have hPX := φ.pX_nonneg
    have hPY := φ.pY_nonneg
    have hPZ := φ.pZ_nonneg
    dsimp [B]
    positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hstep (n : ℕ) (hn : 2 ≤ n) :
      A/(n:ℝ)-A/(n:ℝ)^2 ≤ potential φ x y z (n+1)-potential φ x y z n := by
    have hs := potential_step φ x y z n hx hy hz (by omega)
    have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hshift : A/(n:ℝ)-A/(n:ℝ)^2 ≤ A/((n:ℝ)+1) := by
      apply (le_div_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
      have he : (A/(n:ℝ)-A/(n:ℝ)^2)*((n:ℝ)+1) = A-A/(n:ℝ)^2 := by
        field_simp [hnR.ne']
        ring
      rw [he]
      exact sub_le_self _ (div_nonneg hA (sq_nonneg _))
    have he : A/((n:ℝ)+1) = 8*B/(((n:ℝ)+1)*S) := by
      dsimp [A]
      rw [div_div]
      congr 1
      ring
    rw [he] at hshift
    exact hshift.trans hs
  have hupper (n : ℕ) (hn : 2 ≤ n) :
      potential φ x y z n ≤ (2*S)*Real.log n + 2*S*Real.log S :=
    potential_upper φ x y z n hx hy hz (by omega)
  have h := Matmul.DiscretePotential.growth_coefficient_le
    (potential φ x y z) A A (2*S) (2*S*Real.log S) hstep hupper
  have hh := (div_le_iff₀ hS).mp h
  dsimp [B,S] at hh ⊢
  nlinarith only [hh]

def scaledCeil (x : ℝ) (n : ℕ) : ℝ :=
  ((Nat.ceil (x*(n:ℝ))+1:ℕ):ℝ)/(n:ℝ)

theorem scaledCeil_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (scaledCeil x) atTop (𝓝 x) := by
  unfold scaledCeil
  have hcast : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hceil := (tendsto_nat_ceil_mul_div_atTop hx).comp hcast
  have hinv : Tendsto (fun n : ℕ => (1:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hcast
  simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero,Function.comp_def]
    using hceil.add hinv

/-- Every actual integral tensor character satisfies the full weighted
quadratic constraint, including boundary weights equal to zero. -/
theorem actual_weighted_quadratic_cap (φ : IntegralCharacter) (x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    4*(φ.pX*y*z+φ.pY*x*z+φ.pZ*x*y) ≤ (x+y+z)^2 := by
  have hnat (n : ℕ) :
      4*(φ.pX*scaledCeil y n*scaledCeil z n+
        φ.pY*scaledCeil x n*scaledCeil z n+
        φ.pZ*scaledCeil x n*scaledCeil y n) ≤
          (scaledCeil x n+scaledCeil y n+scaledCeil z n)^2 := by
    have h := weighted_quadratic_cap_nat φ (Nat.ceil (x*(n:ℝ))+1)
      (Nat.ceil (y*(n:ℝ))+1) (Nat.ceil (z*(n:ℝ))+1) (by omega) (by omega) (by omega)
    have hd := div_le_div_of_nonneg_right h (sq_nonneg (n:ℝ))
    convert hd using 1 <;> (try rfl) <;> (try dsimp only [scaledCeil]) <;> push_cast <;> ring
  have hX := scaledCeil_tendsto x hx
  have hY := scaledCeil_tendsto y hy
  have hZ := scaledCeil_tendsto z hz
  have hleft : Tendsto (fun n =>
      4*(φ.pX*scaledCeil y n*scaledCeil z n+
        φ.pY*scaledCeil x n*scaledCeil z n+
        φ.pZ*scaledCeil x n*scaledCeil y n)) atTop
      (𝓝 (4*(φ.pX*y*z+φ.pY*x*z+φ.pZ*x*y))) :=
    tendsto_const_nhds.mul ((((tendsto_const_nhds.mul hY).mul hZ).add
      ((tendsto_const_nhds.mul hX).mul hZ)).add ((tendsto_const_nhds.mul hX).mul hY))
  have hright := ((hX.add hY).add hZ).pow 2
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hnat)

#print axioms actual_weighted_quadratic_cap

end
end HierarchicalAbsoluteSpectral.ScaleneCharacter
