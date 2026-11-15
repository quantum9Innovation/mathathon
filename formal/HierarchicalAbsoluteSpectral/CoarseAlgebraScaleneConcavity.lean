import Matmul.DiscreteSlopes
import Matmul.DiscretePotential

/-! Weighted logarithmic growth of coupled concave convolution rows. -/

namespace HierarchicalAbsoluteSpectral.ScaleneConcavity

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

/-- The tangent inequality for the logarithm, at the upper endpoint. -/
theorem log_increment_lower {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y-x)/y ≤ Real.log y-Real.log x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at h
  have he : (y-x)/y = 1-x/y := by field_simp [hy.ne']
  rw [he]
  linarith

/-- A common increment and a cap on the two endpoints yield the weighted
logarithmic growth, without an asymptotic or smoothness assumption. -/
theorem weighted_log_growth {x y A B L D r s : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hA : 0 < A) (hB : 0 < B)
    (hL : 0 < L) (hD : 0 < D) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hincA : r*L ≤ A-x) (hincB : s*L ≤ B-y)
    (hcap : A+B ≤ L*D) :
    4*r*s/D ≤ s*(Real.log A-Real.log x)+r*(Real.log B-Real.log y) := by
  have hlogA := log_increment_lower hx hA
  have hlogB := log_increment_lower hy hB
  have hincA' : r*L/A ≤ (A-x)/A := div_le_div_of_nonneg_right hincA hA.le
  have hincB' : s*L/B ≤ (B-y)/B := div_le_div_of_nonneg_right hincB hB.le
  have hlog := add_le_add
    (mul_le_mul_of_nonneg_left (hincA'.trans hlogA) hs)
    (mul_le_mul_of_nonneg_left (hincB'.trans hlogB) hr)
  have hrecip : 4/D ≤ L/A+L/B := by
    apply (div_le_iff₀ hD).mpr
    have hmul : 4*A*B ≤ (A+B)*(L*D) := by
      have hh := mul_le_mul_of_nonneg_left hcap (show 0 ≤ A+B by positivity)
      nlinarith [sq_nonneg (A-B)]
    apply le_of_mul_le_mul_right (a := A*B) ?_ (mul_pos hA hB)
    have heq : ((L/A+L/B)*D)*(A*B) = (A+B)*(L*D) := by
      field_simp [hA.ne',hB.ne'] <;> ring
    rw [heq]
    nlinarith
  calc
    4*r*s/D = (r*s)*(4/D) := by ring
    _ ≤ (r*s)*(L/A+L/B) := mul_le_mul_of_nonneg_left hrecip (mul_nonneg hr hs)
    _ = s*(r*L/A)+r*(s*L/B) := by ring
    _ ≤ _ := hlog

/-- The weighted endpoint estimate for coupled positive concave sequences.
The tripling identities are the exact finite hypotheses supplied by the
integral convolution constructions. -/
theorem coupled_log_increment {g h : ℕ → ℝ} {a u v r s : ℕ}
    (ha : 1 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hg : ∀ k : ℕ, 1 ≤ k → 0 < g k)
    (hh : ∀ k : ℕ, 1 ≤ k → 0 < h k)
    (hgd : Antitone (fun k : ℕ => g (k+2)-g (k+1)))
    (hhd : Antitone (fun k : ℕ => h (k+2)-h (k+1)))
    (hgt : ∀ k : ℕ, 1 ≤ k → 2*g k+h k ≤ g (3*k+a-1))
    (hht : ∀ k : ℕ, 1 ≤ k → 2*h k+g k ≤ h (3*k+a-1)) :
    4*(r:ℝ)*s/((u:ℝ)+v+r+s+a-1) ≤
      (s:ℝ)*(Real.log (g (u+r))-Real.log (g u))+
        (r:ℝ)*(Real.log (h (v+s))-Real.log (h v)) := by
  have hgt' : ∀ k : ℕ, 1 ≤ k → 2*g k+h k ≤ g (3*k+(a-1)) := by
    intro k hk
    have he : 3*k+(a-1) = 3*k+a-1 := by omega
    rw [he]
    exact hgt k hk
  have hht' : ∀ k : ℕ, 1 ≤ k → 2*h k+g k ≤ h (3*k+(a-1)) := by
    intro k hk
    have he : 3*k+(a-1) = 3*k+a-1 := by omega
    rw [he]
    exact hht k hk
  obtain ⟨L,hL,_,_,hcap,hgi,hhi,_,_⟩ :=
    Matmul.DiscreteSlopes.exists_common_row_slope hg hh hgd hhd hgt' hht'
  have hgr := Matmul.DiscreteSlopes.long_increment_of_lower hgi u r hu
  have hhs := Matmul.DiscreteSlopes.long_increment_of_lower hhi v s hv
  let m := max (u+r) (v+s)
  have hum : u+r ≤ m := le_max_left _ _
  have hvm : v+s ≤ m := le_max_right _ _
  have hgm := Matmul.DiscreteSlopes.long_increment_of_lower hgi (u+r) (m-(u+r)) (by omega)
  have hhm := Matmul.DiscreteSlopes.long_increment_of_lower hhi (v+s) (m-(v+s)) (by omega)
  rw [Nat.add_sub_of_le hum, Nat.cast_sub hum, Nat.cast_add] at hgm
  rw [Nat.add_sub_of_le hvm, Nat.cast_sub hvm, Nat.cast_add] at hhm
  have hcapm := hcap m (by omega)
  rw [Nat.cast_sub ha,Nat.cast_one] at hcapm
  have hcap' : g (u+r)+h (v+s) ≤ L*((u:ℝ)+v+r+s+a-1) := by
    nlinarith
  have huR : (1:ℝ) ≤ u := by exact_mod_cast hu
  have hvR : (1:ℝ) ≤ v := by exact_mod_cast hv
  have haR : (1:ℝ) ≤ a := by exact_mod_cast ha
  apply weighted_log_growth (hg u hu) (hh v hv) (hg (u+r) (by omega))
    (hh (v+s) (by omega)) hL (by
      have hrR : (0:ℝ) ≤ r := Nat.cast_nonneg r
      have hsR : (0:ℝ) ≤ s := Nat.cast_nonneg s
      linarith) (Nat.cast_nonneg r)
    (Nat.cast_nonneg s) hgr hhs hcap'

/-- A larger convenient denominator may be substituted in the growth bound. -/
theorem coupled_log_increment_of_denominator {g h : ℕ → ℝ} {a u v r s : ℕ}
    (ha : 1 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hg : ∀ k : ℕ, 1 ≤ k → 0 < g k)
    (hh : ∀ k : ℕ, 1 ≤ k → 0 < h k)
    (hgd : Antitone (fun k : ℕ => g (k+2)-g (k+1)))
    (hhd : Antitone (fun k : ℕ => h (k+2)-h (k+1)))
    (hgt : ∀ k : ℕ, 1 ≤ k → 2*g k+h k ≤ g (3*k+a-1))
    (hht : ∀ k : ℕ, 1 ≤ k → 2*h k+g k ≤ h (3*k+a-1))
    {D : ℝ} (hD : (u:ℝ)+v+r+s+a-1 ≤ D) :
    4*(r:ℝ)*s/D ≤
      (s:ℝ)*(Real.log (g (u+r))-Real.log (g u))+
        (r:ℝ)*(Real.log (h (v+s))-Real.log (h v)) := by
  have huR : (1:ℝ) ≤ u := by exact_mod_cast hu
  have hvR : (1:ℝ) ≤ v := by exact_mod_cast hv
  have haR : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hd : 0 < (u:ℝ)+v+r+s+a-1 := by
    have hrR : (0:ℝ) ≤ r := Nat.cast_nonneg r
    have hsR : (0:ℝ) ≤ s := Nat.cast_nonneg s
    linarith
  exact (div_le_div_of_nonneg_left (by positivity) hd hD).trans
    (coupled_log_increment ha hu hv hg hh hgd hhd hgt hht)

end
end HierarchicalAbsoluteSpectral.ScaleneConcavity
