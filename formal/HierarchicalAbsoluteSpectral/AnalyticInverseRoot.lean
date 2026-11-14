import HierarchicalAbsoluteSpectral.DyadicNodes
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircle

/-!
The analytic extension used to bound the error of the finite polynomial in
Lemma 4. Complex functions and contour integrals occur only in its proof;
the polynomial itself remains the sampled, finite `inverseRootInterpolant`.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section

def complexInverseRoot (η : ℝ) (z : ℂ) : ℂ :=
  (Complex.sqrt (Complex.sqrt (z^2 + (η : ℂ)^2) + (η : ℂ)))⁻¹

def joukowski (w : ℂ) : ℂ := (w + w⁻¹) / 2

theorem complex_sqrt_sq (z : ℂ) : (Complex.sqrt z)^2 = z := by
  exact Complex.cpow_nat_inv_pow z (by decide : (2 : ℕ) ≠ 0)

theorem complex_sqrt_re_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem complex_sqrt_norm_sq (z : ℂ) : ‖Complex.sqrt z‖^2 = ‖z‖ := by
  rw [← norm_pow, complex_sqrt_sq]

theorem complex_sqrt_ofReal_nonneg (x : ℝ) (hx : 0 ≤ x) :
    Complex.sqrt (x : ℂ) = (Real.sqrt x : ℂ) := by
  exact Complex.sqrt_of_nonneg (by exact_mod_cast hx)

theorem complexInverseRoot_ofReal (η x : ℝ) (hη : 0 < η) :
    complexInverseRoot η (x : ℂ) = (inverseRootValue η x : ℂ) := by
  have h0 : 0 ≤ x^2+η^2 := by positivity
  have h1 : 0 ≤ Real.sqrt (x^2+η^2)+η := by positivity
  simp only [complexInverseRoot, inverseRootValue, ← Complex.ofReal_pow,
    ← Complex.ofReal_add, complex_sqrt_ofReal_nonneg _ h0,
    complex_sqrt_ofReal_nonneg _ h1, Complex.ofReal_inv]

theorem inverseRoot_inner_re_pos (η : ℝ) (z : ℂ) (hη : 0 < η)
    (hz : |z.im| ≤ η/4) : 0 < (z^2 + (η : ℂ)^2).re := by
  have hz2 : z.im^2 ≤ (η/4)^2 := by
    have := (sq_le_sq₀ (abs_nonneg z.im) (by positivity)).mpr hz
    simpa only [sq_abs] using this
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [sq_nonneg z.re, sq_pos_of_pos hη]

theorem inverseRoot_outer_re_pos (η : ℝ) (z : ℂ) (hη : 0 < η) :
    0 < (Complex.sqrt (z^2+(η : ℂ)^2)+(η : ℂ)).re := by
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith [complex_sqrt_re_nonneg (z^2+(η : ℂ)^2)]

theorem complexInverseRoot_differentiableAt (η : ℝ) (z : ℂ) (hη : 0 < η)
    (hz : |z.im| ≤ η/4) : DifferentiableAt ℂ (complexInverseRoot η) z := by
  have hi := inverseRoot_inner_re_pos η z hη hz
  have ho := inverseRoot_outer_re_pos η z hη
  have harg : DifferentiableAt ℂ (fun z : ℂ => z^2+(η : ℂ)^2) z := by fun_prop
  have hs := (Complex.differentiableAt_sqrt (Or.inl hi)).comp z harg
  have ht := (Complex.differentiableAt_sqrt (Or.inl ho)).comp z (hs.add_const (η : ℂ))
  apply ht.inv
  intro heq
  change Complex.sqrt (Complex.sqrt (z^2+(η : ℂ)^2)+(η : ℂ)) = 0 at heq
  have heq' := congrArg (fun w : ℂ => w^2) heq
  rw [complex_sqrt_sq] at heq'
  have hr := congrArg Complex.re heq'
  simp only [zero_pow (by decide : 2 ≠ 0), Complex.zero_re] at hr
  linarith

theorem complexInverseRoot_norm_le (η : ℝ) (z : ℂ) (hη : 0 < η) :
    ‖complexInverseRoot η z‖ ≤ (Real.sqrt η)⁻¹ := by
  have hηs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hlo : η ≤ ‖Complex.sqrt (z^2+(η : ℂ)^2)+(η : ℂ)‖ := by
    have hr := Complex.re_le_norm (Complex.sqrt (z^2+(η : ℂ)^2)+(η : ℂ))
    simp only [Complex.add_re, Complex.ofReal_re] at hr
    linarith [complex_sqrt_re_nonneg (z^2+(η : ℂ)^2)]
  have hs : Real.sqrt η ≤ ‖Complex.sqrt (Complex.sqrt (z^2+(η : ℂ)^2)+(η : ℂ))‖ := by
    have heq := complex_sqrt_norm_sq (Complex.sqrt (z^2+(η : ℂ)^2)+(η : ℂ))
    nlinarith [norm_nonneg (Complex.sqrt (Complex.sqrt (z^2+(η : ℂ)^2)+(η : ℂ))),
      Real.sq_sqrt hη.le]
  simpa only [complexInverseRoot, norm_inv] using inv_anti₀ hηs hs

theorem joukowski_differentiableAt (w : ℂ) (hw : w ≠ 0) :
    DifferentiableAt ℂ joukowski w := by
  unfold joukowski
  fun_prop

theorem joukowski_inv (w : ℂ) : joukowski w⁻¹ = joukowski w := by
  simp [joukowski, add_comm]

theorem joukowski_im_bound (w : ℂ) (hw : 1 ≤ ‖w‖) :
    |(joukowski w).im| ≤ ‖w‖-1 := by
  have hn : 0 < ‖w‖ := by linarith
  have hn2 : 0 < ‖w‖^2 := sq_pos_of_pos hn
  have hsq : 1 ≤ ‖w‖^2 := by nlinarith
  have hfac : 0 ≤ 1-(‖w‖^2)⁻¹ := by
    have := (inv_le_one₀ hn2).mpr hsq
    linarith
  have heq : (joukowski w).im = w.im*(1-(‖w‖^2)⁻¹)/2 := by
    simp only [joukowski, Complex.div_ofNat_im, Complex.add_im, Complex.inv_im,
      Complex.normSq_eq_norm_sq]
    ring
  rw [heq, abs_div, abs_mul, abs_of_nonneg hfac]
  norm_num
  have hm := mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm w) hfac
  have hid : ‖w‖*(1-(‖w‖^2)⁻¹) = ‖w‖-‖w‖⁻¹ := by field_simp
  rw [hid] at hm
  have hninv : 2-‖w‖ ≤ ‖w‖⁻¹ := by
    apply (le_of_mul_le_mul_left (a := ‖w‖) ?_ hn)
    rw [mul_inv_cancel₀ hn.ne']
    nlinarith [sq_nonneg (‖w‖-1)]
  linarith

theorem inverseRoot_joukowski_differentiableAt (η : ℝ) (w : ℂ) (hη : 0 < η)
    (hw : 1 ≤ ‖w‖) (hw' : ‖w‖ ≤ 1+η/4) :
    DifferentiableAt ℂ (fun w => complexInverseRoot η (joukowski w)) w := by
  have hstrip : |(joukowski w).im| ≤ η/4 := by
    have := joukowski_im_bound w hw
    linarith
  have hne : w ≠ 0 := by intro heq; norm_num [heq] at hw
  exact (complexInverseRoot_differentiableAt η _ hη hstrip).comp w
    (joukowski_differentiableAt w hne)

end
end HierarchicalAbsoluteSpectral
