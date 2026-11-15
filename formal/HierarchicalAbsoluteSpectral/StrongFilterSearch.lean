import HierarchicalAbsoluteSpectral.StrongFilterScalar
import HierarchicalAbsoluteSpectral.ArithmeticProgram

/-! The first sufficient Chebyshev degree, found using scalar arithmetic and
comparisons alone. No logarithm or transcendental oracle is executed. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Polynomial Polynomial.Chebyshev
open ArithmeticProgram hiding pure

def chebyshevNextProgram (x previous current : ℝ) : ArithmeticProgram ℝ := do
  let a ← mul 2 x
  let b ← mul a current
  sub b previous

@[simp] theorem chebyshevNextProgram_eval (x p c : ℝ) :
    (chebyshevNextProgram x p c).eval=2*x*c-p := by simp [chebyshevNextProgram]
@[simp] theorem chebyshevNextProgram_work (x p c : ℝ) :
    (chebyshevNextProgram x p c).work=3 := by simp [chebyshevNextProgram]
theorem chebyshevNextProgram_admissible (x p c : ℝ) :
    (chebyshevNextProgram x p c).admissible := by simp [chebyshevNextProgram]

theorem strongDenominator_recurrence (α : ℝ) (n : ℕ) :
    strongFilterDenominator α (n+1)=
      2*strongFilterCoordinate α (1+2*α)*strongFilterDenominator α n-
        (T ℝ ((n:ℤ)-1)).eval (strongFilterCoordinate α (1+2*α)) := by
  simp only [strongFilterDenominator, Nat.cast_add, Nat.cast_one, T_add_one,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

structure StrongSearchState (α D : ℝ) (hα : 0<α) (hα1 : α≤1) (hD : 1≤D) where
  degree : ℕ
  coordinate : ℝ
  previous : ℝ
  current : ℝ
  coordinate_eq : coordinate=strongFilterCoordinate α (1+2*α)
  previous_eq : previous=(T ℝ ((degree:ℤ)-1)).eval coordinate
  current_eq : current=strongFilterDenominator α degree
  bounded : degree≤strongFilterDegree α D hα hα1 hD

namespace StrongSearchState
variable {α D : ℝ} {hα : 0<α} {hα1 : α≤1} {hD : 1≤D}

theorem lt_of_not_stopped (s : StrongSearchState α D hα hα1 hD) (h : ¬D≤s.current) :
    s.degree<strongFilterDegree α D hα hα1 hD := by
  apply lt_of_le_of_ne s.bounded
  intro he
  apply h
  rw [s.current_eq, he]
  exact strongFilterDegree_stops α D hα hα1 hD

def next (s : StrongSearchState α D hα hα1 hD) (h : ¬D≤s.current)
    (v : {v : ℝ // v=(chebyshevNextProgram s.coordinate s.previous s.current).eval}) :
    StrongSearchState α D hα hα1 hD where
  degree := s.degree+1
  coordinate := s.coordinate
  previous := s.current
  current := v.val
  coordinate_eq := s.coordinate_eq
  previous_eq := by simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    s.coordinate_eq, strongFilterDenominator] using s.current_eq
  current_eq := by
    rw [v.property, chebyshevNextProgram_eval, s.previous_eq, s.current_eq, s.coordinate_eq]
    exact (strongDenominator_recurrence α s.degree).symm
  bounded := Nat.succ_le_of_lt (s.lt_of_not_stopped h)

end StrongSearchState

def strongSearchLoop {α D : ℝ} {hα : 0<α} {hα1 : α≤1} {hD : 1≤D}
    (s : StrongSearchState α D hα hα1 hD) : ArithmeticProgram ℕ :=
  .branch D s.current
    (fun _ => .pure s.degree)
    (fun h => do
      let v ← (chebyshevNextProgram s.coordinate s.previous s.current).certify
      strongSearchLoop (s.next h v))
termination_by strongFilterDegree α D hα hα1 hD-s.degree
decreasing_by
  have := s.lt_of_not_stopped h
  simp only [StrongSearchState.next]
  omega

theorem strongSearchLoop_specification {α D : ℝ} {hα : 0<α} {hα1 : α≤1} {hD : 1≤D}
    (s : StrongSearchState α D hα hα1 hD) :
    (strongSearchLoop s).eval=strongFilterDegree α D hα hα1 hD ∧
      (strongSearchLoop s).work=4*(strongFilterDegree α D hα hα1 hD-s.degree)+1 ∧
      (strongSearchLoop s).admissible := by
  rw [strongSearchLoop.eq_def]
  by_cases h : D≤s.current
  · have hm : strongFilterDegree α D hα hα1 hD≤s.degree := by
      apply Nat.find_min'
      rwa [s.current_eq] at h
    have he : s.degree=strongFilterDegree α D hα hα1 hD := le_antisymm s.bounded hm
    simp [ArithmeticProgram.eval, ArithmeticProgram.work, ArithmeticProgram.admissible, h,he]
  · have hi := strongSearchLoop_specification
      (s.next h (chebyshevNextProgram s.coordinate s.previous s.current).certify.eval)
    have hn := s.lt_of_not_stopped h
    simp only [ArithmeticProgram.eval, ArithmeticProgram.work, ArithmeticProgram.admissible,
      dif_neg h, eval_bind, work_bind, admissible_bind, certify_work,
      chebyshevNextProgram_work, certify_admissible, chebyshevNextProgram_admissible, true_and]
    refine ⟨hi.1,?_,hi.2.2⟩
    rw [hi.2.1]
    simp only [StrongSearchState.next]
    omega
termination_by strongFilterDegree α D hα hα1 hD-s.degree
decreasing_by
  have := s.lt_of_not_stopped h
  simp only [StrongSearchState.next]
  omega

def strongCoordinateProgram (α : ℝ) : ArithmeticProgram ℝ := do
  let a ← mul 2 α
  let b ← add 1 a
  let c ← mul 2 b
  let d ← add 1 α
  let e ← div c d
  sub e 1

@[simp] theorem strongCoordinateProgram_eval (α : ℝ) :
    (strongCoordinateProgram α).eval=strongFilterCoordinate α (1+2*α) := by
  simp [strongCoordinateProgram, strongFilterCoordinate]
@[simp] theorem strongCoordinateProgram_work (α : ℝ) :
    (strongCoordinateProgram α).work=6 := by simp [strongCoordinateProgram]
theorem strongCoordinateProgram_admissible (α : ℝ) (hα : 0<α) :
    (strongCoordinateProgram α).admissible := by
  simp [strongCoordinateProgram, (by positivity : (1:ℝ)+α≠0)]

def strongDegreeProgram (α D : ℝ) (hα : 0<α) (hα1 : α≤1) (hD : 1≤D) : ArithmeticProgram ℕ := do
  let x ← (strongCoordinateProgram α).certify
  strongSearchLoop (α := α) (D := D) (hα := hα) (hα1 := hα1) (hD := hD)
    { degree := 0
      coordinate := x.val
      previous := x.val
      current := 1
      coordinate_eq := by rw [x.property, strongCoordinateProgram_eval]
      previous_eq := by norm_num
      current_eq := by simp [strongFilterDenominator]
      bounded := Nat.zero_le _ }

theorem strongDegreeProgram_specification (α D : ℝ) (hα : 0<α) (hα1 : α≤1) (hD : 1≤D) :
    (strongDegreeProgram α D hα hα1 hD).eval=strongFilterDegree α D hα hα1 hD ∧
      (strongDegreeProgram α D hα hα1 hD).work=4*strongFilterDegree α D hα hα1 hD+7 ∧
      (strongDegreeProgram α D hα hα1 hD).admissible := by
  simp only [strongDegreeProgram, eval_bind, work_bind, admissible_bind,
    certify_work, strongCoordinateProgram_work, certify_admissible,
    strongCoordinateProgram_admissible α hα, true_and]
  have hi := strongSearchLoop_specification
    ({ degree := 0
       coordinate := (strongCoordinateProgram α).certify.eval.val
       previous := (strongCoordinateProgram α).certify.eval.val
       current := 1
       coordinate_eq := by simp
       previous_eq := by norm_num
       current_eq := by simp [strongFilterDenominator]
       bounded := Nat.zero_le _ } : StrongSearchState α D hα hα1 hD)
  refine ⟨hi.1,?_,hi.2.2⟩
  have hw := hi.2.1
  dsimp only at hw
  omega

end
end HierarchicalAbsoluteSpectral
