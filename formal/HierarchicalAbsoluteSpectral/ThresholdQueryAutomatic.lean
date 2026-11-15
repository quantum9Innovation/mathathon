import HierarchicalAbsoluteSpectral.ThresholdQueryCost
import HierarchicalAbsoluteSpectral.ThresholdKrylovDegree

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {k r : ℕ}

/-- The degree is found by executed Chebyshev recurrence tests; it is then
used by the actual powers/range/inertia query compiler. -/
def automaticKrylovQueryProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (S : Core k) (source : MatrixAction Sᵀ r) (j : Fin k) (U ε : ℝ)
    (hk : 1 ≤ k) (hU : 1 ≤ U) (hε : 0 < ε) (hε' : ε ≤ 1)
    (N : ℕ) (G : Fin N → Fin r → Fin k → ℝ) (g : Fin N → Fin 2 → Fin (k*k) → ℝ) :
    ArithmeticProgram ThresholdDecision := do
  let q ← krylovDegreeProgram k U (1/2) ε hk hU (by norm_num) (by norm_num) hε hε'
  repeatedKrylovQueryProgram kernels T hT actions q S source j ε N G g

theorem automaticKrylovQueryProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (S : Core k) (source : MatrixAction Sᵀ r) (j : Fin k) (U ε : ℝ)
    (hk : 1 ≤ k) (hU : 1 ≤ U) (hε : 0 < ε) (hε' : ε ≤ 1)
    (N : ℕ) (G : Fin N → Fin r → Fin k → ℝ) (g : Fin N → Fin 2 → Fin (k*k) → ℝ) :
    (automaticKrylovQueryProgram kernels T hT actions S source j U ε hk hU hε hε' N G g).eval =
      (repeatedKrylovQueryProgram kernels T hT actions
        (krylovDegree k U (1/2) ε hk hU (by norm_num) (by norm_num) hε hε') S source j ε N G g).eval := by
  simp only [automaticKrylovQueryProgram,eval_bind,
    (krylovDegreeProgram_specification k U (1/2) ε hk hU (by norm_num) (by norm_num) hε hε').1]

theorem automaticKrylovQueryProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (S : Core k) (source : MatrixAction Sᵀ r) (j : Fin k) (U ε : ℝ)
    (hk : 1 ≤ k) (hU : 1 ≤ U) (hε : 0 < ε) (hε' : ε ≤ 1)
    (N : ℕ) (G : Fin N → Fin r → Fin k → ℝ) (g : Fin N → Fin 2 → Fin (k*k) → ℝ) :
    (automaticKrylovQueryProgram kernels T hT actions S source j U ε hk hU hε hε' N G g).admissible := by
  simp only [automaticKrylovQueryProgram,admissible_bind,repeatedKrylovQueryProgram_admissible,and_true]
  exact (krylovDegreeProgram_specification k U (1/2) ε hk hU (by norm_num) (by norm_num) hε hε').2.2

theorem automaticKrylovQueryProgram_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (S : Core k) (source : MatrixAction Sᵀ r) (j : Fin k) (U ε : ℝ)
    (hk : 1 ≤ k) (hU : 1 ≤ U) (hε : 0 < ε) (hε' : ε ≤ 1)
    (N : ℕ) (G : Fin N → Fin r → Fin k → ℝ) (g : Fin N → Fin 2 → Fin (k*k) → ℝ) :
    let q := krylovDegree k U (1/2) ε hk hU (by norm_num) (by norm_num) hε hε'
    (automaticKrylovQueryProgram kernels T hT actions S source j U ε hk hU hε hε' N G g).work =
      4*q+15+(repeatedKrylovQueryProgram kernels T hT actions q S source j ε N G g).work := by
  simp only [automaticKrylovQueryProgram,work_bind,
    (krylovDegreeProgram_specification k U (1/2) ε hk hU (by norm_num) (by norm_num) hε hε').1,
    (krylovDegreeProgram_specification k U (1/2) ε hk hU (by norm_num) (by norm_num) hε hε').2.1]

end
end HierarchicalAbsoluteSpectral
