import HierarchicalAbsoluteSpectral.StoredProxyAction

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
variable {k m b s t : ℕ}

/-- Apply a stored sketch Gram through its original small support factor;
the potentially large normalized sketch is never formed. -/
def storedCongruenceGramAction
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (F : Matrix (Fin s) (Fin m) ℝ) (L : Matrix (Fin m) (Fin k) ℝ) :
    MatrixAction (Lᵀ*(Fᵀ*F)*L) b :=
  (((kernels k m b).action Lᵀ).comp
    ((storedGramAction F (kernels s m b) (kernels m s b)).comp ((kernels m k b).action L))).castMatrix
      (by simp only [Matrix.mul_assoc])

@[simp] theorem storedCongruenceGramAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (F : Matrix (Fin s) (Fin m) ℝ) (L : Matrix (Fin m) (Fin k) ℝ) :
    (storedCongruenceGramAction (b:=b) kernels F L).cost =
      (kernels k m b).cost+(kernels m s b).cost+(kernels s m b).cost+(kernels m k b).cost := by
  dsimp [storedCongruenceGramAction,storedGramAction,MatrixAction.castMatrix,MatrixAction.comp]
  ring

def storedFinePencilAction
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (HA : Matrix (Fin s) (Fin m) ℝ) (HB : Matrix (Fin t) (Fin m) ℝ)
    (L : Matrix (Fin m) (Fin k) ℝ) (U : Matrix (Fin m) (Fin k) ℝ)
    (t0 ε : ℝ) (hε : 0 < ε) :
    MatrixAction (trueNeumannPencil (Uᵀ*(HAᵀ*HA)*U) (Lᵀ*(HBᵀ*HB)*L) t0 ε hε) b :=
  storedNeumannPencilAction (storedCongruenceGramAction kernels HA U)
    (storedCongruenceGramAction kernels HB L) t0 ε hε

@[simp] theorem storedFinePencilAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (HA : Matrix (Fin s) (Fin m) ℝ) (HB : Matrix (Fin t) (Fin m) ℝ)
    (L : Matrix (Fin m) (Fin k) ℝ) (U : Matrix (Fin m) (Fin k) ℝ)
    (t0 ε : ℝ) (hε : 0 < ε) :
    (storedFinePencilAction (b:=b) kernels HA HB L U t0 ε hε).cost =
      2*dyadicStoppingLevel (1/2) ε (by norm_num) (by norm_num) hε+1+
      2*neumannCount ε hε*((kernels k m b).cost+(kernels m s b).cost+
        (kernels s m b).cost+(kernels m k b).cost+2*k*b)+
      ((kernels k m b).cost+(kernels m t b).cost+(kernels t m b).cost+(kernels m k b).cost)+2*k*b := by
  dsimp only [storedFinePencilAction,storedNeumannPencilAction,MatrixAction.sub,
    MatrixAction.scale,MatrixAction.constructedNeumann]
  rw [storedCongruenceGramAction_cost,storedCongruenceGramAction_cost]
  ring

end
end HierarchicalAbsoluteSpectral
