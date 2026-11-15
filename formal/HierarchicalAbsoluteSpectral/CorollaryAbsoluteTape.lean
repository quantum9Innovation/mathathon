import HierarchicalAbsoluteSpectral.CorollaryAbsoluteProgram

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory
variable {n m p L k s N : ℕ}

/-- Fresh query, inertia and carried-filter arrays for one attempted rank. -/
abbrev AbsoluteProbabilityTape (k s N : ℕ) :=
  (Fin N → Fin (s+1) → Fin k → ℝ) ×
    ((Fin N → Fin 2 → Fin (k*k) → ℝ) × (Fin s → Fin k → ℝ))

def absoluteProbabilityLaw (k s N : ℕ) : Measure (AbsoluteProbabilityTape k s N) :=
  (repeatedGaussianColumns k (s+1) N).prod
    ((Measure.pi (fun _ : Fin N => Measure.pi (fun _ : Fin 2 => gaussianVector (k*k)))).prod
      (gaussianColumns k s))

instance absoluteProbabilityLaw_isProbability (k s N : ℕ) :
    IsProbabilityMeasure (absoluteProbabilityLaw k s N) := by
  unfold absoluteProbabilityLaw
  infer_instance

def absoluteProbabilityTapeRestriction (hk : k ≤ m)
    (z : AbsoluteProbabilityTape m s N) : AbsoluteProbabilityTape k s N :=
  ⟨(fun u j i => z.1 u j (Fin.castLE hk i)),
    (fun u t i => z.2.1 u t (Fin.castLE (Nat.mul_le_mul hk hk) i)),
    (fun j i => z.2.2 j (Fin.castLE hk i))⟩

theorem absolute_gaussianVector_rows_measurePreserving (hk : k ≤ m) :
    MeasurePreserving (fun z : Fin m → ℝ => fun i : Fin k => z (Fin.castLE hk i))
      (gaussianVector m) (gaussianVector k) :=
  gaussianTape_injection_measurePreserving (Fin.castLEEmb hk)

theorem absolute_gaussianColumns_rows_measurePreserving (hk : k ≤ m) (s : ℕ) :
    MeasurePreserving (fun z : Fin s → Fin m → ℝ => fun j i => z j (Fin.castLE hk i))
      (gaussianColumns m s) (gaussianColumns k s) :=
  measurePreserving_pi (fun _ : Fin s => gaussianVector m) (fun _ : Fin s => gaussianVector k)
    (fun _ => absolute_gaussianVector_rows_measurePreserving hk)

theorem absoluteProbabilityTapeRestriction_measurePreserving (hk : k ≤ m) :
    MeasurePreserving (absoluteProbabilityTapeRestriction (s:=s) (N:=N) hk)
      (absoluteProbabilityLaw m s N) (absoluteProbabilityLaw k s N) := by
  have hq := measurePreserving_pi (fun _ : Fin N => gaussianColumns m (s+1))
    (fun _ : Fin N => gaussianColumns k (s+1))
    (fun _ => absolute_gaussianColumns_rows_measurePreserving hk (s+1))
  have hd := measurePreserving_pi (fun _ : Fin N => gaussianColumns (m*m) 2)
    (fun _ : Fin N => gaussianColumns (k*k) 2)
    (fun _ => absolute_gaussianColumns_rows_measurePreserving (Nat.mul_le_mul hk hk) 2)
  exact hq.prod (hd.prod (absolute_gaussianColumns_rows_measurePreserving hk s))

/-- The data are allocated by rank, so every rank uses independent fresh
arrays while the control flow decides which ones are actually evaluated. -/
abbrev AbsoluteCoreTape (I : AbsoluteProblem n m p L) :=
  ∀ s : Fin (m+1), AbsoluteProbabilityTape m s.val I.seed.repetitions

def absoluteCoreLaw (I : AbsoluteProblem n m p L) : Measure (AbsoluteCoreTape I) :=
  Measure.pi (fun s => absoluteProbabilityLaw m s.val I.seed.repetitions)

instance absoluteCoreLaw_isProbability (I : AbsoluteProblem n m p L) :
    IsProbabilityMeasure (absoluteCoreLaw I) := by unfold absoluteCoreLaw; infer_instance

abbrev AbsoluteTape (I : AbsoluteProblem n m p L) := MainRandomTape I.seed × AbsoluteCoreTape I

def absoluteRandomLaw (I : AbsoluteProblem n m p L) : Measure (AbsoluteTape I) :=
  (mainRandomLaw I.seed).prod (absoluteCoreLaw I)

instance absoluteRandomLaw_isProbability (I : AbsoluteProblem n m p L) :
    IsProbabilityMeasure (absoluteRandomLaw I) := by unfold absoluteRandomLaw; infer_instance

end
end HierarchicalAbsoluteSpectral
