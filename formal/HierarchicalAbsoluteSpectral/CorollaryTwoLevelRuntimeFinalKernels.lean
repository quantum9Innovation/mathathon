import HierarchicalAbsoluteSpectral.CoarseAlgebraScalene
import HierarchicalAbsoluteSpectral.CoarseAlgebraKernelSelection
import HierarchicalAbsoluteSpectral.CoarseAlgebraSingularInertiaCost

/-!
One arithmetic kernel family for the two-level running-time bounds. At core
size `m`, only finitely many certified coefficient circuits are compared:
the requested shapes and precision indices `j ≤ m`. All choices precede
the exponent slack in the eventual estimates.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Matmul.RectangularPrograms

structure PositiveScaleneShape where
  u : ℝ
  v : ℝ
  w : ℝ
  u_pos : 0 < u
  v_pos : 0 < v
  w_pos : 0 < w

namespace PositiveScaleneShape

def cyclic (s : PositiveScaleneShape) : PositiveScaleneShape :=
  ⟨s.v,s.w,s.u,s.v_pos,s.w_pos,s.u_pos⟩

def swap (s : PositiveScaleneShape) : PositiveScaleneShape :=
  ⟨s.u,s.w,s.v,s.u_pos,s.w_pos,s.v_pos⟩

def permutations (s : PositiveScaleneShape) : List PositiveScaleneShape :=
  [s,s.swap,s.cyclic,s.cyclic.swap,s.cyclic.cyclic,s.cyclic.cyclic.swap]

def Fits (s : PositiveScaleneShape) (δ : ℝ) (m a b c : ℕ) : Prop :=
  a ≤ width (s.u+δ) m ∧ b ≤ width (s.v+δ) m ∧ c ≤ width (s.w+δ) m

theorem fits_mono (s : PositiveScaleneShape) {δ ε : ℝ} (hδε : δ ≤ ε)
    {m a b c : ℕ} (hm : 1 ≤ m) (hfit : s.Fits δ m a b c) : s.Fits ε m a b c := by
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hwidth (x : ℝ) : width (x+δ) m ≤ width (x+ε) m :=
    Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hmR (by linarith))
  exact ⟨hfit.1.trans (hwidth s.u),hfit.2.1.trans (hwidth s.v),hfit.2.2.trans (hwidth s.w)⟩

end PositiveScaleneShape

structure InflatedScaleneKernelFamily (s : PositiveScaleneShape) (ε : ℝ) where
  δ : ℝ
  δ_pos : 0 < δ
  kernel : ∀ m : ℕ,
    ArithmeticKernel (width (s.u+δ) m) (width (s.v+δ) m) (width (s.w+δ) m)
  constant : ℝ
  constant_pos : 0 < constant
  cost_bound : ∀ m : ℕ, 1 ≤ m →
    ((kernel m).cost:ℝ) ≤ constant*(m:ℝ)^(scaleneBound s.u s.v s.w+ε)

def chosenInflatedScaleneFamily (s : PositiveScaleneShape) (j : ℕ) :
    InflatedScaleneKernelFamily s (1/(j+1:ℝ)) := Classical.choice (by
  obtain ⟨δ,hδ,K,C,hC,hK⟩ := exists_inflated_scalene_arithmetic_kernels
    s.u s.v s.w (1/(j+1:ℝ)) s.u_pos s.v_pos s.w_pos (by positivity)
  exact ⟨⟨δ,hδ,K,C,hC,hK⟩⟩)

def InflatedScaleneKernelFamily.cap {s : PositiveScaleneShape} {ε : ℝ}
    (P : InflatedScaleneKernelFamily s ε) (m : ℕ) : MatrixKernelCap :=
  ⟨width (s.u+P.δ) m,width (s.v+P.δ) m,width (s.w+P.δ) m,P.kernel m⟩

def finiteScaleneCaps (shapes : List PositiveScaleneShape) (m : ℕ) : List MatrixKernelCap :=
  (List.range (m+1)).flatMap (fun j => shapes.map (fun s => (chosenInflatedScaleneFamily s j).cap m))

def finiteScaleneKernelFamily (shapes : List PositiveScaleneShape)
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (m : ℕ) :
    ∀ a b c : ℕ, ArithmeticKernel a b c :=
  combineKernelCaps fallback (finiteScaleneCaps shapes m)

theorem finiteScaleneKernelFamily_cost_le_fallback (shapes : List PositiveScaleneShape)
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (m a b c : ℕ) :
    (finiteScaleneKernelFamily shapes fallback m a b c).cost ≤ (fallback a b c).cost :=
  combineKernelCaps_cost_le_fallback fallback (finiteScaleneCaps shapes m) a b c

theorem finiteScaleneKernelFamily_cost_le_chosen (shapes : List PositiveScaleneShape)
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (s : PositiveScaleneShape)
    (hs : s ∈ shapes) (m j a b c : ℕ) (hjm : j ≤ m)
    (hfit : s.Fits (chosenInflatedScaleneFamily s j).δ m a b c) :
    (finiteScaleneKernelFamily shapes fallback m a b c).cost ≤
      ((chosenInflatedScaleneFamily s j).kernel m).cost := by
  apply combineKernelCaps_cost_le_cap fallback (finiteScaleneCaps shapes m)
    ((chosenInflatedScaleneFamily s j).cap m) _ a b c hfit
  apply List.mem_flatMap.mpr
  refine ⟨j,List.mem_range.mpr (by omega),?_⟩
  exact List.mem_map.mpr ⟨s,hs,rfl⟩

/-- A fixed positive padding allowance survives the diagonal selection, and
the coefficient constant is absorbed into every positive exponent slack. -/
theorem finiteScaleneKernelFamily_eventually (shapes : List PositiveScaleneShape)
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (s : PositiveScaleneShape)
    (hs : s ∈ shapes) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop, ∀ a b c : ℕ,
      s.Fits δ m a b c →
      ((finiteScaleneKernelFamily shapes fallback m a b c).cost:ℝ) ≤
        (m:ℝ)^(scaleneBound s.u s.v s.w+ζ) := by
  obtain ⟨j,hj⟩ := exists_nat_one_div_lt (show (0:ℝ) < ζ/2 by positivity)
  let P := chosenInflatedScaleneFamily s j
  have ht : Tendsto (fun m : ℕ => (m:ℝ)^(ζ/2)) atTop atTop :=
    (tendsto_rpow_atTop (show 0 < ζ/2 by positivity)).comp tendsto_natCast_atTop_atTop
  refine ⟨P.δ,P.δ_pos,?_⟩
  filter_upwards [eventually_ge_atTop (max j 1),ht.eventually (eventually_ge_atTop P.constant)]
    with m hm hconstant
  intro a b c hfit
  have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
  have hjm : j ≤ m := (le_max_left _ _).trans hm
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm1
  have hcost : ((finiteScaleneKernelFamily shapes fallback m a b c).cost:ℝ) ≤
      (P.kernel m).cost := by
    exact_mod_cast finiteScaleneKernelFamily_cost_le_chosen shapes fallback s hs m j a b c hjm hfit
  calc
    _ ≤ P.constant*(m:ℝ)^(scaleneBound s.u s.v s.w+1/(j+1:ℝ)) :=
      hcost.trans (P.cost_bound m hm1)
    _ ≤ (m:ℝ)^(ζ/2)*(m:ℝ)^(scaleneBound s.u s.v s.w+1/(j+1:ℝ)) :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (m:ℝ)^(ζ/2+(scaleneBound s.u s.v s.w+1/(j+1:ℝ))) := (Real.rpow_add hm0 _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hmR (by linarith)

theorem finiteScaleneKernelFamily_uniform_eventually (shapes : List PositiveScaleneShape)
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ shapes, ∀ a b c : ℕ,
      s.Fits δ m a b c →
      ((finiteScaleneKernelFamily shapes fallback m a b c).cost:ℝ) ≤
        (m:ℝ)^(scaleneBound s.u s.v s.w+ζ) := by
  have hpoint := fun s hs => finiteScaleneKernelFamily_eventually shapes fallback s hs ζ hζ
  have hfinite : ∀ (L : List PositiveScaleneShape), (∀ s ∈ L, s ∈ shapes) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ L, ∀ a b c : ℕ,
        s.Fits δ m a b c →
        ((finiteScaleneKernelFamily shapes fallback m a b c).cost:ℝ) ≤
          (m:ℝ)^(scaleneBound s.u s.v s.w+ζ) := by
    intro L
    induction L with
    | nil =>
      intro _
      refine ⟨1,by norm_num,Eventually.of_forall ?_⟩
      intro m s hs
      simp at hs
    | cons s L ih =>
      intro hL
      obtain ⟨δ,hδ,hhead⟩ := hpoint s (hL s (List.mem_cons_self))
      obtain ⟨ε,hε,htail⟩ := ih (fun t ht => hL t (List.mem_cons_of_mem s ht))
      refine ⟨min δ ε,lt_min hδ hε,?_⟩
      filter_upwards [hhead,htail,eventually_ge_atTop (1:ℕ)] with m hhead htail hm
      intro t ht a b c hfit
      rcases List.mem_cons.mp ht with hts | htL
      · subst t
        exact hhead a b c (s.fits_mono (min_le_left _ _) hm hfit)
      · exact htail t htL a b c (t.fits_mono (min_le_right _ _) hm hfit)
  exact hfinite shapes (fun _ h => h)

def twoLevelCoarseShape : PositiveScaleneShape :=
  ⟨57/50,1,1,by norm_num,by norm_num,by norm_num⟩

def twoLevelTrueShape : PositiveScaleneShape :=
  ⟨59/50,1,14/25,by norm_num,by norm_num,by norm_num⟩

def twoLevelFineShape : PositiveScaleneShape :=
  ⟨7/6,1,14/25,by norm_num,by norm_num,by norm_num⟩

def twoLevelSquareShape : PositiveScaleneShape :=
  ⟨1,1,1,by norm_num,by norm_num,by norm_num⟩

def twoLevelFullOutputShape : PositiveScaleneShape :=
  ⟨59/50,14/25,59/50,by norm_num,by norm_num,by norm_num⟩

theorem twoLevelSquareShape_bound :
    scaleneBound twoLevelSquareShape.u twoLevelSquareShape.v twoLevelSquareShape.w = 9/4 := by
  norm_num [twoLevelSquareShape,scaleneBound]

theorem twoLevelCoarseShape_bound :
    scaleneBound twoLevelCoarseShape.u twoLevelCoarseShape.v twoLevelCoarseShape.w = 3362/1425 :=
  scaleneBound_coarse

theorem twoLevelTrueShape_bound :
    scaleneBound twoLevelTrueShape.u twoLevelTrueShape.v twoLevelTrueShape.w = 9006001/4130000 :=
  scaleneBound_true

theorem twoLevelFineShape_bound :
    scaleneBound twoLevelFineShape.u twoLevelFineShape.v twoLevelFineShape.w = 867/400 :=
  scaleneBound_fine

theorem twoLevelFullOutputShape_bound :
    scaleneBound twoLevelFullOutputShape.u twoLevelFullOutputShape.v twoLevelFullOutputShape.w = 59/25 := by
  norm_num [twoLevelFullOutputShape,scaleneBound]

def twoLevelRuntimeFinalShapes : List PositiveScaleneShape :=
  twoLevelCoarseShape.permutations ++ twoLevelTrueShape.permutations ++
    twoLevelFineShape.permutations ++ twoLevelFullOutputShape.permutations ++ [twoLevelSquareShape]

theorem twoLevelRuntimeFinalShapes_coarse : twoLevelCoarseShape ∈ twoLevelRuntimeFinalShapes := by
  simp [twoLevelRuntimeFinalShapes,PositiveScaleneShape.permutations]

theorem twoLevelRuntimeFinalShapes_true : twoLevelTrueShape ∈ twoLevelRuntimeFinalShapes := by
  simp [twoLevelRuntimeFinalShapes,PositiveScaleneShape.permutations]

theorem twoLevelRuntimeFinalShapes_fine : twoLevelFineShape ∈ twoLevelRuntimeFinalShapes := by
  simp [twoLevelRuntimeFinalShapes,PositiveScaleneShape.permutations]

theorem twoLevelRuntimeFinalShapes_square : twoLevelSquareShape ∈ twoLevelRuntimeFinalShapes := by
  simp [twoLevelRuntimeFinalShapes]

theorem twoLevelRuntimeFinalShapes_fullOutput : twoLevelFullOutputShape ∈ twoLevelRuntimeFinalShapes := by
  simp [twoLevelRuntimeFinalShapes,PositiveScaleneShape.permutations]

def twoLevelRuntimeGlobalExponent : ℝ := 9/4+1/100000

structure TwoLevelGlobalKernelFamily where
  kernel : ∀ a b c : ℕ, ArithmeticKernel a b c
  constant : ℝ
  constant_pos : 0 < constant
  bound : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
    ((kernel a b c).cost:ℝ) ≤ constant*(D:ℝ)^twoLevelRuntimeGlobalExponent

def chosenTwoLevelGlobalKernelFamily : TwoLevelGlobalKernelFamily := Classical.choice (by
  obtain ⟨K,C,hC,hK⟩ := exists_full_shape_arithmetic_kernels (1/100000) (by norm_num)
  exact ⟨⟨K,C,hC,hK⟩⟩)

def twoLevelRuntimeFinalFallback (a b c : ℕ) : ArithmeticKernel a b c :=
  (chosenTwoLevelGlobalKernelFamily.kernel a b c).cheaper (classicalArithmeticKernels a b c)

def twoLevelRuntimeFinalKernels (m : ℕ) : ∀ a b c : ℕ, ArithmeticKernel a b c :=
  finiteScaleneKernelFamily twoLevelRuntimeFinalShapes twoLevelRuntimeFinalFallback m

theorem twoLevelRuntimeFinalKernels_classical (m a b c : ℕ) :
    (twoLevelRuntimeFinalKernels m a b c).cost ≤ 2*a*b*c := by
  exact (finiteScaleneKernelFamily_cost_le_fallback _ _ m a b c).trans
    ((ArithmeticKernel.cheaper_cost_le_right _ _).trans_eq (classicalArithmeticKernels_cost a b c))

theorem twoLevelRuntimeFinalKernels_global :
    ∃ C : ℝ, 0 < C ∧ ∀ m a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((twoLevelRuntimeFinalKernels m a b c).cost:ℝ) ≤ C*(D:ℝ)^twoLevelRuntimeGlobalExponent := by
  refine ⟨chosenTwoLevelGlobalKernelFamily.constant,chosenTwoLevelGlobalKernelFamily.constant_pos,?_⟩
  intro m a b c D hD ha hb hc
  have hcost : (twoLevelRuntimeFinalKernels m a b c).cost ≤
      (chosenTwoLevelGlobalKernelFamily.kernel a b c).cost :=
    (finiteScaleneKernelFamily_cost_le_fallback _ _ m a b c).trans
      (ArithmeticKernel.cheaper_cost_le_left _ _)
  exact (Nat.cast_le.mpr hcost).trans (chosenTwoLevelGlobalKernelFamily.bound a b c D hD ha hb hc)

/-- Every critical shape and all six permutations use the same fixed family.
The positive padding allowance is uniform over the entire finite list. -/
theorem twoLevelRuntimeFinalKernels_scalene (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ s ∈ twoLevelRuntimeFinalShapes, ∀ a b c : ℕ, s.Fits δ m a b c →
        ((twoLevelRuntimeFinalKernels m a b c).cost:ℝ) ≤
          (m:ℝ)^(scaleneBound s.u s.v s.w+ζ) :=
  finiteScaleneKernelFamily_uniform_eventually twoLevelRuntimeFinalShapes twoLevelRuntimeFinalFallback ζ hζ

theorem twoLevelRuntimeFinalKernels_square (ζ : ℝ) (hζ : 0 < ζ) :
    ∀ᶠ m : ℕ in atTop, ∀ a b c : ℕ, a ≤ m → b ≤ m → c ≤ m →
      ((twoLevelRuntimeFinalKernels m a b c).cost:ℝ) ≤ (m:ℝ)^(9/4+ζ) := by
  obtain ⟨δ,hδ,hK⟩ := twoLevelRuntimeFinalKernels_scalene ζ hζ
  filter_upwards [hK,eventually_ge_atTop (1:ℕ)] with m hm hm1
  intro a b c ha hb hc
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hwidth : m ≤ width (1+δ) m := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hmR (show (1:ℝ) ≤ 1+δ by linarith)
    rw [Real.rpow_one] at hpow
    exact_mod_cast hpow.trans (Nat.le_ceil ((m:ℝ)^(1+δ)))
  have hcost := hm twoLevelSquareShape twoLevelRuntimeFinalShapes_square a b c
    ⟨ha.trans hwidth,hb.trans hwidth,hc.trans hwidth⟩
  simpa only [twoLevelSquareShape_bound] using hcost

#print axioms twoLevelRuntimeFinalKernels_scalene

end
end HierarchicalAbsoluteSpectral
