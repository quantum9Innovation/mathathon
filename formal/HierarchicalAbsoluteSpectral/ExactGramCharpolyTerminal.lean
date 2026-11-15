import HierarchicalAbsoluteSpectral.ExactGramCharpolyKrylovBasis
import HierarchicalAbsoluteSpectral.ExactGramCharpolyCompanionOrbit

/-!
At a truncation length at least the ambient dimension, Cayley--Hamilton
closes the generator flags. Stable prefix completeness then forces every
selected generator orbit to be an initial interval of powers.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators

def exactGramEarlierSpan {n w : ℕ} (V : Matrix (Fin n) (Fin w) ℝ) (i : Fin w) :
    Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ {x | ∃ k, k < i ∧ x = exactGramColumn V k}

namespace ExactGramKrylovBasis

variable {n d : ℕ} {A : Core n}

theorem columns_independent (b : ExactGramKrylovBasis A d) :
    LinearIndependent ℝ (exactGramColumn b.basis) := by
  apply Matrix.mulVec_injective_iff.mp
  intro x y h
  have hh := congrArg (fun z => b.inverse *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, b.left_inverse, Matrix.one_mulVec] using hh

theorem column_not_mem_earlier (b : ExactGramKrylovBasis A d) (i : Fin b.width) :
    exactGramColumn b.basis i ∉ exactGramEarlierSpan b.basis i := by
  intro hi
  apply (linearIndependent_iff_notMem_span.mp b.columns_independent i)
  apply (Submodule.span_mono ?_) hi
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, ⟨Set.mem_univ _, by simpa using ne_of_lt hk⟩, rfl⟩

theorem prefix_le_earlier (b : ExactGramKrylovBasis A d) (i : Fin b.width)
    (cut : ExactGramKrylovLabel n) (hcut : cut < b.labels i) :
    exactGramPrefixSpan b.basis b.labels cut ≤ exactGramEarlierSpan b.basis i := by
  apply exactGramPrefixSpan_le_of_columns
  intro k hk
  apply Submodule.subset_span
  exact ⟨k, b.labels.strictMono.lt_iff_lt.mp (lt_of_le_of_lt hk hcut), rfl⟩

def generatorSpan (b : ExactGramKrylovBasis A d) (g : ℕ) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ {x | ∃ k, (ofLex (b.labels k)).1.val < g ∧
    x = exactGramColumn b.basis k}

theorem prefix_le_generator (b : ExactGramKrylovBasis A d) (j : Fin n) (e g : ℕ)
    (hjg : j.val < g) :
    exactGramPrefixSpan b.basis b.labels (toLex (j,e)) ≤ b.generatorSpan g := by
  apply exactGramPrefixSpan_le_of_columns
  intro k hk
  apply Submodule.subset_span
  refine ⟨k, ?_, rfl⟩
  have hlex := Prod.Lex.le_iff.mp hk
  simp only [ofLex_toLex] at hlex
  rcases hlex with hlt | ⟨heq,_⟩
  · exact lt_trans hlt hjg
  · simpa only [heq] using hjg

theorem orbit_mem_generator (b : ExactGramKrylovBasis A d) (hnd : n ≤ d)
    (g : ℕ) (j : Fin n) (hj : j.val < g) (e : ℕ) :
    (A^e) *ᵥ Pi.single j 1 ∈ b.generatorSpan g := by
  apply exactGram_pow_mulVec_mem_of_initial A (Pi.single j 1) (b.generatorSpan g) hnd
  intro i
  exact b.prefix_le_generator j i.val g hj (b.complete j i.val i.isLt)

theorem generator_le_earlier (b : ExactGramKrylovBasis A d) (i : Fin b.width) :
    b.generatorSpan (ofLex (b.labels i)).1.val ≤ exactGramEarlierSpan b.basis i := by
  apply Submodule.span_le.mpr
  rintro x ⟨k,hk,rfl⟩
  apply Submodule.subset_span
  refine ⟨k, ?_, rfl⟩
  apply b.labels.strictMono.lt_iff_lt.mp
  exact Prod.Lex.lt_iff.mpr (Or.inl hk)

theorem mul_column (b : ExactGramKrylovBasis A d) (i : Fin b.width) :
    A *ᵥ exactGramColumn b.basis i =
      (A^((ofLex (b.labels i)).2+1)) *ᵥ Pi.single (ofLex (b.labels i)).1 1 := by
  rw [b.column_eq, Matrix.mulVec_mulVec, pow_succ']

/-- The predecessor of every positive selected exponent is selected too. -/
theorem predecessor_selected (b : ExactGramKrylovBasis A d) (hnd : n ≤ d)
    (i : Fin b.width) (he : 0 < (ofLex (b.labels i)).2) :
    ∃ k, b.labels k = toLex ((ofLex (b.labels i)).1, (ofLex (b.labels i)).2-1) := by
  by_contra hmissing
  push_neg at hmissing
  let g := (ofLex (b.labels i)).1
  let e := (ofLex (b.labels i)).2
  have hbexp : e < d := b.exponent_lt i
  have hprev : (A^(e-1)) *ᵥ Pi.single g 1 ∈
      exactGramPrefixSpan b.basis b.labels (toLex (g,e-1)) :=
    b.complete g (e-1) (by dsimp [e]; omega)
  have hmap : exactGramPrefixSpan b.basis b.labels (toLex (g,e-1)) ≤
      (exactGramEarlierSpan b.basis i).comap A.mulVecLin := by
    apply exactGramPrefixSpan_le_of_columns
    intro k hk
    change A *ᵥ exactGramColumn b.basis k ∈ exactGramEarlierSpan b.basis i
    rw [b.mul_column]
    have hlex := Prod.Lex.le_iff.mp hk
    simp only [ofLex_toLex] at hlex
    rcases hlex with hgen | ⟨hgen,hexp⟩
    · apply b.generator_le_earlier i
      exact b.orbit_mem_generator hnd _ _ hgen _
    · have hne : (ofLex (b.labels k)).2 ≠ e-1 := by
        intro heq
        apply hmissing k
        apply ofLex.injective
        exact Prod.ext hgen heq
      have hnext : (ofLex (b.labels k)).2+1 < e := by omega
      have hnextd : (ofLex (b.labels k)).2+1 < d := hnext.trans hbexp
      have hcut : toLex ((ofLex (b.labels k)).1, (ofLex (b.labels k)).2+1) <
          b.labels i := by
        apply Prod.Lex.lt_iff.mpr
        exact Or.inr ⟨hgen,hnext⟩
      exact b.prefix_le_earlier i _ hcut
        (b.complete _ _ hnextd)
  have hmem := hmap hprev
  change A *ᵥ ((A^(e-1)) *ᵥ Pi.single g 1) ∈ exactGramEarlierSpan b.basis i at hmem
  rw [Matrix.mulVec_mulVec, ← pow_succ'] at hmem
  have hexp : e-1+1 = e := by omega
  rw [hexp] at hmem
  apply b.column_not_mem_earlier i
  simpa only [b.column_eq] using hmem

theorem lower_exponent_selected (b : ExactGramKrylovBasis A d) (hnd : n ≤ d)
    (g : Fin n) (e : ℕ) (i : Fin b.width) (hi : b.labels i = toLex (g,e))
    (q : ℕ) (hq : q ≤ e) : ∃ k, b.labels k = toLex (g,q) := by
  induction e generalizing i with
  | zero =>
      have hqzero : q = 0 := by omega
      subst q
      exact ⟨i,hi⟩
  | succ e ih =>
      by_cases heq : q = e+1
      · subst q; exact ⟨i,hi⟩
      · have hpos : 0 < (ofLex (b.labels i)).2 := by rw [hi]; simp
        obtain ⟨k,hk⟩ := b.predecessor_selected hnd i hpos
        have hk' : b.labels k = toLex (g,e) := by simpa only [hi, ofLex_toLex, Nat.add_sub_cancel] using hk
        exact ih k hk' (by omega)

theorem selected_exponent_lt_width (b : ExactGramKrylovBasis A d) (hnd : n ≤ d)
    (i : Fin b.width) : (ofLex (b.labels i)).2 < b.width := by
  let g := (ofLex (b.labels i)).1
  let e := (ofLex (b.labels i)).2
  have hchoose : ∀ q : Fin (e+1), ∃ k, b.labels k = toLex (g,q.val) := by
    intro q
    apply b.lower_exponent_selected hnd g e i rfl q.val
    exact Nat.le_of_lt_succ q.isLt
  choose f hf using hchoose
  have hinj : Function.Injective f := by
    intro q r h
    apply Fin.ext
    have hh := congrArg (fun z => (ofLex z).2) ((hf q).symm.trans ((congrArg b.labels h).trans (hf r)))
    exact hh
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  dsimp only [e] at hcard
  omega

end ExactGramKrylovBasis

end
end HierarchicalAbsoluteSpectral
