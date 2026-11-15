import HierarchicalAbsoluteSpectral.MainProblem

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section

def MainGaussianIndex.indexEquiv (n m p r L cap repetitions : ℕ) :
    MainGaussianIndex n m p r L cap repetitions ≃
      (Fin (L+1) × Fin 3 × Fin (2^dyadicPaddingLevel n)) ⊕
      ((Fin (L+1) × Fin 3 × Fin (2^dyadicPaddingLevel p)) ⊕
      ((Fin r × Fin m) ⊕
      ((Fin cap × Fin repetitions × Fin (r+1) × Fin m) ⊕
      ((Fin cap × Fin repetitions × Fin 2 × Fin (m*m)) ⊕ (Fin r × Fin m))))) where
  toFun
    | .sketchLeft j a i => .inl (j,a,i)
    | .sketchRight j a i => .inr (.inl (j,a,i))
    | .initializer j i => .inr (.inr (.inl (j,i)))
    | .query a b j i => .inr (.inr (.inr (.inl (a,b,j,i))))
    | .inertia a b j i => .inr (.inr (.inr (.inr (.inl (a,b,j,i)))))
    | .strong j i => .inr (.inr (.inr (.inr (.inr (j,i)))))
  invFun
    | .inl (j,a,i) => .sketchLeft j a i
    | .inr (.inl (j,a,i)) => .sketchRight j a i
    | .inr (.inr (.inl (j,i))) => .initializer j i
    | .inr (.inr (.inr (.inl (a,b,j,i)))) => .query a b j i
    | .inr (.inr (.inr (.inr (.inl (a,b,j,i))))) => .inertia a b j i
    | .inr (.inr (.inr (.inr (.inr (j,i))))) => .strong j i
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with x | x
    · rcases x with ⟨j,a,i⟩; rfl
    · rcases x with x | x
      · rcases x with ⟨j,a,i⟩; rfl
      · rcases x with x | x
        · rcases x with ⟨j,i⟩; rfl
        · rcases x with x | x
          · rcases x with ⟨a,b,j,i⟩; rfl
          · rcases x with x | x
            · rcases x with ⟨a,b,j,i⟩; rfl
            · rcases x with ⟨j,i⟩; rfl

theorem mainGaussianDrawCount (n m p r L cap repetitions : ℕ) :
    Fintype.card (MainGaussianIndex n m p r L cap repetitions)=
      3*(L+1)*(2^dyadicPaddingLevel n+2^dyadicPaddingLevel p)+2*r*m+
        cap*repetitions*((r+1)*m+2*m*m) := by
  rw [Fintype.card_congr (MainGaussianIndex.indexEquiv n m p r L cap repetitions)]
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  ring

def mainRandomizedWork {n m p r L : ℕ} (I : FixedProblem n m p r L) (bodyWork : ℕ) : ℕ :=
  Fintype.card (MainGaussianIndex n m p r L I.queryCap I.repetitions)+bodyWork

theorem mainRandomizedWork_eq {n m p r L : ℕ} (I : FixedProblem n m p r L) (bodyWork : ℕ) :
    mainRandomizedWork I bodyWork=
      3*(L+1)*(2^dyadicPaddingLevel n+2^dyadicPaddingLevel p)+2*r*m+
        I.queryCap*I.repetitions*((r+1)*m+2*m*m)+bodyWork := by
  exact congrArg (fun v : ℕ => v+bodyWork) (mainGaussianDrawCount _ _ _ _ _ _ _)

theorem mainGaussianDrawCount_input_core_bound {n m p r L : ℕ}
    (I : FixedProblem n m p r L) :
    Fintype.card (MainGaussianIndex n m p r L I.queryCap I.repetitions) ≤
      6*(L+1)*(m*(n+p))+(2+4*I.queryCap*I.repetitions)*m*m := by
  have hm : 1 ≤ m := I.rank_positive.trans I.rank_le_core
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < m) I.core_le_rows
  have hp : 0 < p := lt_of_lt_of_le (by omega : 0 < m) I.core_le_cols
  have hpadn := (dyadicPaddingLevel_lt_two n hn).le
  have hpadp := (dyadicPaddingLevel_lt_two p hp).le
  have hpad : 2^dyadicPaddingLevel n+2^dyadicPaddingLevel p ≤ 2*(n+p) := by omega
  have hsketch := Nat.mul_le_mul_left (3*(L+1)) hpad
  have hinput : n+p ≤ m*(n+p) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (n+p) hm
  have hinput' := Nat.mul_le_mul_left (6*(L+1)) hinput
  have hrank := Nat.mul_le_mul_right m I.rank_le_core
  have hrank' : r+1 ≤ 2*m := by have hh:=I.rank_le_core; omega
  have hquery' := Nat.mul_le_mul_right m hrank'
  have hquery : (r+1)*m+2*m*m ≤ 4*m*m := by nlinarith
  have hqueries := Nat.mul_le_mul_left (I.queryCap*I.repetitions) hquery
  rw [mainGaussianDrawCount]
  nlinarith

end
end HierarchicalAbsoluteSpectral
