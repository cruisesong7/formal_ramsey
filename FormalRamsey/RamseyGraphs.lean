import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Clique
-- import Mathlib.Data.Vector3
-- import Mathlib.Data.Rat.NNRat

-- import Lean.Parser.Tactic
import Mathlib.Tactic
-- import FormalRamsey.PickTactic
-- import FormalRamsey.Utils

def RamseyGraphProp (N s t : ℕ) : Prop := N > 0 ∧ (∀ (G : SimpleGraph (Fin N)), (∃ S, G.IsNClique s S) ∨ (∃ T, Gᶜ.IsNClique t T))

lemma RamseyGraphMonotone : ∀ {N s t}, RamseyGraphProp N s t → ∀ {M}, N ≤ M → RamseyGraphProp M s t := by
  unfold RamseyGraphProp
  intros N s t R M NleqM
  rcases R with ⟨Ngt0, R⟩
  apply And.intro
  linarith only[Ngt0, NleqM]
  intros G
  let subAdj : Fin N → Fin N → Prop := λ u v ↦ G.Adj (Fin.castLE NleqM u) (Fin.castLE NleqM v)
  have subAdjSym : Symmetric subAdj := sorry
  have subAdjLoopless : Irreflexive subAdj := sorry
  let G' : SimpleGraph (Fin N) := { Adj := subAdj, symm := subAdjSym, loopless := subAdjLoopless }
  cases R G' with
  | inl R =>
    -- Turn the set S of Fin N into a set S' of Fin M and use that
    left
    admit
  | inr R =>
    -- Turn the set T of Fin N into a set T' of Fin M and use that
    right
    admit
    
theorem RamseyGraphPropSymm : ∀ N s t, RamseyGraphProp N s t ↔ RamseyGraphProp N t s := by
  have helper : ∀ N s t, RamseyGraphProp N s t → RamseyGraphProp N t s := by
    simp [RamseyGraphProp]
    intros N s t Ngt0 R
    simp [Ngt0]
    intro G
    cases R Gᶜ with
    | inl R =>
      right
      rcases R with ⟨S, Sprop⟩
      use S
    | inr R =>
      left
      rcases R with ⟨T, Tprop⟩
      simp at Tprop
      use T
  intros N s t
  use helper N s t, helper N t s
  done

noncomputable def Ramsey (s t : ℕ) : ℕ := sInf { N : ℕ | RamseyGraphProp N s t }

theorem RamseyGraph2 : ∀ k : ℕ, Ramsey 2 k.succ = k.succ := sorry
  -- intros k
  -- unfold Ramsey₂

  -- have Ramsey₂2_monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | Ramsey₂Prop N 2 k.succ } → M₂ ∈ { N : ℕ | Ramsey₂Prop N 2 k.succ }
  -- intros M₁ M₂ M₁leM₂
  -- simp
  -- intro M₁Ramsey
  -- apply RamseyMonotone M₁Ramsey M₁leM₂

  -- rw [Nat.sInf_upward_closed_eq_succ_iff]
  -- simp
  -- apply And.intro
  -- simp [Ramsey₂Prop, RamseyProp]
  -- intros f
  -- rcases Finset.eq_empty_or_nonempty (Finset.filter 
  -- (λ (x : Sym2 (Fin k.succ))↦ ¬ x.IsDiag ∧ f x = 0) Finset.univ) with h|h
  -- rw [Finset.filter_eq_empty_iff] at h
  -- use Finset.univ,1
  -- constructor
  -- simp [graphAtColor, Vector.get, List.nthLe, SimpleGraph.isClique_iff, Set.Pairwise]
  -- intros x y xneqy
  -- let a: Sym2 (Fin (k + 1)) := ⟦(x, y)⟧
  -- rcases (Quotient.exists_rep a) with ⟨⟨fst,snd⟩,aprop⟩ 
  -- simp_all
  -- have nDiag : ¬Sym2.IsDiag a := by simp_all
  -- cases aprop <;> simp[← not0_eq1, (h a nDiag)] 
  -- simp [Vector.get, List.nthLe]
  -- rcases h with ⟨⟨fst,snd⟩ ,wprop⟩ 
  -- simp at wprop
  -- use {fst,snd},0
  -- constructor
  -- simp [SimpleGraph.isClique_iff, graphAtColor, Set.Pairwise]

  -- apply And.intro
  -- intro h ;simp[h] ;exact wprop.right
  -- intro h ;simp[h,Sym2.eq_swap] ;exact wprop.right
  -- simp [Vector.get,List.nthLe,Finset.card_eq_two]
  -- use fst,snd
  -- simp
  -- intro h
  -- rw [← Sym2.mk''_isDiag_iff] at h
  -- cases wprop.left h
  
  -- unfold Ramsey₂Prop
  -- unfold RamseyProp
  -- simp
  -- intro
  -- let f : Sym2 (Fin k) → Fin 2 := λ e ↦ 1
  -- use f
  -- by_contra h
  -- simp at h
  -- rcases h with ⟨ S, ⟨ i, SProp ⟩ ⟩ 
  -- fin_cases i

  -- rw [SimpleGraph.isNClique_iff] at SProp
  -- rcases SProp with ⟨SisClique,S_card⟩
  -- unfold graphAtColor at SisClique
  -- simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at SisClique
  -- simp [Vector.get, List.nthLe,Finset.card_eq_two] at S_card
  -- rcases S_card with ⟨x,y,⟨xneqy,Sxy⟩ ⟩ 
  -- have xins : x ∈ S := by rw [Sxy]; simp
  -- have yins : y ∈ S := by rw [Sxy]; simp
  -- exact SisClique xins yins xneqy

  -- have kcard : Fintype.card (Fin k) < k.succ := by simp
  -- have cliquefree : (graphAtColor (completeGraph (Fin k)) f 1).CliqueFree k.succ := by 
  --   apply SimpleGraph.cliqueFree_of_card_lt kcard
  -- unfold SimpleGraph.CliqueFree at cliquefree
  -- have Scontra :=  cliquefree S
  -- contradiction

  -- assumption
  -- done

theorem RamseyGraph1Prop : ∀ N k : ℕ, RamseyGraphProp N.succ 1 k := sorry
  -- intros
  -- simp [Ramsey₂Prop, RamseyProp]
  -- intros
  -- use {0}, 0
  -- constructor
  -- simp [SimpleGraph.isClique_iff, Set.Pairwise]
  -- simp [Vector.get]
  -- simp [List.nthLe]
  -- done

theorem RamseyGraph1 : ∀ k : ℕ, Ramsey 1 k.succ = 1 := sorry
  -- intro k
  -- simp [Ramsey₂]
  -- have Ramsey1Monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | Ramsey₂Prop N 1 k.succ } → M₂ ∈ { N : ℕ | Ramsey₂Prop N 1 k.succ }
  -- intros M₁ M₂ M₁leM₂
  -- simp
  -- intro M₁Ramsey
  -- apply RamseyMonotone M₁Ramsey M₁leM₂
  -- --NOTE: used to be rewrite[Nat.sInf_upward_closed_eq_succ_iff] (Ramsey1Monotone) 
  -- rw [Nat.sInf_upward_closed_eq_succ_iff] 
  -- simp
  -- apply And.intro
  -- apply Ramsey₂1Prop 0 k.succ
  -- simp [Ramsey₂Prop, RamseyProp]
  -- assumption
  -- done

theorem RamseyGraphFinite : ∀ s t : ℕ, { N : ℕ | RamseyGraphProp N s.succ t.succ }.Nonempty := by
  suffices RamseyGraphFiniteAdditive : ∀ m : ℕ, ∀ s t, m = s + t → { N : ℕ | RamseyGraphProp N s.succ t.succ }.Nonempty
  sorry
  sorry
  -- intros s t
  -- simp [RamseyGraphFiniteAdditive (s + t) s t]
  
  -- intro m
  -- induction' m with st ih
  -- intros s t h
  -- have h' := Eq.symm h
  -- simp at h'
  -- rcases h' with ⟨s0, t0⟩ 
  -- simp [s0, t0]
  -- use 1
  -- simp
  -- simp [Ramsey₂Prop, RamseyProp]
  -- intro
  -- use {0}, 0
  -- constructor<;> simp [SimpleGraph.isClique_iff, Set.Pairwise, Vector.head]
  -- intros s t h
  -- cases s<;>
  -- cases t
  -- use 1
  -- simp [Ramsey₂1Prop]
  -- use 1
  -- simp [Ramsey₂1Prop]
  -- use 1
  -- simp
  -- rw [Ramsey₂PropSymm]
  -- simp [Ramsey₂1Prop]
  -- next s t => 
  -- have stsuccpred := congr_arg Nat.pred h
  -- have s1t : st = s + t.succ
  -- simp at stsuccpred
  -- rw [stsuccpred]
  -- simp [Nat.succ_add]
  -- have st1 : st = s.succ + t
  -- simp at stsuccpred
  -- rw [stsuccpred]
  -- simp [Nat.add_succ]
  -- have RamseyS := ih s t.succ s1t
  -- have RamseyT := ih s.succ t st1
  -- rcases RamseyS with ⟨S, Sprop⟩ 
  -- rcases RamseyT with ⟨T, Tprop⟩ 
  -- simp at Sprop Tprop
  -- use S + T
  -- simp
  -- apply Ramsey₂PropIneq <;> assumption
  -- done

theorem RamseyGraphSymm : ∀  s t: ℕ, Ramsey s.succ t.succ = Ramsey t.succ s.succ := by
  sorry
  -- intros s t
  -- apply Nat.le_antisymm
  -- have RamseyM := Nat.sInf_mem (Ramsey₂Finite t s)
  -- apply Nat.sInf_le
  -- simp [Ramsey₂] at RamseyM ⊢
  -- rw [Ramsey₂PropSymm] at RamseyM
  -- assumption
  -- have RamseyN := Nat.sInf_mem (Ramsey₂Finite s t)
  -- apply Nat.sInf_le
  -- simp [Ramsey₂] at RamseyN ⊢
  -- rw [Ramsey₂PropSymm] at RamseyN
  -- assumption
  -- done
  

theorem RamseyGraph_binomial_coefficient_ineq : ∀ s t : ℕ, Ramsey s.succ t.succ 
≤ Nat.choose (s.succ + t.succ - 2) (s.succ - 1) := by
  intros s t

  induction' s with s' ihp₁ generalizing t
  simp [RamseyGraph1 t]

  induction' t with t' ihp₂
  rw [RamseyGraphSymm]
  simp [RamseyGraph1 s'.succ]
  transitivity Ramsey s'.succ t'.succ.succ + Ramsey s'.succ.succ t'.succ
  -- apply Ramsey₂Ineq s' t'

  -- have temp₁: Ramsey₂ s'.succ t'.succ.succ + Ramsey₂ s'.succ.succ t'.succ
  -- ≤ (s'.succ + t'.succ.succ - 2).choose s' + (s'.succ.succ + t'.succ - 2).choose s'.succ
  -- apply add_le_add
  -- exact ihp₁ t'.succ
  -- exact ihp₂

  -- have temp₂ :(s'.succ.succ + t'.succ.succ - 2).choose (s'.succ.succ - 1) = 
  -- (s'.succ + t'.succ.succ - 2).choose s' + (s'.succ.succ + t'.succ - 2).choose s'.succ
  -- := by simp [Nat.succ_add, Nat.add_succ,Nat.choose_succ_succ]
  -- rw [temp₂]
  -- exact temp₁
  -- done

#eval (List.finRange 8).sublistsLen 3

theorem R34 : Ramsey 3 4 = 9 := sorry
