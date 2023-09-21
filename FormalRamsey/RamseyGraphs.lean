import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice

def RamseyGraphProp (N s t : ℕ) : Prop := N > 0 ∧ (∀ (G : SimpleGraph (Fin N)) [DecidableRel G.Adj], (∃ S, G.IsNClique s S) ∨ (∃ T, Gᶜ.IsNClique t T))

lemma RamseyGraphMonotone : ∀ {N s t}, RamseyGraphProp N s t → ∀ {M}, N ≤ M → RamseyGraphProp M s t := by
  unfold RamseyGraphProp
  intros N s t R M NleqM
  rcases R with ⟨Ngt0, R⟩
  apply And.intro
  use (lt_of_lt_of_le Ngt0.lt NleqM)
  intros G _
  let subAdj : Fin N → Fin N → Prop := λ u v ↦ G.Adj (Fin.castLE NleqM u) (Fin.castLE NleqM v)
  have subAdjSym : Symmetric subAdj := by 
    unfold Symmetric
    simp
    intros _ _ xAdjy
    simp only [SimpleGraph.Adj.symm xAdjy]
  have subAdjLoopless : Irreflexive subAdj := by
    unfold Irreflexive
    simp
  let G' : SimpleGraph (Fin N) := { Adj := subAdj, symm := subAdjSym, loopless := subAdjLoopless }
  rcases R G' with ⟨S, SProp⟩ | ⟨S, SProp⟩
  left; swap; right
  all_goals{
    use S.map (Fin.castLEEmb NleqM).toEmbedding
    simp [SProp]
    simp [SimpleGraph.isNClique_iff, SimpleGraph.IsClique, Set.Pairwise] at SProp ⊢
    simp [SProp.right]
    intros x _ y _ _
    have xNeqy : x ≠ y := by intro; simp_all
    simp_all
  }
  
theorem RamseyGraphPropSymm : ∀ N s t, RamseyGraphProp N s t ↔ RamseyGraphProp N t s := by
  have helper : ∀ N s t, RamseyGraphProp N s t → RamseyGraphProp N t s := by
    simp [RamseyGraphProp]
    intros N s t Ngt0 R
    simp [Ngt0]
    intros G _
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

theorem RamseyGraph2 : ∀ k : ℕ, Ramsey 2 k.succ = k.succ := by
  intros k
  unfold Ramsey

  have RamseyGraph2Monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | RamseyGraphProp N 2 k.succ } → M₂ ∈ { N : ℕ | RamseyGraphProp N 2 k.succ }
  intros M₁ M₂ M₁leM₂
  simp
  intro M₁Ramsey
  apply RamseyGraphMonotone M₁Ramsey M₁leM₂

  rw [Nat.sInf_upward_closed_eq_succ_iff]
  simp
  apply And.intro
  simp [RamseyGraphProp, SimpleGraph.isNClique_iff, SimpleGraph.IsClique, Set.Pairwise]
  intros G _
  rcases Finset.eq_empty_or_nonempty (G.edgeFinset) with GEmp| ⟨⟨x,y⟩, xyInG⟩ 

  · rw [Finset.eq_empty_iff_forall_not_mem] at GEmp
    right
    use Finset.univ
    simp_all
    intros x y _
    let e: Sym2 (Fin (k + 1)) := ⟦(x, y)⟧
    have tmp := GEmp e
    simp_all

  · left
    use {x,y}
    simp[Finset.card_eq_two]
    simp at xyInG 
    have tmp := @SimpleGraph.mem_edgeSet (Fin k.succ) G x y
    change Quot.mk Setoid.r (x, y) ∈ SimpleGraph.edgeSet G ↔ SimpleGraph.Adj G x y at tmp
    rw [tmp] at xyInG 
    apply And.intro
    swap
    · use x, y
      simp
      intro h
      simp_all
    · apply And.intro <;> intros <;> simp [xyInG, SimpleGraph.Adj.symm]

  simp [RamseyGraphProp, SimpleGraph.isNClique_iff, SimpleGraph.IsClique, Set.Pairwise]
  intro
  use (⊥ : SimpleGraph (Fin k))
  by_contra h
  simp at h
  rcases (h (SimpleGraph.Bot.adjDecidable (Fin k))) with ⟨_, ⟨_, h⟩⟩ | ⟨S, h⟩ 
  rw [Finset.card_eq_two] at h
  rcases h with ⟨_, _, _, _⟩
  simp_all
  have tmp := card_finset_fin_le S
  rw [h , Nat.succ_eq_add_one] at tmp
  simp at tmp
  
  assumption
  done

theorem RamseyGraph1Prop : ∀ N k : ℕ, RamseyGraphProp N.succ 1 k := by
  intros
  simp [RamseyGraphProp]
  intros
  left
  use {0}
  simp [SimpleGraph.isNClique_iff]
  done

theorem RamseyGraph1 : ∀ k : ℕ, Ramsey 1 k.succ = 1 := by
  intro k
  simp [Ramsey]
  have Ramsey1Monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | RamseyGraphProp N 1 k.succ } → M₂ ∈ { N : ℕ | RamseyGraphProp N 1 k.succ }
  intros M₁ M₂ M₁leM₂
  simp
  intro M₁RamseyG
  apply RamseyGraphMonotone M₁RamseyG M₁leM₂
  --NOTE: used to be rewrite[Nat.sInf_upward_closed_eq_succ_iff] (Ramsey1Monotone) 
  rw [Nat.sInf_upward_closed_eq_succ_iff] 
  simp [RamseyGraph1Prop 0 k.succ]
  simp [RamseyGraphProp]
  assumption
  done

theorem RamseyGraphFinite : ∀ s t : ℕ, { N : ℕ | RamseyGraphProp N s.succ t.succ }.Nonempty := by
  suffices RamseyGraphFiniteAdditive : ∀ m : ℕ, ∀ s t, m = s + t → { N : ℕ | RamseyGraphProp N s.succ t.succ }.Nonempty
  intros s t
  simp [RamseyGraphFiniteAdditive (s + t) s t]
  
  intro m
  induction' m with st ih
  intros s t h
  have h' := Eq.symm h
  simp at h'
  rcases h' with ⟨s0, t0⟩ 
  simp [s0, t0]
  use 1
  simp
  simp [RamseyGraphProp]
  intros
  left
  use {0}
  simp [SimpleGraph.isNClique_iff, SimpleGraph.IsClique]
  intros s t h
  cases s<;>
  cases t
  use 1
  simp [RamseyGraphProp, SimpleGraph.isNClique_iff, SimpleGraph.IsClique, Set.Pairwise]
  use 1
  simp [RamseyGraphProp, SimpleGraph.isNClique_iff, SimpleGraph.IsClique, Set.Pairwise]
  use 1
  simp
  rw [RamseyGraphPropSymm]
  simp [RamseyGraph1Prop]
  next s t => 
  have stsuccpred := congr_arg Nat.pred h
  have s1t : st = s + t.succ
  simp at stsuccpred
  rw [stsuccpred]
  simp [Nat.succ_add]
  have st1 : st = s.succ + t
  simp at stsuccpred
  rw [stsuccpred]
  simp [Nat.add_succ]
  have RamseyS := ih s t.succ s1t
  have RamseyT := ih s.succ t st1
  rcases RamseyS with ⟨S, Sprop⟩ 
  rcases RamseyT with ⟨T, Tprop⟩ 
  simp at Sprop Tprop
  use S + T
  simp
  sorry
  -- apply Ramsey₂PropIneq <;> assumption
  -- done

theorem RamseyGraphSymm : ∀  s t: ℕ, Ramsey s.succ t.succ = Ramsey t.succ s.succ := by 
  intros s t
  apply Nat.le_antisymm
  have RamseyM := Nat.sInf_mem (RamseyGraphFinite t s)
  apply Nat.sInf_le
  simp [Ramsey] at RamseyM ⊢
  rw [RamseyGraphPropSymm] at RamseyM
  assumption
  have RamseyN := Nat.sInf_mem (RamseyGraphFinite s t)
  apply Nat.sInf_le
  simp [Ramsey] at RamseyN ⊢
  rw [RamseyGraphPropSymm] at RamseyN
  assumption
  done
  

theorem RamseyGraph_binomial_coefficient_ineq : ∀ s t : ℕ, Ramsey s.succ t.succ ≤ Nat.choose (s.succ + t.succ - 2) (s.succ - 1) := by
  intros s t

  induction' s with s' ihp₁ generalizing t
  simp [RamseyGraph1 t]

  induction' t with t' ihp₂
  rw [RamseyGraphSymm]
  simp [RamseyGraph1 s'.succ]
  transitivity Ramsey s'.succ t'.succ.succ + Ramsey s'.succ.succ t'.succ
  sorry
  sorry

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

-- #eval (List.finRange 8).sublistsLen 3

-- theorem R34 : Ramsey 3 4 = 9 := sorry
