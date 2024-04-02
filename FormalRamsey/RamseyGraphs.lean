import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice

import FormalRamsey.G6
import FormalRamsey.G6Visualizer

def RamseyGraphProp (N s t : ℕ) : Prop := (∀ (G : SimpleGraph (Fin N)) [DecidableRel G.Adj], (∃ S, G.IsNClique s S) ∨ (∃ T, Gᶜ.IsNClique t T))

lemma RamseyGraphMonotone : ∀ {N s t}, RamseyGraphProp N s t → ∀ {M}, N ≤ M → RamseyGraphProp M s t := by
  unfold RamseyGraphProp
  intros N s t R M NleqM G _
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
    intros N s t R G _
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

noncomputable def GraphRamsey (s t : ℕ) : ℕ := sInf { N : ℕ | RamseyGraphProp N s t }

theorem GraphRamsey2 : ∀ k : ℕ, GraphRamsey 2 k.succ = k.succ := by
  intros k
  unfold GraphRamsey

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
    let e: Sym2 (Fin (k + 1)) := s(x, y)
    have tmp := GEmp e
    simp_all

  · left
    use {x,y}
    simp[Finset.card_eq_two]
    simp at xyInG
    apply And.intro
    swap
    · use x, y
      simp
      intro h
      simp_all
    · apply And.intro <;> intros <;> simp [xyInG, SimpleGraph.Adj.symm]

  simp [RamseyGraphProp, SimpleGraph.isNClique_iff, SimpleGraph.IsClique, Set.Pairwise]
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

theorem RamseyGraph1 : ∀ k : ℕ, GraphRamsey 1 k.succ = 1 := by
  intro k
  simp [GraphRamsey]
  have Ramsey1Monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | RamseyGraphProp N 1 k.succ } → M₂ ∈ { N : ℕ | RamseyGraphProp N 1 k.succ }
  intros M₁ M₂ M₁leM₂
  simp
  intro M₁RamseyG
  apply RamseyGraphMonotone M₁RamseyG M₁leM₂
  --NOTE: used to be rewrite[Nat.sInf_upward_closed_eq_succ_iff] (Ramsey1Monotone)
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  simp [RamseyGraph1Prop 0 k.succ]
  simp [RamseyGraphProp]
  use (⊥ : SimpleGraph (Fin 0))
  simp
  intro x
  have xempty : x = ∅ := by simp[Finset.eq_empty_iff_forall_not_mem]
  simp [xempty, SimpleGraph.isNClique_iff]
  assumption
  done

open ProofWidgets

theorem R34 : ¬(RamseyGraphProp 8 3 4) := by
  simp [RamseyGraphProp]
  -- use readG6 "GhdGKC", (by infer_instance)
  g6 "GhdGKC"
  with_panel_widgets [SelectionPanel]
  simp [not_or]
  apply And.intro
  · intros S
    rw [← SimpleGraph.mem_cliqueFinset_iff]
    have cliqueFree : SimpleGraph.cliqueFinset (readG6 "GhdGKC") 3 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.not_mem_empty S
  · intros T
    rw [← SimpleGraph.mem_cliqueFinset_iff]
    have cliqueFree : SimpleGraph.cliqueFinset (readG6 "GhdGKC")ᶜ 4 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.not_mem_empty T


theorem R35 : ¬(RamseyGraphProp 13 3 5) := by
  simp [RamseyGraphProp]
  -- use readG6 "LhEIHEPQHGaPaP", (by infer_instance)
  g6 "LhEIHEPQHGaPaP"
  with_panel_widgets [SelectionPanel]
  simp [not_or]
  apply And.intro
  · intros S
    rw [← SimpleGraph.mem_cliqueFinset_iff]
    have cliqueFree : SimpleGraph.cliqueFinset (readG6 "LhEIHEPQHGaPaP") 3 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.not_mem_empty S
  · intros T
    rw [← SimpleGraph.mem_cliqueFinset_iff]
    have cliqueFree : SimpleGraph.cliqueFinset (readG6 "LhEIHEPQHGaPaP")ᶜ 5 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.not_mem_empty T
  done

theorem R44' : ¬(RamseyGraphProp 17 4 4) := by
  simp [RamseyGraphProp]
  -- use readG6 "P}qTKukXaUja[IBjanPeMI\\K", (by infer_instance)
  g6 "P}qTKukXaUja[IBjanPeMI\\K"
  with_panel_widgets [SelectionPanel]
  simp [not_or]
  apply And.intro
  · intros S
    rw [← SimpleGraph.mem_cliqueFinset_iff]
    have cliqueFree : SimpleGraph.cliqueFinset (readG6 "P}qTKukXaUja[IBjanPeMI\\K") 4 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.not_mem_empty S
  · intros T
    rw [← SimpleGraph.mem_cliqueFinset_iff]
    have cliqueFree : SimpleGraph.cliqueFinset (readG6 "P}qTKukXaUja[IBjanPeMI\\K")ᶜ 4 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.not_mem_empty T
  done
