import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice

import FormalRamsey.G6
import FormalRamsey.G6Visualizer

def RamseyGraphProp (N s t : ℕ) : Prop := (∀ (G : SimpleGraph (Fin N)) [DecidableRel G.Adj], (∃ S, G.IsNClique s S) ∨ (∃ T, G.IsNIndepSet t T))

lemma RamseyGraphMonotone : ∀ {N s t}, RamseyGraphProp N s t → ∀ {M}, N ≤ M → RamseyGraphProp M s t := by
  unfold RamseyGraphProp
  intros N s t R M NleqM G _
  let subAdj : Fin N → Fin N → Prop := λ u v ↦ G.Adj (Fin.castLE NleqM u) (Fin.castLE NleqM v)
  have subAdjSym : Symmetric subAdj := by
    unfold Symmetric
    intros _ _ xAdjy
    simp [subAdj, SimpleGraph.Adj.symm xAdjy]
  have subAdjLoopless : Irreflexive subAdj := by
    unfold Irreflexive
    simp [subAdj]
  let G' : SimpleGraph (Fin N) := { Adj := subAdj, symm := subAdjSym, loopless := subAdjLoopless }
  rcases R G' with ⟨S, SProp⟩ | ⟨S, SProp⟩
  left; swap; right
  all_goals{
    use S.map (Fin.castLEEmb NleqM)
    simp [SimpleGraph.isNClique_iff, SimpleGraph.IsClique, SimpleGraph.isNIndepSet_iff, SimpleGraph.IsIndepSet, Set.Pairwise, G', subAdj] at SProp ⊢
    simp [SProp.right]
    intros x _ y _ _
    simp_all
  }

theorem RamseyGraphPropSymm : ∀ N s t, RamseyGraphProp N s t ↔ RamseyGraphProp N t s := by
  have helper : ∀ N s t, RamseyGraphProp N s t → RamseyGraphProp N t s := by
    simp [RamseyGraphProp]
    intros N s t R G
    cases R Gᶜ with
    | inl R =>
      right
      rcases R with ⟨S, Sprop⟩
      simp at Sprop
      use S
    | inr R =>
      left
      rcases R with ⟨T, Tprop⟩
      simp at Tprop
      use T
  intros N s t
  use helper N s t, helper N t s

noncomputable def GraphRamsey (s t : ℕ) : ℕ := sInf { N : ℕ | RamseyGraphProp N s t }

theorem GraphRamsey2 : ∀ k : ℕ, GraphRamsey 2 k.succ = k.succ := by
  intros k
  unfold GraphRamsey
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  simp
  apply And.intro
  · unfold RamseyGraphProp
    intros G _
    simp [SimpleGraph.isNClique_iff, SimpleGraph.IsClique, SimpleGraph.isNIndepSet_iff, SimpleGraph.IsIndepSet, Set.Pairwise]
    rcases Finset.eq_empty_or_nonempty (G.edgeFinset) with GEmp | ⟨⟨x,y⟩, xyInG⟩
    · rw [Finset.eq_empty_iff_forall_notMem] at GEmp
      right
      use Finset.univ
      simp_all
      intros x y _
      let e: Sym2 (Fin (k + 1)) := s(x, y)
      rw [← SimpleGraph.mem_edgeSet]
      exact GEmp e
    · left
      use {x, y}
      simp[Finset.card_eq_two]
      simp at xyInG
      apply And.intro
      · apply And.intro <;> intros <;> simp [xyInG, SimpleGraph.Adj.symm]
      · use x, y
        simp
        intro h
        simp_all
  · simp [RamseyGraphProp, SimpleGraph.isNClique_iff, SimpleGraph.IsClique, SimpleGraph.isNIndepSet_iff, SimpleGraph.IsIndepSet, Set.Pairwise]
    use (⊥ : SimpleGraph (Fin k))
    simp
    apply And.intro
    · intro e eProp eCard
      rw [Finset.card_eq_two] at eCard
      rcases eCard with ⟨x, y, xneqy, exy⟩
      simp [exy, xneqy] at eProp
    · intros S Scard
      have tmp := card_finset_fin_le S
      simp [Scard] at tmp
  · intros M₁ M₂ M₁leM₂
    simp
    intro M₁Ramsey
    apply RamseyGraphMonotone M₁Ramsey M₁leM₂

theorem RamseyGraph1Prop : ∀ N k : ℕ, RamseyGraphProp N.succ 1 k := by
  intros
  simp [RamseyGraphProp]
  intros
  left
  use {0}
  simp [SimpleGraph.isNClique_iff]

theorem RamseyGraph1 : ∀ k : ℕ, GraphRamsey 1 k.succ = 1 := by
  intro k
  simp [GraphRamsey]
  have Ramsey1Monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | RamseyGraphProp N 1 k.succ } → M₂ ∈ { N : ℕ | RamseyGraphProp N 1 k.succ } := by
    intros M₁ M₂ M₁leM₂
    simp
    intro M₁RamseyG
    apply RamseyGraphMonotone M₁RamseyG M₁leM₂
  --NOTE: used to be rewrite[Nat.sInf_upward_closed_eq_succ_iff] (Ramsey1Monotone)
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  · simp [RamseyGraph1Prop 0 k.succ]
    simp [RamseyGraphProp]
    use (⊥ : SimpleGraph (Fin 0))
    intros x botIndep
    have xempty : x = ∅ := by simp [Finset.eq_empty_iff_forall_notMem]
    have ctr := botIndep.card_eq
    simp [xempty] at ctr
  · assumption

open ProofWidgets

theorem R34 : ¬(RamseyGraphProp 8 3 4) := by
  simp only [RamseyGraphProp, not_forall]
  g6 "GhdGKC"
  with_panel_widgets [SelectionPanel]
  simp [not_or]
  apply And.intro
  · intros S
    rw [← SimpleGraph.mem_cliqueFinset_iff]
    have cliqueFree : (readG6 "GhdGKC").cliqueFinset 3 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.notMem_empty S
  · intros T
    rw [← SimpleGraph.mem_indepSetFinset_iff]
    have cliqueFree : (readG6 "GhdGKC").indepSetFinset 4 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.notMem_empty T

theorem R35 : ¬(RamseyGraphProp 13 3 5) := by
  simp only [RamseyGraphProp, not_forall]
  g6 "LhEIHEPQHGaPaP"
  with_panel_widgets [SelectionPanel]
  simp [not_or]
  apply And.intro
  · intros S
    rw [← SimpleGraph.mem_cliqueFinset_iff]
    have cliqueFree : (readG6 "LhEIHEPQHGaPaP").cliqueFinset 3 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.notMem_empty S
  · intros T
    rw [← SimpleGraph.mem_indepSetFinset_iff]
    have cliqueFree : (readG6 "LhEIHEPQHGaPaP").indepSetFinset 5 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.notMem_empty T

-- NOTE: This is required since leanprover/lean4:v4.16.0-rc1
set_option maxHeartbeats 500000

theorem R44' : ¬(RamseyGraphProp 17 4 4) := by
  simp only [RamseyGraphProp, not_forall]
  g6 "P}qTKukXaUja[IBjanPeMI\\K"
  with_panel_widgets [SelectionPanel]
  simp [not_or]
  apply And.intro
  · intros S
    rw [← SimpleGraph.mem_cliqueFinset_iff]
    have cliqueFree : (readG6 "P}qTKukXaUja[IBjanPeMI\\K").cliqueFinset 4 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.notMem_empty S
  · intros T
    rw [← SimpleGraph.mem_indepSetFinset_iff]
    have cliqueFree : (readG6 "P}qTKukXaUja[IBjanPeMI\\K").indepSetFinset 4 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.notMem_empty T
