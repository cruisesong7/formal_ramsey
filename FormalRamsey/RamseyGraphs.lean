import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice

import FormalRamsey.G6
import FormalRamsey.G6Visualizer
import FormalRamsey.Encodings.CNF.RamseyEncoder

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

namespace SimpleGraph

private theorem IsIndepSet.subset {α : Type} {G : SimpleGraph α} {s t : Finset α} (h : t ⊆ s) : G.IsIndepSet s → G.IsIndepSet t := Set.Pairwise.mono h

private lemma exists_isNClique_of_le_cliqueNum {α : Type} [Fintype α] {n : ℕ} {G : SimpleGraph α} (h : n ≤ G.cliqueNum) : ∃ S : Finset α, G.IsNClique n S := by
  rcases G.exists_isNClique_cliqueNum with ⟨s, sclique⟩
  have nlescard : n ≤ s.card := by simp [h, sclique.card_eq]
  obtain ⟨t, tprop⟩ := s.exists_subset_card_eq nlescard
  use t
  simp [← tprop.right, isNClique_iff]
  exact sclique.isClique.subset tprop.left

namespace Iso

private lemma IsClique {α : Type} {G G' : SimpleGraph α} (iso : G ≃g G') : ∀ s, G.IsClique s ↔ G'.IsClique (iso.toEquiv '' s) := by
  simp [SimpleGraph.IsClique, Set.Pairwise]
  intros
  apply Iff.intro <;> intros sprop u uins v vins uneqv
  · simp [← iso.map_rel_iff'] at sprop
    apply sprop <;> assumption
  · rw [← iso.map_rel_iff']
    simp
    apply sprop <;> assumption

private lemma IsIndepSet {α : Type} {G G' : SimpleGraph α} (iso : G ≃g G') : ∀ s, G.IsIndepSet s ↔ G'.IsIndepSet (iso.toEquiv '' s) := by
  simp [SimpleGraph.IsIndepSet, Set.Pairwise]
  intros
  apply Iff.intro <;> intros sprop u uins v vins uneqv
  · simp [← iso.map_rel_iff'] at sprop
    apply sprop <;> assumption
  · rw [← iso.map_rel_iff']
    simp
    apply sprop <;> assumption

private lemma IsNClique {α : Type} {G G' : SimpleGraph α} (iso : G ≃g G') : ∀ s, G.IsNClique n s ↔ G'.IsNClique n (s.map iso.toEquiv) := by simp [isNClique_iff, iso.IsClique]

private lemma IsNIndepSet {α : Type} {G G' : SimpleGraph α} (iso : G ≃g G') : ∀ s, G.IsNIndepSet n s ↔ G'.IsNIndepSet n (s.map iso.toEquiv) := by simp [isNIndepSet_iff, iso.IsIndepSet]

private lemma cliqueNum {α : Type} {G G' : SimpleGraph α} (iso : G ≃g G') : G.cliqueNum = G'.cliqueNum := by
  unfold SimpleGraph.cliqueNum
  congr
  ext n
  simp
  apply Iff.intro
  · intro Gclique
    obtain ⟨S, Sprop⟩ := Gclique
    use (S.map iso.toEquiv)
    rw [iso.IsNClique] at Sprop
    assumption
  · intro Gclique'
    obtain ⟨S', Sprop'⟩ := Gclique'
    use (S'.map iso.toEquiv.symm)
    simpa [iso.IsNClique, Finset.map_map]

end Iso

private lemma exists_isNIndset_of_le_indepNum  {α : Type} [Fintype α] {G : SimpleGraph α} (h : n ≤ G.indepNum) : ∃ S : Finset α, G.IsNIndepSet n S := by
  rcases G.exists_isNIndepSet_indepNum with ⟨s, sindset⟩
  have nlescard : n ≤ s.card := by simp [h, sindset.card_eq]
  obtain ⟨t, tprop⟩ := s.exists_subset_card_eq nlescard
  use t
  simp [← tprop.right, isNIndepSet_iff]
  exact sindset.isIndepSet.subset tprop.left

end SimpleGraph

open Trestle Model PropFun

theorem R36 : RamseyGraphProp 18 3 6 := by
  suffices Runsat: ¬(Sat (RamseyEncoding 17 3 6).val.toICnf.toPropFun) by
    simp [Sat, (RamseyEncoding 17 3 6).toICnf_equisatisfiable] at Runsat
    unfold RamseyGraphProp
    intros G GDecAdj
    let τ : PropAssignment (EdgeVar 18) := (λ e ↦ (GDecAdj e.i e.j).decide)
    have iso : G ≃g (assignment_to_graph τ true) := {
      toEquiv := by
        use id
        · use id
        · simp [Function.LeftInverse]
        · simp [Function.RightInverse, Function.LeftInverse],
      map_rel_iff' := by
       simp [τ, assignment_to_graph]
       intros u v
       split
       next vequ _ => simp [vequ]
       next vnequ _ =>
         simp [min_def, max_def]
         split
         next => exact G.adj_comm v u
         next => simp
    }
    cases Nat.decLt G.cliqueNum 3 with
    | isTrue Gcnlt3 =>
      right
      simp [iso.cliqueNum] at Gcnlt3
      obtain ⟨T, TIsNIndepSet⟩ := SimpleGraph.exists_isNIndset_of_le_indepNum (Runsat τ Gcnlt3)
      rw [iso.symm.IsNIndepSet] at TIsNIndepSet
      use T.map iso.symm.toEquiv
    | isFalse Gcnge3 =>
      left
      simp at Gcnge3
      exact G.exists_isNClique_of_le_cliqueNum Gcnge3
  simp [Sat]
  intros τ τmodels
  -- from here on one would add clauses until τ models ⊥ and we would be done
  sorry
