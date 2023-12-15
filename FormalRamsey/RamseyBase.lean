import Mathlib.Combinatorics.SimpleGraph.Clique

import FormalRamsey.Utils

namespace Ramsey

def graphAtColor {N k : ℕ} (G : SimpleGraph (Fin N)) (ϕ : Sym2 (Fin N) → Fin k)
 (i : Fin k): SimpleGraph (Fin N) := {
  Adj := λ u v ↦ (G.Adj u v) ∧ (ϕ ⟦(u, v)⟧ = i),
  symm := by
    unfold Symmetric
    intros _ _ h
    rcases h with ⟨Gxy,ϕxy⟩
    apply And.intro
    apply G.symm Gxy
    rw [Sym2.eq_swap]
    exact ϕxy,
  loopless :=  by
    unfold Irreflexive
    intros _ h
    simp at h
 }

def RamseyProp {k : ℕ} (N : ℕ) (s : Vector ℕ k.succ) : Prop :=
∀ f : Sym2 (Fin N) → Fin k.succ,
(∃ S i, (graphAtColor (completeGraph (Fin N)) f i).IsNClique (s.get i) S)

lemma RamseyProp0 : ∀ {k : ℕ} {s : Vector ℕ k.succ}, RamseyProp 0 s → ∃ (i : Fin k.succ), s.get i = 0 := by
  intros k s R
  simp [RamseyProp] at R
  rcases (R (λ _ ↦ 0)) with ⟨S, c, SNclique⟩
  simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at SNclique
  have Sempty : S = ∅ := by simp
  simp [Sempty] at SNclique
  use c
  rw [SNclique]

lemma RamseyMonotone : ∀ {N k : ℕ} {s : Vector ℕ k.succ}, RamseyProp N s → ∀ {M}, N ≤ M → RamseyProp M s := by
  unfold RamseyProp
  intros N k s R M NleqM
  intros f
  let f' : Sym2 (Fin N) → Fin k.succ := λ e ↦ f (Sym2.map (Fin.castLE NleqM) e)
  rcases (R f') with ⟨S,⟨i, Sclique, Scard⟩⟩
  use Finset.map (Fin.castLEEmb NleqM).toEmbedding S, i
  constructor
  simp [graphAtColor, SimpleGraph.isClique_iff, Set.Pairwise] at Sclique ⊢
  intros a ainS b binS aneqb_cast
  have aneqb : ¬ a = b := by intro h; simp[h] at aneqb_cast
  have ScliqueMap := Sclique ainS binS aneqb
  simp_all
  simp [Scard]
  done

def monochromaticVicinity {α : Type} [Fintype α] {c : ℕ} (g : SimpleGraph α) [DecidableRel g.Adj] (v : α) (f : Sym2 α → Fin c) (i : Fin c) : Finset α := Finset.filter (λ x ↦  f ⟦(v, x)⟧ = i) (g.neighborFinset v)

lemma monochromaticVicinity_Ramsey {N c : ℕ} {v : Fin N} {f : Sym2 (Fin N) → Fin c.succ} {i : Fin c.succ} {s : Vector ℕ c.succ} : RamseyProp ((monochromaticVicinity (⊤:SimpleGraph (Fin N)) v f i).card) s → (∃ S, (graphAtColor (completeGraph (Fin N)) f i).IsNClique (s.get i).succ S) ∨ (∃ i' S, i' ≠ i ∧ (graphAtColor (completeGraph (Fin N)) f i').IsNClique (s.get i') S) := by
  intro vicinityProp
  have cardeq : (Finset.card (@Finset.univ (Fin (monochromaticVicinity (⊤:SimpleGraph (Fin N)) v f i).card) _)) = (monochromaticVicinity (⊤:SimpleGraph (Fin N)) v f i).card := by simp
  cases bijection_of_eq_card cardeq with
  | inl bothEmpty =>
    simp [bothEmpty.right] at vicinityProp
    unfold RamseyProp at vicinityProp
    rcases (vicinityProp (λ _ ↦ 0)) with ⟨S, j, SNClique⟩
    simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at SNClique
    have Sempty : S = ∅ := by simp
    simp [Sempty] at SNClique
    rcases (instDecidableEqFin c.succ j i) with h | h
    · right
      use j, ∅
      simp [← SNClique, h, SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor]
    · left
      use {v}
      simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor]
      rw [← h, SNClique]
  | inr bijMapper =>
    rcases bijMapper with ⟨mapper, mapperBij⟩
    let ftrans : Fin (monochromaticVicinity (⊤:SimpleGraph (Fin N)) v f i).card → Fin N := λ x ↦ ↑(mapper ⟨x, Finset.mem_univ x⟩)
    have ftransembinj : Function.Injective ftrans := by
      intros _ _ fa₁a₂
      simp at fa₁a₂
      have a₁a₂eq := mapperBij.left (Subtype.ext fa₁a₂)
      simp at a₁a₂eq
      exact a₁a₂eq
    let ftransemb : Function.Embedding _ _ := ⟨ftrans, ftransembinj⟩
    rcases vicinityProp (λ e ↦ f (e.map (λ x ↦ ↑(mapper ⟨x, Finset.mem_univ x⟩)))) with ⟨S, ⟨i', Sclique⟩⟩
    rcases (instDecidableEqFin c.succ i' i) with h | h
    · right
      use i'
      simp [h]
      use S.map ftransemb
      constructor
      · simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor]
        intros a ainS b binS ftransneq
        simp [ftransneq]
        simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at Sclique
        rcases (instDecidableEqFin _ a b) with aneqb | aeqb
        have abedge := Sclique.clique ainS binS aneqb
        simp at abedge
        exact abedge.right
        simp [aeqb] at ftransneq
      · simp
        exact Sclique.card_eq
    · left
      use (insert v (S.map ftransemb))
      constructor
      simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor]
      apply And.intro
      · intros a _ _
        have mapperprop := (mapper ⟨a, Finset.mem_univ a⟩).prop
        simp [monochromaticVicinity] at mapperprop
        exact mapperprop
      · intros a ainS
        have mapperprop := (mapper ⟨a, Finset.mem_univ a⟩).prop
        simp [monochromaticVicinity] at mapperprop
        apply And.intro
        · rw [Sym2.eq_swap]
          intros mapper
          simp [mapper, mapperprop.right]
        · intros b binS mapperneq
          simp [mapperneq]
          simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at Sclique
          rcases (instDecidableEqFin _ a b) with aneqb | aeqb
          · have abedge := Sclique.clique ainS binS aneqb
            simp at abedge
            simp [← h, abedge.right]
          · simp [aeqb] at mapperneq
      · have vnotinSmap : v ∉ (S.map ftransemb) := by
          simp_all
          intros a _ mappera
          have mapperat := (mapper ⟨a, Finset.mem_univ a⟩).prop
          simp [mappera, monochromaticVicinity] at mapperat
        rw [Finset.card_insert_of_not_mem vnotinSmap]
        simp [Sclique.card_eq, h]

end Ramsey
