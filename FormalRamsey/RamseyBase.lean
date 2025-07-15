import Mathlib.Combinatorics.SimpleGraph.Clique

import FormalRamsey.Utils

namespace Ramsey

def graphAtColor {N k : ℕ} (G : SimpleGraph (Fin N)) (f : Sym2 (Fin N) → Fin k) (i : Fin k): SimpleGraph (Fin N) := {
  Adj := λ u v ↦ (G.Adj u v) ∧ (f s(u, v) = i),
  symm := by
    unfold Symmetric
    intros _ _ h
    rcases h with ⟨Gxy, fxy⟩
    apply And.intro
    apply G.symm Gxy
    rw [Sym2.eq_swap]
    exact fxy,
  loopless :=  by
    unfold Irreflexive
    intros _ h
    simp at h
 }

instance : ∀ {N k : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (f : Sym2 (Fin N) → Fin k) (i : Fin k), DecidableRel (graphAtColor G f i).Adj := by
  intros _ _ G GAdj f i u v
  simp [graphAtColor]
  cases GAdj u v with
  | isTrue uvAdj =>
    cases instDecidableEqFin _ (f s(u, v)) i with
    | isTrue fuvi =>
      apply isTrue
      tauto
    | isFalse fuvneqi =>
      apply isFalse
      tauto
  | isFalse uvNotAdj =>
    apply isFalse
    tauto

def RamseyProp {k : ℕ} (N : ℕ) (s : List.Vector ℕ k.succ) : Prop :=
∀ f : Sym2 (Fin N) → Fin k.succ,
(∃ S i, (graphAtColor ⊤ f i).IsNClique (s.get i) S)

instance : ∀ (k : ℕ) (s : List.Vector ℕ k.succ), DecidablePred (Membership.mem { N | RamseyProp N s }) := by
  intros k s N
  simp [RamseyProp]
  infer_instance

lemma RamseyProp0 : ∀ {k : ℕ} {s : List.Vector ℕ k.succ}, RamseyProp 0 s → ∃ (i : Fin k.succ), s.get i = 0 := by
  intros k s R
  simp [RamseyProp] at R
  rcases (R (λ _ ↦ 0)) with ⟨S, c, SNclique⟩
  simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at SNclique
  have Sempty : S = ∅ := by simp [Finset.eq_empty_iff_forall_notMem]
  simp [Sempty] at SNclique
  use c
  rw [SNclique]

lemma RamseyMonotone : ∀ {N k : ℕ} {s : List.Vector ℕ k.succ}, RamseyProp N s → ∀ {M}, N ≤ M → RamseyProp M s := by
  unfold RamseyProp
  intros N k s R M NleqM
  intros f
  let f' : Sym2 (Fin N) → Fin k.succ := λ e ↦ f (Sym2.map (Fin.castLE NleqM) e)
  rcases (R f') with ⟨S,⟨i, Sclique, Scard⟩⟩
  use Finset.map (Fin.castLEEmb NleqM) S, i
  constructor
  · simp [graphAtColor, SimpleGraph.isClique_iff, Set.Pairwise] at Sclique ⊢
    intros a ainS b binS aneqb_cast
    have aneqb : ¬ a = b := by intro h; simp[h] at aneqb_cast
    have ScliqueMap := Sclique ainS binS aneqb
    simp_all [f']
  · simp [Scard]

def monochromaticVicinity {α : Type} [Fintype α] {c : ℕ} (g : SimpleGraph α) [DecidableRel g.Adj] (v : α) (f : Sym2 α → Fin c) (i : Fin c) : Finset α := Finset.filter (λ x ↦  f s(v, x) = i) (g.neighborFinset v)

lemma monochromaticVicinity_Ramsey {N c : ℕ} {v : Fin N} {f : Sym2 (Fin N) → Fin c.succ} {i : Fin c.succ} {s : List.Vector ℕ c.succ} : RamseyProp ((monochromaticVicinity ⊤ v f i).card) s → (∃ S, (graphAtColor ⊤ f i).IsNClique (s.get i).succ S) ∨ (∃ i' S, i' ≠ i ∧ (graphAtColor ⊤ f i').IsNClique (s.get i') S) := by
  intro vicinityProp
  have cardeq : (Finset.card (@Finset.univ (Fin (monochromaticVicinity ⊤ v f i).card) _)) = (monochromaticVicinity ⊤ v f i).card := by simp
  cases bijection_of_eq_card cardeq with
  | inl bothEmpty =>
    simp [bothEmpty.right] at vicinityProp
    unfold RamseyProp at vicinityProp
    rcases (vicinityProp (λ _ ↦ 0)) with ⟨S, j, SNClique⟩
    simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at SNClique
    have Sempty : S = ∅ := by simp [Finset.eq_empty_iff_forall_notMem]
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
    let ftrans : Fin (monochromaticVicinity ⊤ v f i).card → Fin N := λ x ↦ ↑(mapper ⟨x, Finset.mem_univ x⟩)
    have ftransembinj : Function.Injective ftrans := by
      intros _ _ fa₁a₂
      simp [ftrans] at fa₁a₂
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
        have abedge := Sclique.isClique ainS binS aneqb
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
        simp only [monochromaticVicinity, Finset.mem_filter, SimpleGraph.mem_neighborFinset, SimpleGraph.top_adj] at mapperprop
        exact mapperprop
      · intros a ainS
        have mapperprop := (mapper ⟨a, Finset.mem_univ a⟩).prop
        simp only [monochromaticVicinity, Finset.mem_filter, SimpleGraph.mem_neighborFinset, SimpleGraph.top_adj] at mapperprop
        apply And.intro
        · rw [Sym2.eq_swap]
          intros ftransnotv
          simp [ftransemb, ftrans, mapperprop.right] at ftransnotv ⊢
          assumption
        · intros b binS mapperneq
          simp [mapperneq]
          simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at Sclique
          rcases (instDecidableEqFin _ a b) with aneqb | aeqb
          · have abedge := Sclique.isClique ainS binS aneqb
            simp at abedge
            simp [← h, ftransemb, ftrans, abedge.right]
          · simp [aeqb] at mapperneq
      · have vnotinSmap : v ∉ (S.map ftransemb) := by
          simp_all
          intros a _ mappera
          have mapperat := (mapper ⟨a, Finset.mem_univ a⟩).prop
          simp [ftransemb, ftrans] at mappera
          simp only [mappera, monochromaticVicinity, Finset.mem_filter, SimpleGraph.mem_neighborFinset, SimpleGraph.top_adj] at mapperat
          simp [← mappera] at mapperat
        rw [Finset.card_insert_of_notMem vnotinSmap]
        simp [Sclique.card_eq, h]

end Ramsey
