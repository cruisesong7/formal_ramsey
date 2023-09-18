import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.DoubleCounting
import Mathlib.Data.Rat.Floor 
import Mathlib.Algebra.Parity
import Mathlib.LinearAlgebra.AffineSpace.Combination

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

def RamseyProp (N k : ℕ) (s : Vector ℕ k.succ) : Prop := N > 0 ∧
∀ f : Sym2 (Fin N) → Fin k.succ,
(∃ S i, (graphAtColor (completeGraph (Fin N)) f i).IsNClique (s.get i) S) 

lemma RamseyMonotone : ∀ {N k s}, RamseyProp N k s → ∀ {M}, N ≤ M → RamseyProp M k s := by
  unfold RamseyProp
  intros N k s R M NleqM
  rcases R with ⟨Ngt0, R⟩
  apply And.intro
  linarith only[Ngt0, NleqM]
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

end Ramsey

lemma bijection_of_eq_card {α β : Type} [DecidableEq α] [DecidableEq β] : ∀ {s : Finset α} {t : Finset β}, s.card = t.card → ((s = ∅ ∧ t = ∅) ∨ ∃ f : ↥s → ↥t, Function.Bijective f) := by
  
  intro s
  induction' s using Finset.induction with a s anotins ih
  simp
  intros t h
  left
  rw [← Finset.card_eq_zero]
  symm
  exact h

  intros t tcard
  right
  rw [(Finset.card_insert_of_not_mem anotins)] at tcard
  have tinsert := Eq.symm tcard
  rw [Finset.card_eq_succ] at tinsert
  rcases tinsert with ⟨b, t', bnotint', bins, tcards⟩
  rcases (ih (Eq.symm tcards)) with stempt | fbij 
  simp [stempt.right] at bins
  rw [stempt.left, ← bins]
  have bobv : b ∈ t
  rw [← bins]
  exact Finset.mem_singleton_self b
  lift b to t using bobv
  rw [bins]
  use (λ _ : {y // y ∈ insert a ∅} ↦ b)
  apply And.intro
  intros a₁ a₂ _
  apply Subtype.ext
  have a₁prop := a₁.prop
  have a₂prop := a₂.prop
  simp at a₁prop a₂prop
  simp [a₁prop, a₂prop]
  intros b'
  use ⟨a, Finset.mem_insert_self a ∅⟩
  have b'prop := b'.prop
  simp [← bins] at b'prop
  apply Subtype.ext
  simp [b'prop]
  have bint : b ∈ t := by rw [← bins] ; simp
  rcases fbij with ⟨f, fbij⟩
  have fhelper : ∀ x, ↑(f x) ∈ t
  intros
  simp [← bins]
  use (λ x ↦ match Finset.decidableMem ↑x s with
  | isTrue p => ⟨f ⟨↑x, p⟩, fhelper ⟨↑x, p⟩⟩
  | isFalse _ => ⟨b, bint⟩)
  apply And.intro
  intros a₁ a₂ fa₁a₂
  simp at fa₁a₂
  split at fa₁a₂ <;> split at fa₁a₂ <;> simp at fa₁a₂
  next a₁ins _ _ a₂ins _ =>
    have a₁eqa₂ := fbij.left (Subtype.ext fa₁a₂)
    simp at a₁eqa₂
    exact Subtype.ext a₁eqa₂
  next a₁ins _ _ a₂notins _ =>
    have fa₁prop := (f ⟨↑a₁, a₁ins⟩).prop
    rw [fa₁a₂] at fa₁prop
    contradiction
  next a₁notins _ _ a₂ins _ =>
    have bint' := (f { val := ↑a₂, property := a₂ins }).prop
    rw [← fa₁a₂] at bint'
    contradiction
  next a₁notins _ _ a₂notins _ =>
    have a₁a := a₁.prop
    have a₂a := a₂.prop
    simp [a₁notins, a₂notins] at a₁a a₂a
    apply Subtype.ext
    simp [a₁a, a₂a]
  
  intros b'
  have b'prop := b'.prop
  simp [← bins] at b'prop
  rcases b'prop with b'prop|b'prop
  use ⟨a, Finset.mem_insert_self a s⟩
  simp
  rcases ains : (Finset.decidableMem a s) with h|h
  simp [← b'prop]
  contradiction
  have boysc := fbij.right ⟨↑b', b'prop⟩
  rcases boysc with ⟨a', fa'⟩
  have a'ins : ↑a' ∈ insert a s
  simp
  use ⟨a',a'ins⟩ 
  rcases (Finset.decidableMem ↑a' s) with h|_
  cases h a'.prop
  simp_all
  split <;> simp_all;simp_all

lemma floormagic : ∀ (n m : ℕ) (q : ℚ), q < 1 → ↑n ≤ ⌊(↑m + q)⌋  → n ≤ m := by
  intros n m q smallqat nlemfloor
  rw  [Int.floor_nat_add] at nlemfloor
  have qflrle0 : ⌊q⌋ ≤ 0
  by_contra qflrpos
  simp at qflrpos
  rw [Int.floor_pos] at qflrpos
  cases (lt_irrefl 1 (lt_of_le_of_lt qflrpos smallqat))
  have mqlem := Int.add_le_add_left qflrle0 ↑m
  have nleqm := Int.le_trans nlemfloor mqlem
  simp at nleqm
  exact nleqm

 lemma xor_even_le_implies_lt : ∀ {m n : ℕ}, Xor' (Even m) (Even n) → m ≤ n → m < n := by
  intros m n xoreven mlen
  cases' xoreven with hp hq
  rw [le_iff_lt_or_eq] at mlen
  cases' mlen with mltn meqn
  exact mltn
  simp [meqn] at hp
  rw [le_iff_lt_or_eq] at mlen
  cases' mlen with mltn meqn
  exact mltn
  simp [meqn] at hq
  --NOTE: try using <;> to reduce redundancy 
  -- rcases xoreven with xoreven |xoreven <;>{
  -- rw [le_iff_lt_or_eq] at mlen
  -- rcases mlen with mlen | mlen
  -- exact mlen 
  -- simp [mlen] at xoreven
  -- --rw [le_iff_lt_or_eq] at mlen
  -- cases xoreven
  -- }
lemma notc : ∀ {c x y : Fin 2}, x ≠ c → y ≠ c → x = y := by

  intros c x y _ _
  fin_cases c 
  all_goals{
    fin_cases x 
    try{tauto}
    fin_cases y 
    all_goals{
      tauto
    }
  }
  done

 

lemma not0_eq1: ∀ {x: Fin 2}, x ≠ 0 ↔ x = 1 := by
  intro 
  apply Iff.intro 
  · intro xneq0
    have _1_neq0 : (1 : Fin 2) ≠ 0 := by simp
    apply notc xneq0 _1_neq0
  · intro
    simp_all
  done

lemma missing_pigeonhole {α β : Type} [DecidableEq α] [LinearOrderedSemiring β] : ∀ {s : Finset α}, Finset.Nonempty s → ∀ {f g : α → β}, s.sum f ≤ s.sum g → ∃ a : α, a ∈ s ∧ f a ≤ g a := by
  
  intros s sne f g fgsum
  induction' s using Finset.induction with a t anotint ih
  rcases sne with ⟨sne_w, sne_h⟩ 
  cases sne_h
  rcases Finset.eq_empty_or_nonempty t with h|h
  simp [h] at fgsum ⊢
  assumption
  simp_all
  cases (le_or_lt (f a) (g a)) with 
  |inl fleg => simp [fleg]
  |inr gltf =>
    cases (le_or_lt (t.sum f) (t.sum g)) with 
    |inl tfleg => simp_all
    |inr tgltf => cases (not_le_of_lt (add_lt_add gltf tgltf) fgsum)

  

-- NOTE: Proof by simp
/- lemma halflt1 : mkRat 1 2 < 1 := by
  simp -/


lemma dblcnt (M' N': ℕ) (f : Sym2 (Fin (M'+ N').succ) → Fin 2): ∀ c : Fin 2, 2 * (Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = c) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset).card = (Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) ↦ f ⟦x.toProd⟧ = c) Finset.univ).card := by

  let r: Sym2 (Fin (M' + N').succ) → (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart → Prop := λ x y ↦ x = ⟦y.toProd⟧ ∨ x = ⟦y.toProd.swap⟧
  intro c
  let s := Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = c) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset
  let t := Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) ↦ f ⟦x.toProd⟧ = c) Finset.univ
  have hm : ∀ (a : Sym2 (Fin (M' + N').succ)), a ∈ s → (Finset.bipartiteAbove r t a).card = 2
  intros a ains
  rcases (Quotient.exists_rep a) with ⟨⟨fst,snd⟩, aprop⟩ 
  simp [SimpleGraph.mem_edgeSet, ← SimpleGraph.completeGraph_eq_top,completeGraph] at ains --NOTE: can be replace by simp_all
  simp [Finset.bipartiteAbove,Finset.card_eq_two]
  rcases ains with ⟨ains_left, ains_right⟩ 

  have aOutAdj : (⊤ : SimpleGraph (Fin (M' + N').succ)).Adj fst snd := by
    simp [← aprop] at ains_left
    simp [ains_left] 
  use SimpleGraph.Dart.mk (fst,snd) aOutAdj
  
  have aOutSwapAdj : (⊤ : SimpleGraph (Fin (M' + N').succ)).Adj snd fst := by 
    simp[aOutAdj]
    simp [Sym2.eq_swap, ←aprop] at ains_left
    intro ; simp_all
  use SimpleGraph.Dart.mk (snd,fst) aOutSwapAdj
  simp

  apply And.intro
  by_contra h
  simp[Prod.ext_iff] at h
  rcases h with ⟨h_left, _⟩ 
  simp[← aprop,h_left] at ains_left
  
  simp[Finset.Subset.antisymm_iff, Finset.subset_iff]
  apply And.intro
  intros x _ aeqx
  have swap : (snd, fst) = Prod.swap (fst, snd) := by simp
  simp [SimpleGraph.Dart.ext_iff]
  rw [swap, ← SimpleGraph.dart_edge_eq_mk'_iff]
  simp [aeqx, SimpleGraph.Dart.edge,aprop]

  simp_all
  have aeqswap : a = Quotient.mk (Sym2.Rel.setoid (Fin (Nat.succ (M' + N')))) (snd, fst) := by simp[← aprop]
  simp[aeqswap]
  simp[← aeqswap, ains_right] 
  
  have hn : ∀ (b : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart), b ∈ t → (Finset.bipartiteBelow r s b).card = 1
  intros b bint
  simp [Finset.bipartiteBelow, Finset.card_eq_one]
  simp[← SimpleGraph.completeGraph_eq_top, completeGraph] at bint
  use b.edge 
  simp[Finset.Subset.antisymm_iff, Finset.subset_iff, SimpleGraph.mem_edgeSet,←  SimpleGraph.completeGraph_eq_top, completeGraph]
  have toEdge : b.edge = ⟦b.toProd⟧ := by simp [SimpleGraph.dart_edge_eq_mk'_iff]
  apply And.intro
  intros x _ _ xeqb
  simp_all
  simp[Finset.filter] at bint
  simp[toEdge, bint]
  --NOTE: try avoid temp
  have temp := Finset.card_mul_eq_card_mul r hm hn
  simp[mul_one (t.card)] at temp
  simp[← temp,mul_comm]

-- NOTE: use Finset.univ_fin2
/- lemma univexpand : (@Finset.univ (Fin 2) _) = {0, 1} := by
  symm
  rw [Finset.eq_univ_iff_forall]
  intros
  fin_cases x; simp
 -/

lemma mkRat_one_den : ∀ (n : ℤ), (mkRat n 1).den = 1 := by intros; simp [mkRat, Rat.normalize]

lemma mkRat_one_num : ∀ (n : ℤ), (mkRat n 1).num = n := by intros; simp [mkRat, Rat.normalize]
