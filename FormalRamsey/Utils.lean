import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.DoubleCounting
import Mathlib.Data.Rat.Floor 
import Mathlib.Algebra.Parity

import Init.Tactics
import Mathlib.Tactic
import Mathlib.Mathport.Syntax

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
  use (λ x : {y // y ∈ insert a ∅} ↦ b)
  apply And.intro
  intros a₁ a₂ fa₁a₂
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
  have bint : b ∈ t := by rw [← bins] <;> simp
  rcases fbij with ⟨f, fbij⟩
  have fhelper : ∀ x, ↑(f x) ∈ t
  intros
  simp [← bins]
  use (λ x ↦ match Finset.decidableMem ↑x s with
  | isTrue p => ⟨f ⟨↑x, p⟩, fhelper ⟨↑x, p⟩⟩
  | isFalse _ => ⟨b, bint⟩)
  -- split
  -- intros _ _ fa₁a₂
  -- simp at fa₁a₂
  -- rcases (Finset.decidable_mem ↑a₁ s) with  ⟨a₁notins, a₁ins⟩ <;> rcases (Finset.decidable_mem ↑a₂ s) with ⟨a₂notins, a₂ins⟩ <;> simp at fa₁a₂
  -- have a₁a := a₁.prop
  -- have a₂a := a₂.prop
  -- simp [a₁notins, a₂notins] at a₁a a₂a
  -- apply Subtype.ext
  -- simp [a₁a, a₂a]
  -- have fa₂prop := (f ⟨↑a₂, a₂ins⟩).prop
  -- rw [← fa₁a₂] at fa₂prop
  -- contradiction
  -- have fa₁prop := (f ⟨↑a₁, a₁ins⟩).prop
  -- rw [fa₁a₂] at fa₁prop
  -- contradiction
  -- have japf := fbij.left (Subtype.ext fa₁a₂)
  -- simp at japf
  -- apply Subtype.ext
  -- assumption
  -- intros b'
  -- have b'prop := b'.prop
  -- simp [← bins] at b'prop
  -- cases b'prop
  -- use a
  -- simp
  -- simp
  -- cases ains : (Finset.decidable_mem a s)
  -- simp [← b'prop]
  -- contradiction
  -- have boysc := fbij.right ⟨↑b', b'prop⟩
  -- rcases boysc with ⟨a', fa'⟩
  -- use a'
  -- simp
  -- simp
  -- cases (Finset.decidable_mem ↑a' s)
  -- cases h a'.prop
  -- simp [fa']

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

  intros c x y h₁ h₂
  fin_cases c 

  fin_cases x 
  contradiction
  fin_cases y 
  contradiction
  simp

  simp_all
  fin_cases x 
  simp_all
  fin_cases y 
  simp_all
  contradiction
  simp
  contradiction

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
  simp [SimpleGraph.mem_edgeSet, ← SimpleGraph.completeGraph_eq_top,completeGraph] at ains --NOTE: can be replace by simp_all
  simp [Finset.bipartiteAbove,Finset.card_eq_two]
  rcases ains with ⟨ains_left, ains_right⟩ 

  have aOutAdj : (⊤ : SimpleGraph (Fin (M' + N').succ)).Adj (Quot.out a).1 (Quot.out a).2 := by
    --NOTE : try avoid the temp
    have temp : a = ⟦(a.out.1, a.out.2)⟧ := by simp
    rw [temp] at ains_left
    exact ains_left 
  use SimpleGraph.Dart.mk a.out aOutAdj
  
  have aOutSwapAdj : (⊤ : SimpleGraph (Fin (M' + N').succ)).Adj (Quot.out a).swap.1 (Quot.out a).swap.2 := by 
    --NOTE : try avoid the temp
    have temp : a = ⟦(a.out.2, a.out.1)⟧ := by 
      rw[ Sym2.eq_swap] 
      simp
    rw [temp] at ains_left
    exact ains_left

  use SimpleGraph.Dart.mk a.out.swap aOutSwapAdj
  simp

  apply And.intro
  by_contra h
  simp[Prod.ext_iff] at h
  rcases h with ⟨h_left, h_right⟩ 
  --NOTE : try avoid the temp
  have temp : a = ⟦(a.out.1, a.out.2)⟧ := by simp
  rw [temp] at ains_left
  simp[h_left] at ains_left

  simp[Finset.Subset.antisymm_iff, Finset.subset_iff]
  apply And.intro
  intros x _ aeqx
  sorry
  -- have h : (x.toProd.1, x.toProd.2) = ⟦(x.toProd.1, x.toProd.2)⟧.out
  -- ∨ (x.toProd.2, x.toProd.1) = ⟦(x.toProd.1, x.toProd.2)⟧.out := by
  --   simp [Quotient.mk_eq_iff_out, Quotient.mk_out (x.toProd.1, x.toProd.2)]
  

  -- simp at h
  -- cases h 
  -- --|refl =>
  --   left
  --   apply SimpleGraph.Dart.ext
  --   simp[aeqx]
  --   have temp: x.toProd = (x.toProd.1, x.toProd.2) := by simp
  --   rw[temp]
  --   exact cases_eq
  -- right
  -- apply SimpleGraph.Dart.ext
  -- simp[aeqx]
  -- have temp: x.toProd = (x.toProd.2, x.toProd.1).swap := by simp[prod.swap_prod_mk],
  -- rw[temp,prod.swap_inj],
  -- rw[← temp],
  -- simp[cases_eq],

  exact ains_right

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
