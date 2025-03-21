import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Rat.Floor
import Mathlib.LinearAlgebra.AffineSpace.Combination

open List

lemma bijection_of_eq_card {α β : Type} [DecidableEq α] [DecidableEq β] : ∀ {s : Finset α} {t : Finset β}, s.card = t.card → ((s = ∅ ∧ t = ∅) ∨ ∃ f : ↥s → ↥t, Function.Bijective f) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    simp
    intros t h
    left
    rw [← Finset.card_eq_zero]
    symm
    exact h
  -- NOTE: One requires the @ to refer to a and s which seems dumb, possibly a bug
  | @insert a s anotins ih =>
    intros t tcard
    right
    rw [(Finset.card_insert_of_not_mem anotins)] at tcard
    have tinsert := Eq.symm tcard
    rw [Finset.card_eq_succ] at tinsert
    rcases tinsert with ⟨b, t', bnotint', bins, tcards⟩
    rcases (ih (Eq.symm tcards)) with stempt | fbij
    simp [stempt.right] at bins
    rw [stempt.left, ← bins]
    have bobv : b ∈ t := by
      rw [← bins]
      exact Finset.mem_singleton_self b
    lift b to t using bobv
    rw [bins]
    use (λ _ : {y // y ∈ insert a ∅} ↦ b)
    apply And.intro
    · intros a₁ a₂ eq
      apply Subtype.ext
      have a₁prop := a₁.prop
      have a₂prop := a₂.prop
      simp only [Finset.mem_insert, Finset.not_mem_empty, or_false] at a₁prop a₂prop
      simp [a₁prop, a₂prop]
    · intros b'
      use ⟨a, Finset.mem_insert_self a ∅⟩
      have b'prop := b'.prop
      simp [← bins] at b'prop ⊢
      apply Subtype.ext
      simp [b'prop]
    have bint : b ∈ t := by rw [← bins] ; simp
    rcases fbij with ⟨f, fbij⟩
    have fhelper : ∀ x, ↑(f x) ∈ t := by
      intros
      simp [← bins]
    use (λ x ↦ match Finset.decidableMem ↑x s with
    | isTrue p => ⟨f ⟨↑x, p⟩, fhelper ⟨↑x, p⟩⟩
    | isFalse _ => ⟨b, bint⟩)
    apply And.intro
    · intros a₁ a₂ fa₁a₂
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
        simp only [Finset.mem_insert, a₁notins, a₂notins, or_false] at a₁a a₂a
        apply Subtype.ext
        simp [a₁a, a₂a]
    · intros b'
      have b'prop := b'.prop
      simp [← bins] at b'prop
      rcases b'prop with b'prop|b'prop
      use ⟨a, Finset.mem_insert_self a s⟩
      simp
      rcases ains : (Finset.decidableMem a s) with h|h
      simp [← b'prop]
      contradiction
      rcases (fbij.right ⟨↑b', b'prop⟩) with ⟨a', fa'⟩
      use ⟨a', by simp⟩
      rcases (Finset.decidableMem ↑a' s) with h | _
      · cases h a'.prop
      · simp
        split
        · simp [fa']
        · next _ anotins _ =>
            simp [Subtype.coe_mk] at anotins

lemma bijection_of_List_perm {α : Type} : ∀ {l₁ l₂ : List α}, l₁ ~ l₂ → ∃ (f : Fin l₁.length → Fin l₂.length), Function.Bijective f ∧ ∀ (i : Fin l₁.length), l₁.get i = l₂.get (f i) := by
  intro l₁ l₂ permProp
  induction permProp
  case nil =>
    simp
  case cons h l₁ l₂ _ ih =>
    rcases ih with ⟨f, fProp⟩
    haveI : NeZero (h :: l₁).length := by simp; infer_instance
    haveI : NeZero (h :: l₂).length := by simp; infer_instance
    use Fin.cases 0 (λ i ↦ (f i).succ)
    apply And.intro
    · unfold Function.Bijective
      apply And.intro
      · intros a b fab
        simp at fab
        cases Fin.eq_zero_or_eq_succ a with
        | inl i0 =>
          cases Fin.eq_zero_or_eq_succ b with
          | inl j0 => simp [i0, j0]
          | inr jsucc =>
            rcases jsucc with ⟨j', j'Val⟩
            simp [i0, j'Val] at fab
            cases (Fin.succ_ne_zero (f j')).symm fab
        | inr isucc =>
          cases Fin.eq_zero_or_eq_succ b with
          | inl j0 =>
            rcases isucc with ⟨i', i'Val⟩
            simp [j0, i'Val] at fab
            cases (Fin.succ_ne_zero (f i')) fab
          | inr jsucc =>
            rcases isucc with ⟨i', i'Val⟩
            rcases jsucc with ⟨j', j'Val⟩
            simp [i'Val, j'Val] at fab
            have ijeq := fProp.left.left fab
            rw [ijeq] at i'Val
            simp [i'Val, j'Val]
      · intros a
        cases Fin.eq_zero_or_eq_succ a with
        | inl a0 =>
          use 0
          simp [a0]
        | inr asucc =>
          rcases asucc with ⟨a', a'Val⟩
          rcases (fProp.left.right a') with ⟨b, bProp⟩
          use b.succ
          simp [a'Val]
          exact bProp
    · intro i
      cases Fin.eq_zero_or_eq_succ i with
      | inl i0 => simp [i0]
      | inr isucc =>
        rcases isucc with ⟨j, jVal⟩
        simp [jVal]
        exact fProp.right j
  case swap x y l =>
    haveI : NeZero (x :: y :: l).length := by simp; infer_instance
    haveI : NeZero (y :: x :: l).length := by simp; infer_instance
    use Fin.cases 1 (Fin.cases 0 (λ i => i.succ.succ))
    apply And.intro
    · apply And.intro
      · intro a b fab
        simp at fab
        cases Fin.eq_zero_or_eq_succ a with
        | inl i0 =>
          cases Fin.eq_zero_or_eq_succ b with
          | inl j0 => simp [i0, j0]
          | inr jsucc =>
            rcases jsucc with ⟨j', j'Val⟩
            simp [i0, j'Val] at fab
            cases Fin.eq_zero_or_eq_succ j' with
            | inl j'0 => simp [j'0] at fab
            | inr j'succ =>
              rcases j'succ with ⟨j'', j''Val⟩
              rw [j''Val, ← Fin.succ_zero_eq_one, Fin.cases_succ, Fin.succ_inj] at fab
              cases (Fin.succ_ne_zero j'') fab.symm
        | inr isucc =>
          cases Fin.eq_zero_or_eq_succ b with
          | inl j0 =>
            rcases isucc with ⟨i', i'Val⟩
            simp [j0, i'Val] at fab
            cases Fin.eq_zero_or_eq_succ i' with
            | inl i''0 => simp [i''0] at fab
            | inr i'succ =>
              rcases i'succ with ⟨i'', i''Val⟩
              simp [i''Val] at fab
              rw [← Fin.succ_zero_eq_one, Fin.succ_inj] at fab
              cases (Fin.succ_ne_zero i'') fab
          | inr jsucc =>
            rcases isucc with ⟨i', i'Val⟩
            rcases jsucc with ⟨j', j'Val⟩
            simp [i'Val, j'Val] at fab
            cases Fin.eq_zero_or_eq_succ i' with
            | inl i'0 =>
              cases Fin.eq_zero_or_eq_succ j' with
              | inl j'0 =>
                simp [i'Val, j'Val, i'0, j'0]
              | inr j'succ =>
                rcases j'succ with ⟨j'', j''Val⟩
                simp [i'0, j''Val] at fab
                cases (Fin.succ_ne_zero j''.succ).symm fab
            | inr i'succ =>
              cases Fin.eq_zero_or_eq_succ j' with
              | inl j'0 =>
                rcases i'succ with ⟨i'', i''Val⟩
                simp [i''Val, j'0] at fab
                cases (Fin.succ_ne_zero i''.succ) fab
              | inr j'succ =>
                rcases i'succ with ⟨i'', i''Val⟩
                rcases j'succ with ⟨j'', j''Val⟩
                simp [i''Val, j''Val] at fab
                simp [i'Val, j'Val, i''Val, j''Val, fab]
      · intros a
        cases Fin.eq_zero_or_eq_succ a with
        | inl a0 =>
          use 1
          simp [a0]
          rw [← Fin.succ_zero_eq_one, Fin.cases_succ]
          simp
        | inr asucc =>
          rcases asucc with ⟨a', a'Val⟩
          cases Fin.eq_zero_or_eq_succ a' with
          | inl a'0 =>
            use 0
            simp [a'Val, a'0]
          | inr a'succ =>
            rcases a'succ with ⟨a'', a''Val⟩
            use a''.succ.succ
            simp [a'Val, a''Val]
    · intro i
      cases Fin.eq_zero_or_eq_succ i with
      | inl i0 => simp [i0]
      | inr isucc =>
        rcases isucc with ⟨j, jVal⟩
        cases Fin.eq_zero_or_eq_succ j with
        | inl j0 => simp [jVal]
                    simp [j0]
        | inr jsucc =>
          rcases jsucc with ⟨k, kVal⟩
          simp [jVal, kVal]
  case trans l₁ l₂ l₃ _ _ ih₁ ih₂ =>
    rcases ih₁ with ⟨f₁, f₁Prop⟩
    rcases ih₂ with ⟨f₂, f₂Prop⟩
    use f₂ ∘ f₁
    apply And.intro
    · apply And.intro
      · intros a b fab
        exact f₁Prop.left.left (f₂Prop.left.left fab)
      · intro a
        rcases f₂Prop.left.right a with ⟨b, bProp⟩
        rcases f₁Prop.left.right b with ⟨c, cProp⟩
        use c
        simp [bProp, cProp]
    · intro i
      simp
      trans (l₂.get (f₁ i))
      · exact f₁Prop.right i
      · exact f₂Prop.right (f₁ i)

lemma xor_even_le_implies_lt : ∀ {m n : ℕ}, Xor' (Even m) (Even n) → m ≤ n → m < n := by
  intros m n xoreven mlen
  rw [le_iff_lt_or_eq] at mlen
  · cases mlen with
    | inl mltn => exact mltn
    | inr meqn=>
      simp [meqn] at xoreven

lemma dblcnt (M' N': ℕ) (f : Sym2 (Fin (M'+ N').succ) → Fin 2): ∀ c : Fin 2, 2 * (Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = c) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset).card = (Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) ↦ f (Sym2.mk x.toProd) = c) Finset.univ).card := by

  let r: Sym2 (Fin (M' + N').succ) → (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart → Prop := λ x y ↦ x = Sym2.mk y.toProd ∨ x = Sym2.mk y.toProd.swap
  intro c
  let s := Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = c) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset
  let t := Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) ↦ f (Sym2.mk x.toProd) = c) Finset.univ
  have hm : ∀ (a : Sym2 (Fin (M' + N').succ)), a ∈ s → (Finset.bipartiteAbove r t a).card = 2 := by
    intros a ains
    rcases (Quot.exists_rep a) with ⟨⟨fst,snd⟩, aprop⟩
    simp[SimpleGraph.mem_edgeSet] at ains
    --simp [SimpleGraph.mem_edgeSet, ← SimpleGraph.completeGraph_eq_top,completeGraph] at ains --NOTE: can be replace by simp_all
    simp [Finset.bipartiteAbove, Finset.card_eq_two]
    simp [s] at ains
    rcases ains with ⟨ains_left, ains_right⟩
    have aOutAdj : (⊤ : SimpleGraph (Fin (M' + N').succ)).Adj fst snd := by
      simp [← aprop] at ains_left
      simp [ains_left]
    use SimpleGraph.Dart.mk (fst,snd) aOutAdj
    have aOutSwapAdj : (⊤ : SimpleGraph (Fin (M' + N').succ)).Adj snd fst := by
      simp[aOutAdj]
      simp [Sym2.eq_swap, ←aprop] at ains_left
      intro
      simp_all
    use SimpleGraph.Dart.mk (snd,fst) aOutSwapAdj
    simp
    apply And.intro
    · intro fseq
      simp at aOutAdj
      contradiction
    · simp[Finset.Subset.antisymm_iff, Finset.subset_iff]
      apply And.intro
      · intros x _ aeqx
        have swap : (snd, fst) = Prod.swap (fst, snd) := by simp
        simp [SimpleGraph.Dart.ext_iff]
        rw [swap, ← SimpleGraph.dart_edge_eq_mk'_iff]
        simp [r] at aeqx
        simp [aeqx, SimpleGraph.Dart.edge,aprop]
      · simp [r, t]
        have aeqswap : a = s(snd, fst) := by simp[← aprop] --used to be Quotient.mk (Sym2.Rel.setoid (Fin (Nat.succ (M' + N')))) (snd, fst)
        change s(fst, snd) = a at aprop
        simp [← aeqswap, aprop]
        assumption
  have hn : ∀ (b : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart), b ∈ t → (Finset.bipartiteBelow r s b).card = 1 := by
    intros b bint
    simp [Finset.bipartiteBelow, Finset.card_eq_one]
    simp[SimpleGraph.mem_edgeSet] at bint
    -- simp[← SimpleGraph.completeGraph_eq_top, completeGraph] at bint
    use b.edge
    simp[Finset.Subset.antisymm_iff, Finset.subset_iff, SimpleGraph.mem_edgeSet]
    have toEdge : b.edge = Sym2.mk b.toProd := by simp [SimpleGraph.dart_edge_eq_mk'_iff]
    apply And.intro
    · intros
      simp_all [r]
    · have btop := b.adj
      simp [t] at bint
      simp [s, r, toEdge, bint, btop]
   --NOTE: try avoid temp
  have temp := Finset.card_mul_eq_card_mul r hm hn
  simp [s, r, t, mul_one (t.card)] at temp
  simp [← temp, SimpleGraph.edgeFinset, mul_comm]

namespace Rat

lemma mkRat_one_num : ∀ (z : ℤ), (mkRat z 1).num = z := by intros; simp [mkRat, Rat.normalize]

lemma mkRat_one_den : ∀ (z : ℤ), (mkRat z 1).den = 1 := by intros; simp [mkRat, Rat.normalize]

lemma mkRat_num_one : ∀ (n : ℕ), (mkRat 1 n.succ).num = 1 := by intros; simp [mkRat, Rat.normalize]

lemma mkRat_den_one : ∀ (n : ℕ), (mkRat 1 n.succ).den = n.succ := by intros; simp [mkRat, Rat.normalize]

end Rat

namespace Finset

/-- A finite partition of `a : Finset α` is a pairwise disjoint finite set of elements whose supremum is `a`. -/
@[ext]
structure FinpartitionWithEmpty {α : Type} [DecidableEq α] (a : Finset α) where
  /-- The elements of the finite partition of `a` -/
  parts : Finset (Finset α)
  /-- The parts are pairwise disjoint -/
  pwDisj : Set.PairwiseDisjoint ↑parts (@id (Finset α))
  /-- The supremum of the partition is `a` -/
  supParts : parts.sup id = a
  -- deriving DecidableEq

open BigOperators

namespace FinpartitionWithEmpty

variable {α : Type} [DecidableEq α] {a : Finset α} {P : FinpartitionWithEmpty a}

theorem biUnion_parts : P.parts.biUnion id = a :=
  (sup_eq_biUnion _ _).symm.trans P.supParts

theorem sum_card_parts_with_empty (P : FinpartitionWithEmpty a) : ∑ i ∈ P.parts, Finset.card i = a.card := by
  convert congr_arg Finset.card P.biUnion_parts
  rw [card_biUnion P.pwDisj]
  rfl

end FinpartitionWithEmpty

theorem sum_image_vanishing {β : Type u} {α : Type v} {γ : Type w} {f : α → β} [AddCommMonoid β] [DecidableEq α] [DecidableEq γ] {s : Finset γ} {g : γ → α} : (∀ x ∈ s, ∀ y ∈ s, g x = g y → f (g x) ≠ 0 → x = y) → (s.image g).sum (λ x ↦ f x) = s.sum (f ∘ g) := by
  induction s using Finset.induction with
  | empty => simp
  | insert anotins ih =>
    next a s' =>
      intro aProp
      simp [Finset.sum_insert anotins]
      by_cases h:(g a) ∈ s'.image g
      · rw [Finset.insert_eq_of_mem h]
        simp at h
        rcases h with ⟨b, bins', gaeqgb⟩
        have bProp := aProp b
        simp [bins'] at bProp
        rcases bProp with ⟨gbProp, _⟩
        by_cases h:f (g b) = 0
        · rw [gaeqgb] at h
          simp [h]
          apply ih
          intros x xins' y yins' gxy fgx
          apply aProp <;> try { assumption } <;> { simp; right; assumption }
        · rw [gbProp gaeqgb h] at bins'
          contradiction
      · simp [Finset.sum_insert h]
        rw [ih]
        · simp
        · intros x xins' y yins'
          exact aProp x (Finset.mem_insert_of_mem xins') y (Finset.mem_insert_of_mem yins')

end Finset

namespace Fin

lemma univ_disjUnion_zero_succ : ∀ (n : ℕ), (Finset.univ : Finset (Fin n.succ)) = Finset.disjUnion {0} (Finset.univ.map (Fin.succEmb n)) (by simp) := by
  simp [Finset.ext_iff]
  intro n
  apply Fin.cases <;> simp [Fin.succ_ne_zero]

end Fin

lemma vector_list_finset_sum : ∀ {n : ℕ} (V : List.Vector ℕ n), Finset.sum Finset.univ (λ x ↦ ↑(V.get x) : (Fin n) → ℚ) = sum (map Nat.cast V.toList) := by
  intro n
  induction n with
  | zero => simp
  | succ k' ih =>
    intro V
    rw [← Vector.cons_head_tail V, Fin.univ_disjUnion_zero_succ, Finset.sum_disjUnion]
    simp [-Vector.cons_head_tail]
    have ihv := ih V.tail
    simp at ihv
    exact ihv
