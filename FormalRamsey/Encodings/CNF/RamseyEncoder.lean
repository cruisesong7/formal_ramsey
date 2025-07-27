import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Sort
-- NOTE: This was renamed later to Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fin

import Trestle

namespace Fin

-- NOTE: Imported from the future (mathlib v4.18.0)
@[simp]
theorem castLE_le_castLE_iff {i j : Fin n} (h : n ≤ m) : i.castLE h ≤ j.castLE h ↔ i ≤ j := .rfl

-- NOTE: Imported from the future (mathlib v4.20.0-rc1)
@[simp]
theorem cast_castLE {k m n} (km : k ≤ m) (mn : m = n) (i : Fin k) :
    Fin.cast mn (i.castLE km) = i.castLE (mn ▸ km) :=
  Fin.ext (by simp)

end Fin

namespace List

def all_pairs {α : Type} : (l : List α) → List (α × α)
| [] => []
| h :: t => t.map (h, ·) ++ (all_pairs t)

def mem_of_mem_all_pairs {α : Type} {l : List α} {p : α × α} (h : p ∈ l.all_pairs) : p.fst ∈ l ∧ p.snd ∈ l := by
  induction l with
  | nil => simp [all_pairs] at h
  | cons x l' ih =>
    simp [all_pairs] at h
    cases h with
    | inl h' =>
      obtain ⟨y, ⟨ymem, pxy⟩⟩ := h'
      simp [← pxy]
      tauto
    | inr h' => tauto

lemma all_pairs_sorted_of_sorted {α : Type} {l : List α} {R : α → α → Prop} (h : l.Sorted R) : ∀ p ∈ l.all_pairs, R p.fst p.snd := by
  induction l with
  | nil => simp [all_pairs]
  | cons x l' ih =>
    simp [all_pairs] at h ⊢
    intros a b h'
    cases h' with
    | inl yprop =>
      simp [← yprop.right]
      exact h.left _ yprop.left
    | inr abmem => exact (ih h.right) _ abmem

lemma all_pairs_neq_of_nodup {α : Type} {l : List α} (lnodup : l.Nodup) : ∀ p ∈ l.all_pairs, p.fst ≠ p.snd := all_pairs_sorted_of_sorted lnodup

lemma mem_all_pairs_iff_of_irrefl_of_antisymm_of_sorted {α : Type} {l : List α} {R : α → α → Prop} [Rirrefl : IsIrrefl α R] [Ranti : IsAntisymm α R] (lsorted : l.Sorted R) : ∀ p, p ∈ l.all_pairs ↔ R p.fst p.snd ∧ (p.fst ∈ l ∧ p.snd ∈ l) := by
  intro p
  apply Iff.intro
  · intro pmem
    simp [all_pairs_sorted_of_sorted lsorted _ pmem, mem_of_mem_all_pairs pmem]
  · induction l with
    | nil => simp [all_pairs]
    | cons h t ih =>
      simp [all_pairs]
      intros Rp1p2 p1mem p2mem
      cases p1mem with
      | inl p1h =>
        left
        use p.2
        cases p2mem with
        | inl p2h =>
          simp [p1h, p2h] at Rp1p2
          cases Rirrefl.irrefl _ Rp1p2
        | inr p2int =>
          simp [p2int, ← p1h]
      | inr p1int =>
        simp at lsorted
        cases p2mem with
        | inl p2h =>
          have Rp2p1 := lsorted.left _ p1int
          simp [← p2h] at Rp2p1
          simp [Ranti.antisymm _ _ Rp1p2 Rp2p1] at Rp1p2
          cases Rirrefl.irrefl _ Rp1p2
        | inr _ =>
          right
          apply ih <;> tauto

namespace Sorted

lemma antisymm_is_le_sorted_of_nodup_of_sorted {α : Type} {l : List α} {R : α → α → Prop} [Ranti : IsAntisymm α R] (hnodup: l.Nodup) (hsorted : l.Sorted R) {a b : Fin l.length} (hab : R l[a] l[b]) : a ≤ b := by
  induction hsorted with
  | nil => apply Fin.elim0 a
  | cons hR tsorted ih =>
    next xh xt =>
      cases Fin.eq_zero_or_eq_succ a with
      | inl a0 =>
        simp [a0]
      | inr asucc =>
        obtain ⟨a', a'succ⟩ := asucc
        cases Fin.eq_zero_or_eq_succ b with
        | inl b0 =>
          simp [a'succ, b0] at hab
          have hba := hR xt[a']
          simp at hba hnodup
          have aeqb := Ranti.antisymm _ _ hab hba
          simp [← aeqb] at hnodup
        | inr bsucc =>
          obtain ⟨b', b'succ⟩ := bsucc
          simp at hnodup
          simp [a'succ, b'succ] at hab ⊢
          exact ih hnodup.right hab

end Sorted

namespace Sublist

lemma sorted {α : Type} {l l' : List α} {R : α → α → Prop} (sub : l'.Sublist l) : l.Sorted R → l'.Sorted R := by
  induction sub with
  | slnil => simp
  | cons h₁ sub' ih =>
    simp
    intros _ Sl₂
    exact ih Sl₂
  | cons₂ h₁ sub' ih =>
    simp
    intros Rl₂ Sl₂
    apply And.intro
    · intros b bmem
      exact Rl₂ _ (sub'.mem bmem)
    · exact ih Sl₂

end Sublist

end List

-- TODO: Probably move to Utils.lean
namespace SimpleGraph

lemma exists_isNClique_of_le_cliqueNum {α : Type} [Fintype α] {n : ℕ} {G : SimpleGraph α} (h : n ≤ G.cliqueNum) : ∃ S : Finset α, G.IsNClique n S := by
  rcases G.exists_isNClique_cliqueNum with ⟨s, sclique⟩
  have nlescard : n ≤ s.card := by simp [h, sclique.card_eq]
  obtain ⟨t, tprop⟩ := s.exists_subset_card_eq nlescard
  use t
  simp [← tprop.right, isNClique_iff]
  exact sclique.isClique.subset tprop.left

lemma cliqueNum_lt_iff_cliqueFree {α : Type} [Fintype α] {G : SimpleGraph α} {n : ℕ} : G.cliqueNum < n ↔ G.CliqueFree n := by
  apply Iff.intro
  · rintro Gcn S ⟨SIsClique, Scard⟩
    have absurd := SIsClique.card_le_cliqueNum
    rw [Scard] at absurd
    cases (Nat.not_le_of_lt Gcn) absurd
  · intro Gcf
    cases Nat.decLt G.cliqueNum n with
    | isTrue _ => assumption
    | isFalse nleGcn =>
      simp at nleGcn
      obtain ⟨S, SIsNClique⟩ := exists_isNClique_of_le_cliqueNum nleGcn
      cases Gcf S SIsNClique

end SimpleGraph

open Trestle Encode VEncCNF

lemma triangular_monotone : Monotone (λ N : ℕ ↦ N * (N - 1) / 2) := by
  intros a b aleqb
  simp
  cases a with
  | zero => simp
  | succ a' =>
    cases b with
    | zero =>
      simp at aleqb
    | succ b' =>
      simp
      obtain ⟨a'', aprop⟩ := Nat.even_or_odd' a'
      obtain ⟨b'', bprop⟩ := Nat.even_or_odd' b'
      cases aprop with
      | inl aeven =>
        cases bprop with
        | inl beven =>
          simp [aeven, beven, ← Nat.mul_assoc] at aleqb ⊢
          rw [Nat.mul_comm _ 2, Nat.mul_comm _ 2, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by simp), Nat.mul_div_cancel_left _ (by simp)]
          nlinarith
        | inr bodd =>
          simp [aeven, bodd, ← Nat.mul_assoc] at aleqb ⊢
          conv =>
            rhs
            left
            left
            change 2 * (b'' + 1)
          rw [Nat.mul_assoc 2, Nat.mul_div_cancel_left _ (by simp)]
          rw [Nat.mul_comm _ 2, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by simp)]
          nlinarith
      | inr aodd =>
        cases bprop with
        | inl beven =>
          simp [aodd, beven, ← Nat.mul_assoc] at aleqb ⊢
          conv =>
            lhs
            left
            left
            change 2 * (a'' + 1)
          rw [Nat.mul_assoc 2, Nat.mul_div_cancel_left _ (by simp)]
          rw [Nat.mul_comm _ 2, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by simp)]
          nlinarith
        | inr bodd =>
          simp [aodd, bodd, ← Nat.mul_assoc] at aleqb ⊢
          conv =>
            lhs
            left
            left
            change 2 * (a'' + 1)
          conv =>
            rhs
            left
            left
            change 2 * (b'' + 1)
          simp [Nat.mul_assoc 2, Nat.mul_div_cancel_left _ (by simp : 0 < 2)]
          nlinarith

lemma triangular_next : ∀ (n : ℕ), n * (n - 1) / 2 + n = (n + 1) * n / 2 := by
  intros n
  cases n with
  | zero => simp +arith
  | succ n' =>
    obtain ⟨m, nprop⟩ := Nat.even_or_odd' n'
    cases nprop with
    | inl neven =>
      simp [neven]
      conv =>
        rhs
        left
        left
        change 2 * (m + 1)
      rw [Nat.mul_comm _ (2 * m), Nat.mul_assoc 2, Nat.mul_assoc 2]
      simp
      nlinarith
    | inr nodd =>
      simp [nodd]
      conv =>
        rhs
        left
        right
        change 2 * (m + 1)
      conv =>
        lhs
        left
        left
        left
        change 2 * (m + 1)
      rw [Nat.mul_assoc 2, Nat.mul_comm _ (2 * (m + 1)), Nat.mul_assoc 2]
      simp
      nlinarith

structure EdgeVar (N : ℕ) where
  i : Fin N
  j : Fin N
  ijord : i > j

def decoder {N : ℕ} (idx : Fin (N * (N - 1) / 2)) : EdgeVar N :=
match N with
| Nat.zero => Fin.elim0 idx
| Nat.succ M =>
  match Nat.decLt idx.val (M * (M - 1) / 2) with
  | isTrue idxub =>
    let f := (λ i ↦ Fin.castLT i (Nat.lt_trans i.prop (Nat.lt_of_succ_le (Nat.le_refl M.succ))))
    let e := (decoder ⟨idx.val, idxub⟩);
    { i := f e.i, j := f e.j, ijord := by simp [f, e, Fin.castLT, e.ijord] }
  | isFalse idxlb =>
    { i := ⟨M, by simp⟩, j:= ⟨idx.val - M * (M - 1) / 2, by rw [Nat.sub_lt_iff_lt_add (Nat.le_of_not_lt idxlb)]; have idxub := idx.prop; simp [← Nat.add_assoc, triangular_next, -Fin.is_lt] at idxub ⊢; apply Nat.lt_add_right _ idxub⟩, ijord := by simp [Nat.sub_lt_iff_lt_add (Nat.le_of_not_lt idxlb), triangular_next] }

#eval decoder ⟨9, (by simp : 9 < (6 * (6 - 1) / 2))⟩

instance : ∀ N, IndexType (EdgeVar N) := by
  intro N
  use N * (N - 1) / 2
  · intro v
    use v.i.val * (v.i.val - 1) / 2 + v.j.val
    apply Nat.lt_of_lt_of_le (Nat.add_lt_add_left v.ijord.lt (v.i.val * (v.i.val - 1) / 2))
    simp [triangular_next]
    have tm := triangular_monotone (v.i.prop)
    simp at tm
    exact tm
  · use decoder

instance : ∀ N, LawfulIndexType (EdgeVar N) := by
  intro N
  induction N with
  | zero =>
    constructor <;> simp [IndexType.fromFin, IndexType.toFin]
    · intro v
      apply Fin.elim0 v.i
    · intro idx
      simp [IndexType.card] at idx
      apply Fin.elim0 idx
  | succ M ih =>
    constructor <;> simp [IndexType.fromFin, IndexType.toFin]
    · intros v
      unfold decoder
      simp
      split
      next idxub _ =>
        have li := ih.leftInv { i := ⟨v.i.val, by simp at idxub; cases Nat.decLt v.i M with | isTrue _ => assumption | isFalse vileM => simp at vileM; have tm := triangular_monotone vileM; simp at tm; have absurd := Nat.not_lt_of_le (Nat.le_trans tm (Nat.le_add_right _ v.j.val)); contradiction⟩, j := ⟨v.j.val, by trans v.i.val; exact v.ijord; simp at idxub; cases Nat.decLt v.i M with | isTrue _ => assumption | isFalse vileM => simp at vileM; have tm := triangular_monotone vileM; simp at tm; have absurd := Nat.not_lt_of_le (Nat.le_trans tm (Nat.le_add_right _ v.j.val)); contradiction⟩, ijord := v.ijord }
        simp only [IndexType.fromFin, IndexType.toFin] at li
        simp [li]
      next idxlb _ =>
        cases Nat.decLt v.i.val M with
        | isTrue viltM =>
          simp at idxlb
          have tn := Nat.lt_of_le_of_lt idxlb (Nat.add_lt_add_left v.ijord _)
          simp [triangular_next] at tn
          have tm := triangular_monotone viltM
          simp at tm
          have absurd := Nat.lt_of_le_of_lt tm tn
          simp at absurd
        | isFalse Mlevi =>
          simp at Mlevi
          have vieqM := Nat.le_antisymm Mlevi (Nat.le_of_lt_add_one v.i.prop)
          congr
          simp [← vieqM]
    · intros u
      simp [decoder]
      apply Fin.ext
      simp
      split
      next idxub _ =>
        simp
        have deceq := ih.rightInv ⟨u.val, idxub⟩
        simp only [IndexType.fromFin, IndexType.toFin] at deceq
        rw [Fin.ext_iff] at deceq
        simp at deceq
        assumption
      next idxlb _ =>
        simp at idxlb ⊢
        simp [← Nat.add_sub_assoc idxlb]

open Model

def assignment_to_graph {N : ℕ} (τ : PropAssignment (EdgeVar N)) (polarity : Bool) : SimpleGraph (Fin N) := { Adj := (λ i j ↦ match instDecidableEqFin N j i with | isTrue _ => False | isFalse ineqj => (τ (EdgeVar.mk (max i j) (min i j) (by simpa)) = polarity)), loopless := by simp [Irreflexive]; intros i imatch; split at imatch; simp_all; have := Eq.refl i; contradiction, symm := by simp [Symmetric, min_comm, max_comm]; aesop }

lemma assignment_to_graph_compl : ∀ {N : ℕ} (τ : PropAssignment (EdgeVar N)) (p : Bool), assignment_to_graph τ p = (assignment_to_graph τ !p)ᶜ := by
  simp [-Bool.forall_bool, assignment_to_graph]
  intros
  ext u v
  simp
  apply Iff.intro
  · intro Gedge
    split at Gedge
    next =>
      cases Gedge
    next =>
      simp [Gedge]
      intro ueqv
      symm at ueqv
      contradiction
  · rintro ⟨uneqv, Gedge⟩
    split at Gedge
    next =>
      simp_all
    next =>
      simp at Gedge
      assumption

-- NOTE: In the original version there was no need to annotate the p parameter in the pmap inside the for_all
def CliqueFreeEncoding (N x : ℕ) (polarity : Bool) : VEncCNF (EdgeVar N.succ) Unit (λ τ ↦ (assignment_to_graph τ polarity).CliqueFree x) :=
  seq[
    for_all (@((List.finRange N.succ).sublistsLen x).pmap _ _ (λ l ↦ l.Sorted instLTFin.lt) (λ clique (cliquesorted : clique.Sorted instLTFin.lt) ↦ clique.all_pairs.pmap (λ p psorted ↦ (match polarity with | true => Literal.neg | false => Literal.pos) { i := p.snd, j := p.fst, ijord := psorted }) (List.all_pairs_sorted_of_sorted cliquesorted)) (by simp; intros l lsub _; apply List.Pairwise.sublist lsub; simp [List.Sorted, List.finRange, Fin.pos_iff_ne_zero])).toArray (λ clique ↦ addClause clique.toArray)
  ]
  |>.mapProp (by
    ext τ
    simp only [Clause.satisfies_iff, LitVar.satisfies_iff]
    apply Iff.intro
    · intro τmodels
      simp only [SimpleGraph.CliqueFree]
      rintro X ⟨XClique, Xcard⟩
      have xsublx : (X.sort instLEFin.le).all_pairs.pmap (λ p psorted ↦ (match polarity with | true => Literal.neg | false => Literal.pos) ({ i := p.snd, j := p.fst, ijord := psorted } : EdgeVar N.succ)) (by simp; intros u v uvpair; have uvsorted := (List.all_pairs_sorted_of_sorted (X.sort_sorted instLEFin.le)) _ uvpair; have uvneq := (List.all_pairs_neq_of_nodup (X.sort_nodup instLEFin.le)) _ uvpair; simp at uvsorted uvneq; cases Fin.lt_or_eq_of_le uvsorted with | inl _ => assumption | inr _ => contradiction) ∈ (((List.finRange N.succ).sublistsLen x).pmap (λ clique cliquesorted ↦ clique.all_pairs.pmap (λ p psorted ↦ (match polarity with | true => Literal.neg | false => Literal.pos) { i := p.snd, j := p.fst, ijord := psorted }) (List.all_pairs_sorted_of_sorted cliquesorted)) (by simp; intros l lsub _; apply List.Pairwise.sublist lsub; simp [List.Sorted, List.finRange, Fin.pos_iff_ne_zero])).toArray := by
        simp
        use (X.sort instLEFin.le)
        simp [Xcard, List.sublist_iff_exists_fin_orderEmbedding_get_eq]
        let idxMap : Fin (X.sort instLEFin.le).length → Fin (List.finRange N.succ).length := (λ idx ↦ Fin.castLE (by simp) ((X.sort instLEFin.le).get idx))
        have idxMapInj : Function.Injective idxMap := by simp [Function.Injective, idxMap, List.Nodup.getElem_inj_iff (Finset.sort_nodup instLEFin.le X), Fin.val_inj]
        have idxOrdered : ∀ {a₁ a₂ : Fin (X.sort instLEFin.le).length}, idxMap a₁ ≤ idxMap a₂ ↔ a₁ ≤ a₂ := by
          intros a₁ a₂
          apply Iff.intro
          · intro Ra₁a₂
            exact List.Sorted.antisymm_is_le_sorted_of_nodup_of_sorted (Finset.sort_nodup instLEFin.le X) (Finset.sort_sorted instLEFin.le X) Ra₁a₂
          · intro a₁lea₂
            simp [idxMap]
            apply List.Sorted.rel_get_of_le (Finset.sort_sorted instLEFin.le X) a₁lea₂
        use { toFun := idxMap, inj' := idxMapInj, map_rel_iff' := idxOrdered }
        simp [idxMap]
      obtain ⟨xl, ⟨xlprop, xlτ⟩⟩ := τmodels.left _ xsublx
      simp at xlprop
      obtain ⟨u, ⟨v, ⟨uvprop, uvlit⟩⟩⟩ := xlprop
      simp [← uvlit] at xlτ
      simp [SimpleGraph.isClique_iff, Set.Pairwise, assignment_to_graph] at XClique
      have uvmem := List.mem_of_mem_all_pairs uvprop
      simp at uvmem
      have ultv := List.all_pairs_sorted_of_sorted (X.sort_sorted_lt) _ uvprop
      simp at ultv
      have contra := XClique uvmem.left uvmem.right (Fin.ne_of_lt ultv)
      split at contra
      next => simp_all
      next =>
        have vareq : true = false := by
          cases polarity with
          | true =>
            simp at xlτ
            rw [← xlτ, ← contra]
            congr
            · exact max_eq_right_of_lt ultv
            · exact min_eq_left_of_lt ultv
          | false =>
            simp at xlτ
            rw [← xlτ, ← contra]
            congr
            · exact (max_eq_right_of_lt ultv).symm
            · exact (min_eq_left_of_lt ultv).symm
        simp at vareq
    · simp [SimpleGraph.CliqueFree]
      rintro cliquefree lits clique ⟨cliquesubl, cliquelength⟩ litseq
      simp [← litseq]
      have notclique := cliquefree clique.toFinset
      simp [SimpleGraph.isNClique_iff, clique.toFinset_card_of_nodup (cliquesubl.nodup (List.nodup_ofFn.mpr Function.injective_id)), cliquelength, SimpleGraph.isClique_iff, Set.Pairwise] at notclique
      obtain ⟨u, ⟨umem, ⟨v, ⟨vmem, ⟨uneqv, uvnotadj⟩⟩⟩⟩⟩ := notclique
      use (match polarity with | true => Literal.neg | false => Literal.pos) { i := max u v, j := min u v, ijord := (by simp; intro ueqv; simp [ueqv] at uneqv) }
      apply And.intro
      · use min u v, max u v
        simp [clique.mem_all_pairs_iff_of_irrefl_of_antisymm_of_sorted (cliquesubl.sorted (List.sorted_lt_ofFn_iff.mpr strictMono_id))]
        apply And.intro
        · intro ueqv
          simp [ueqv] at uneqv
        · simp [max_def, min_def]
          split <;> tauto
      · simp [assignment_to_graph] at uvnotadj
        split at uvnotadj
        next ueqv _ =>
          simp [ueqv] at uneqv
        next =>
          cases polarity <;> simp at uvnotadj ⊢ <;> assumption
  )

def RamseyEncoding (N x y : ℕ) : VEncCNF (EdgeVar N.succ) Unit (λ τ ↦ (assignment_to_graph τ true).cliqueNum < x ∧ (assignment_to_graph τ true).indepNum < y) :=
  seq[
    CliqueFreeEncoding N x true,
    CliqueFreeEncoding N y false
  ]
  |>.mapProp (by
    ext τ

    rw [assignment_to_graph_compl τ false]
    simp [assignment_to_graph, ← SimpleGraph.cliqueNum_compl, SimpleGraph.cliqueNum_lt_iff_cliqueFree, -SimpleGraph.indepSetFree_compl, -SimpleGraph.cliqueFree_compl]
  )

def main (argv : List String) : IO UInt32 := do
  let N := argv[0]!.toNat!;
  let x := argv[1]!.toNat!;
  let y := argv[2]!.toNat!;
  -- TODO: Preprocess so that the input is a PNat and one cn call RamseyEncoding N.succ x y
  let cnf := RamseyEncoding N x y

  Solver.Dimacs.printICnf IO.print cnf.val.toICnf

  return 0
