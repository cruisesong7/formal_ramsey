import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Vector3
import Mathlib.Data.Rat.NNRat

import Lean.Parser.Tactic
import Mathlib.Tactic
import FormalRamsey.PickTactic
import FormalRamsey.Utils

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

def RamseyProp (N k : ℕ) (s : Vector ℕ k) : Prop := N > 0 ∧
∀ f : Sym2 (Fin N) → Fin k,
(∃ S i, (graphAtColor (completeGraph (Fin N)) f i).IsNClique (s.get i) S) 

def Ramsey₂Prop (N s t : ℕ) : Prop := RamseyProp N 2 ⟨[s, t], by simp⟩

lemma RamseyMonotone : ∀ {N k s}, RamseyProp N k s → ∀ {M}, N ≤ M → RamseyProp M k s := by
  unfold RamseyProp
  intros N k s R M NleqM
  rcases R with ⟨Ngt0, R⟩
  apply And.intro
  linarith only[Ngt0, NleqM]
  intros f
  let f' : Sym2 (Fin N) → Fin k := λ e ↦ f (Sym2.map (Fin.castLE NleqM) e)
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

theorem Ramsey₂PropSymm : ∀ N s t, Ramsey₂Prop N s t ↔ Ramsey₂Prop N t s := by
  
  have helper : ∀ N s t, Ramsey₂Prop N s t → Ramsey₂Prop N t s
  simp [Ramsey₂Prop, RamseyProp]
  intros N s t Ngt0 R
  simp [Ngt0]
  intro f
  let f' : Sym2 (Fin N) → Fin 2 := λ e ↦ if f e = 0 then 1 else 0
  rcases (R f') with ⟨S, ⟨i, ⟨Sclique, Scard⟩⟩⟩
  use S
  fin_cases i
  use 1
  simp_all
  simp [Vector.head] at Scard 
  simp [Vector.get,List.nthLe]
  constructor
  simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at Sclique ⊢
  intros _ xinS _ yinS xneqy
  have fxyneq0 := (Sclique xinS yinS xneqy).right

  simp_all
  rw [← not0_eq1]
  intro h
  simp[h] at fxyneq0

  assumption

  use 0
  simp_all
  simp [Vector.head] at Scard 
  simp [Vector.get,List.nthLe]
  constructor
  simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at Sclique ⊢
  intros _ xinS _ yinS xneqy
  have fxyeq0 := (Sclique xinS yinS xneqy).right

  simp_all
  by_contra h
  simp[h] at fxyeq0

  assumption

  intros N s t
  use helper N s t, helper N t s
  done


theorem friendshipUpperound : Ramsey₂Prop 6 3 3 := by
  unfold Ramsey₂Prop RamseyProp
  apply And.intro
  simp
  intros f
  haveI tmpInst := SimpleGraph.neighborSetFintype (⊤:SimpleGraph (Fin 6)) 0
  let g : ((⊤:SimpleGraph (Fin 6)).neighborFinset 0) → Fin 2 := λ x ↦  f ⟦(0, x)⟧
  have ghyp : Fintype.card (Fin 2) • 2 < Fintype.card ↑((completeGraph (Fin 6)).neighborFinset 0)
  simp
  have ghyp := Fintype.exists_lt_card_fiber_of_mul_lt_card g ghyp
  rcases ghyp with ⟨c, chyp⟩
  pick x y z  from (Finset.filter (λ (x : (⊤:SimpleGraph (Fin 6)).neighborFinset 0)↦ g x = c) Finset.univ)
  simp at xIns yIns zIns

  have xneqy : ¬(↑x: Fin 6) = ↑y := by 
    intro xeqy 
    simp [← Subtype.ext_iff] at xeqy
    simp [xeqy] at xLty

  have yneqz :  ¬(↑y: Fin 6) = ↑z := by 
    intro yeqz
    simp [← Subtype.ext_iff] at yeqz
    simp [yeqz] at yLtz

  have xneqz : ¬(↑x: Fin 6) = ↑z := by
    intro xeqz
    have xLtz : x < z := by 
      transitivity y
      exact xLty
      exact yLtz
    simp [← Subtype.ext_iff] at xeqz
    simp [xeqz] at xLtz
  
  rcases Nat.eq_zero_or_pos (Finset.filter (λ e ↦ e = c) {f ⟦(↑x, ↑y)⟧,f ⟦(↑y, ↑z)⟧,f ⟦(↑x, ↑z)⟧}).card with h|h
  simp at h
  rw [Finset.filter_eq_empty_iff {f ⟦(↑x, ↑y)⟧, f ⟦(↑y, ↑z)⟧, f ⟦(↑x, ↑z)⟧}] at h
  simp at h
  rcases h with ⟨fxyneqc, fyzneqc, fxzneqc⟩

  have fxy_eq_fyz:= notc fxyneqc fyzneqc
  have fxy_eq_fxz:= notc fxyneqc fxzneqc
  have d0 :(graphAtColor (⊤:SimpleGraph (Fin 6)) f  (f ⟦(↑x, ↑y)⟧)).IsNClique 3 {↑x, ↑ y, ↑ z}
  simp [graphAtColor, completeGraph]
  constructor
  simp [SimpleGraph.isClique_iff, Set.Pairwise]
  rw [@Sym2.eq_swap (Fin 6) ↑y x, @Sym2.eq_swap (Fin 6) ↑z y, @Sym2.eq_swap (Fin 6) ↑z ↑x]
  tauto
  rw [Finset.card_eq_three]
  use ↑x, ↑y, ↑z
  simp [xneqy, yneqz, xneqz]

  fin_cases c 

  simp [not0_eq1] at fxyneqc 
  simp [fxyneqc] at d0
  use {↑x,↑y,↑z}, 1
  simp[Vector.get, List.nthLe,d0]

  simp [← not0_eq1] at fxyneqc
  simp [fxyneqc] at d0
  use {↑x,↑y,↑z}, 0
  simp[Vector.get, List.nthLe,d0]

  simp_all
  pick e from (Finset.filter (λ (e : Fin 2)↦ e = c) {f ⟦(↑x, ↑y)⟧,f ⟦(↑y, ↑z)⟧,f ⟦(↑x, ↑z)⟧}) 
  simp at eIns
  rcases eIns with ⟨eVal, eColor⟩
  have c0 : ∃ a b : (Fin 6), (graphAtColor (completeGraph (Fin 6)) f c).IsNClique 3 {0, a, b}

  have xProp := Subtype.prop x
  simp at xProp
  have yProp := Subtype.prop y
  simp at yProp
  have zProp := Subtype.prop z
  simp at zProp

  rcases eVal with eVal | ⟨eVal | eVal⟩ <;>  rw [eVal] at eColor

  use ↑x, ↑y
  simp [graphAtColor, completeGraph]
  constructor
  simp [SimpleGraph.isClique_iff, Set.Pairwise]
  rw [@Sym2.eq_swap (Fin 6) ↑x 0, @Sym2.eq_swap (Fin 6) ↑y 0, @Sym2.eq_swap (Fin 6) ↑y ↑x]
  tauto
  rw [Finset.card_eq_three]
  use 0, ↑x, ↑y

  use ↑y, ↑z
  simp [graphAtColor, completeGraph]
  constructor
  simp [SimpleGraph.isClique_iff, Set.Pairwise]
  rw [@Sym2.eq_swap (Fin 6) ↑y 0, @Sym2.eq_swap (Fin 6) ↑z 0, @Sym2.eq_swap (Fin 6) ↑z ↑y]
  tauto
  rw [Finset.card_eq_three]
  use 0, ↑y, ↑z

  use ↑x, ↑z
  simp [graphAtColor, completeGraph]
  constructor
  simp [SimpleGraph.isClique_iff, Set.Pairwise]
  rw [@Sym2.eq_swap (Fin 6) ↑x 0, @Sym2.eq_swap (Fin 6) ↑z 0, @Sym2.eq_swap (Fin 6) ↑z ↑x]
  tauto
  rw [Finset.card_eq_three]
  use 0, ↑x, ↑z

  rcases c0 with ⟨a, b, clique0ab⟩
  fin_cases c

  use {0, a, b}, 0
  assumption

  use {0, a, b}, 1
  assumption
  done

noncomputable def Ramsey₂ (s t : ℕ) : ℕ := sInf { N : ℕ | Ramsey₂Prop N s t }

theorem Ramsey₂2 : ∀ k : ℕ, Ramsey₂ 2 k.succ = k.succ := by
  intros k
  unfold Ramsey₂

  have Ramsey₂2_monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | Ramsey₂Prop N 2 k.succ } → M₂ ∈ { N : ℕ | Ramsey₂Prop N 2 k.succ }
  intros M₁ M₂ M₁leM₂
  simp
  intro M₁Ramsey
  apply RamseyMonotone M₁Ramsey M₁leM₂

  rw [Nat.sInf_upward_closed_eq_succ_iff]
  simp
  apply And.intro
  simp [Ramsey₂Prop, RamseyProp]
  intros f
  rcases Finset.eq_empty_or_nonempty (Finset.filter 
  (λ (x : Sym2 (Fin k.succ))↦ ¬ x.IsDiag ∧ f x = 0) Finset.univ) with h|h
  rw [Finset.filter_eq_empty_iff] at h
  use Finset.univ,1
  constructor
  simp [graphAtColor, Vector.get, List.nthLe, SimpleGraph.isClique_iff, Set.Pairwise]
  intros x y xneqy
  let a: Sym2 (Fin (k + 1)) := ⟦(x, y)⟧
  rcases (Quotient.exists_rep a) with ⟨⟨fst,snd⟩,aprop⟩ 
  simp_all
  have nDiag : ¬Sym2.IsDiag a := by simp_all
  cases aprop <;> simp[← not0_eq1, (h a nDiag)] 
  simp [Vector.get, List.nthLe]
  rcases h with ⟨⟨fst,snd⟩ ,wprop⟩ 
  simp at wprop
  use {fst,snd},0
  constructor
  simp [SimpleGraph.isClique_iff, graphAtColor, Set.Pairwise]

  apply And.intro
  intro h ;simp[h] ;exact wprop.right
  intro h ;simp[h,Sym2.eq_swap] ;exact wprop.right
  simp [Vector.get,List.nthLe,Finset.card_eq_two]
  use fst,snd
  simp
  intro h
  simp[h] at wprop
  --NOTE: simp cant catch contradiction
  have temp : Sym2.IsDiag (Sym2.diag snd) := by simp
  cases wprop.left temp
  
  unfold Ramsey₂Prop
  unfold RamseyProp
  simp
  intro
  let f : Sym2 (Fin k) → Fin 2 := λ e ↦ 1
  use f
  by_contra h
  simp at h
  rcases h with ⟨ S, ⟨ i, SProp ⟩ ⟩ 
  fin_cases i

  rw [SimpleGraph.isNClique_iff] at SProp
  rcases SProp with ⟨SisClique,S_card⟩
  unfold graphAtColor at SisClique
  simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at SisClique
  simp [Vector.get, List.nthLe,Finset.card_eq_two] at S_card
  rcases S_card with ⟨x,y,⟨xneqy,Sxy⟩ ⟩ 
  have xins : x ∈ S := by rw [Sxy]; simp
  have yins : y ∈ S := by rw [Sxy]; simp
  exact SisClique xins yins xneqy

  have kcard : Fintype.card (Fin k) < k.succ := by simp
  have cliquefree : (graphAtColor (completeGraph (Fin k)) f 1).CliqueFree k.succ := by 
    apply SimpleGraph.cliqueFree_of_card_lt kcard
  unfold SimpleGraph.CliqueFree at cliquefree
  have Scontra :=  cliquefree S
  contradiction

  assumption
  done

theorem Ramsey₂1Prop : ∀ N k : ℕ, Ramsey₂Prop N.succ 1 k := by
  intros
  simp [Ramsey₂Prop, RamseyProp]
  intros
  use {0}, 0
  constructor
  simp [SimpleGraph.isClique_iff, Set.Pairwise]
  simp [Vector.get]
  simp [List.nthLe]
  done

theorem Ramsey₂1 : ∀ k : ℕ, Ramsey₂ 1 k.succ = 1 := by
  intro k
  simp [Ramsey₂]
  have Ramsey1Monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | Ramsey₂Prop N 1 k.succ } → M₂ ∈ { N : ℕ | Ramsey₂Prop N 1 k.succ }
  intros M₁ M₂ M₁leM₂
  simp
  intro M₁Ramsey
  apply RamseyMonotone M₁Ramsey M₁leM₂
  --NOTE: used to be rewrite[Nat.sInf_upward_closed_eq_succ_iff] (Ramsey1Monotone) 
  rw [Nat.sInf_upward_closed_eq_succ_iff] 
  simp
  apply And.intro
  apply Ramsey₂1Prop 0 k.succ
  simp [Ramsey₂Prop, RamseyProp]
  assumption
  done

def monochromaticVicinity {α : Type} [Fintype α] {c : ℕ} (g : SimpleGraph α) [DecidableRel g.Adj] (v : α) (f : Sym2 α → Fin c) (i : Fin c) : Finset α := Finset.filter (λ x ↦  f ⟦(v, x)⟧ = i) (g.neighborFinset v)

lemma monochromaticVicinity_Ramsey {N c : ℕ} : ∀ (v : Fin N) (f : Sym2 (Fin N) → Fin c) (i : Fin c) (s : Vector ℕ c), RamseyProp (monochromaticVicinity (⊤:SimpleGraph (Fin N)) v f i).card c s → (∃ S, (graphAtColor (completeGraph (Fin N)) f i).IsNClique (s.get i).succ S) ∨ (∃ i' S, i' ≠ i ∧ (graphAtColor (completeGraph (Fin N)) f i').IsNClique (s.get i') S) := by
  intros v f i s Ramsey
  unfold RamseyProp at Ramsey
  rcases Ramsey with ⟨cardgt0, vicinityProp⟩ 
  have cardeq : (Finset.card (@Finset.univ (Fin (monochromaticVicinity (⊤:SimpleGraph (Fin N)) v f i).card) _)) = (monochromaticVicinity (⊤:SimpleGraph (Fin N)) v f i).card := by simp
  have ftrans := bijection_of_eq_card cardeq
  simp at ftrans
  rcases ftrans with ftrans | ftrans
  simp [(Finset.card_eq_zero.mpr ftrans.right)] at cardgt0
  simp
  rcases ftrans with ⟨ftrans, ftransbij⟩
  have ftransembinj : Function.Injective ((λ x ↦ ↑(ftrans ⟨x, Finset.mem_univ x⟩)):(Fin (monochromaticVicinity (⊤:SimpleGraph (Fin N)) v f i).card → Fin N))
  intros _ _ fa₁a₂
  simp at fa₁a₂
  have a₁a₂eq := ftransbij.left (Subtype.ext fa₁a₂)
  simp at a₁a₂eq
  exact a₁a₂eq
  let ftransemb : Function.Embedding (Fin (monochromaticVicinity (⊤:SimpleGraph (Fin N)) v f i).card) (Fin N) := ⟨λ x ↦ ↑(ftrans ⟨x, Finset.mem_univ x⟩), ftransembinj⟩
  rcases vicinityProp (λ e ↦ f (e.map ((λ x ↦ ↑(ftrans ⟨x, Finset.mem_univ x⟩)):(Fin (monochromaticVicinity (⊤:SimpleGraph (Fin N)) v f i).card → Fin N)))) with ⟨S, ⟨i', Sclique⟩⟩
  rcases (instDecidableEqFin c i' i) with h|h

  right
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

  left
  use (insert v (S.map ftransemb))
  constructor
  simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor]
  apply And.intro
  · intros a _ _
    have ftransaprop := (ftrans ⟨a, Finset.mem_univ a⟩).prop
    simp [monochromaticVicinity] at ftransaprop
    exact ftransaprop
  · intros a ainS
    have ftransaprop := (ftrans ⟨a, Finset.mem_univ a⟩).prop
    simp [monochromaticVicinity] at ftransaprop
    apply And.intro
    · rw [Sym2.eq_swap]
      intros ftransa
      simp [ftransa, ftransaprop.right]
    · intros b binS ftransneq
      simp [ftransneq]
      simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at Sclique
      rcases (instDecidableEqFin _ a b) with aneqb | aeqb
      have abedge := Sclique.clique ainS binS aneqb
      simp at abedge
      simp [← h, abedge.right]
      simp [aeqb] at ftransneq
  · have vnotinSmap : v ∉ (S.map ftransemb) := by
      simp_all
      intros a _ ftransa
      have ftransat := (ftrans ⟨a, Finset.mem_univ a⟩).prop
      simp [ftransa, monochromaticVicinity] at ftransat
    rw [Finset.card_insert_of_not_mem vnotinSmap]
    simp [Sclique.card_eq, h]
  done

theorem Ramsey₂PropIneq : ∀ M N s t : ℕ, Ramsey₂Prop M s.succ t.succ.succ → Ramsey₂Prop N s.succ.succ t.succ → Ramsey₂Prop (M + N) s.succ.succ t.succ.succ := by
  intros M N s t RamseyM RamseyN
  have MNpos : M + N > 0 := by simp [Nat.add_lt_add, RamseyM.left, RamseyN.left]
  unfold Ramsey₂Prop RamseyProp
  apply And.intro
  exact MNpos

  intro f
  rcases (Nat.exists_eq_succ_of_ne_zero (Ne.symm (ne_of_lt MNpos.lt))) with ⟨MN, MNprop⟩
  haveI : NeZero (M + N) := by
    constructor
    intro h
    simp [h] at MNpos
  let g : Fin 2 → ℚ := λ x ↦ (monochromaticVicinity (⊤:SimpleGraph (Fin (M + N))) 0 f x).card
  let h : Fin 2 → ℚ := ![↑M - mkRat 1 2, ↑N - mkRat 1 2]
  have hgsum : Finset.univ.sum h = Finset.univ.sum g
  simp [Finset.univ_fin2]
  have lhs :  ↑M - mkRat 1 2 + (↑N - mkRat 1 2) = ↑M + ↑N - 1 := by
    abel
    cancel_denoms
    simp [add_comm]

  simp [lhs]
  rcases (Nat.exists_eq_succ_of_ne_zero (ne_of_gt MNpos.lt)) with ⟨O, Oprop⟩
  have filterdisj : Disjoint (monochromaticVicinity (⊤:SimpleGraph (Fin (M + N))) 0 f 0) (monochromaticVicinity (⊤:SimpleGraph (Fin (M + N))) 0 f 1)
  rw [Finset.disjoint_iff_ne]
  intros _ ainS _ binT
  simp [monochromaticVicinity] at ainS binT
  intro aeqb
  rw [aeqb] at ainS
  cases Eq.trans (Eq.symm binT.right) ainS.right
  --NOTE ugly
  rw [← Rat.mkRat_self (monochromaticVicinity ⊤ 0 f 0).card, ← Rat.mkRat_self (monochromaticVicinity ⊤ 0 f 1).card]
  rw [Rat.mkRat_add_mkRat]
  rw[Rat.coe_nat_num , Rat.coe_nat_den]
  rw[Rat.coe_nat_num , Rat.coe_nat_den]
  have numSimp1 : (↑(Finset.card (monochromaticVicinity ⊤ 0 f 0)) : ℤ )* ↑(1:ℕ) = ↑(Finset.card (monochromaticVicinity ⊤ 0 f 0)) := by
    simp[Int.mul_one]
  have numSimp2 : (↑(Finset.card (monochromaticVicinity ⊤ 0 f 1)) : ℤ )* ↑(1:ℕ) = ↑(Finset.card (monochromaticVicinity ⊤ 0 f 1)) := by
    simp[Int.mul_one]
  rw [numSimp1, numSimp2,Int.ofNat_add_out]
  simp at filterdisj
  have seteq : (monochromaticVicinity ⊤ 0 f 0) ∪ (monochromaticVicinity ⊤ 0 f 1) = ((⊤:SimpleGraph (Fin (M + N))).neighborFinset 0)
  apply subset_antisymm <;> unfold HasSubset.Subset
  intros _ ainset
  simp [monochromaticVicinity] at ainset ⊢
  rcases ainset with aprop| aprop <;> exact aprop.left
  intros a ainset
  simp at ainset ⊢

  by_contra h
  simp[not_or] at h
  simp[monochromaticVicinity, ainset, not0_eq1] at h

  rw [← Finset.card_union_eq filterdisj, seteq, SimpleGraph.neighborFinset_eq_filter]
  simp [← SimpleGraph.completeGraph_eq_top, completeGraph, Finset.filter_ne]

  rw[Rat.mkRat_one]
  have MNle1 : 1 ≤ M + N := by linarith only [MNpos]
  rw [Int.coe_nat_sub MNle1]
  
  rw[← Int.ofNat_add_out]
  rw[← Rat.cast_coe_nat M]  
  rw[← Rat.cast_coe_nat N] 
  admit; admit
  -- rw [← Rat.mkRat_self M , ← Rat.mkRat_self N, ← Rat.divInt_one_one]
  -- simp [Rat.add_def', Rat.sub_def']
  -- simp [Rat.mkRat_eq_iff]
  -- rw [← Int.coe_nat_add M N, ← Rat.mk_one_one, Rat.sub_def (ne_of_gt Int.zero_lt_one) (ne_of_gt Int.zero_lt_one)]

  simp[Oprop]
  have halflt1 :mkRat 1 2 < 1 := by simp
  have mp := missing_pigeonhole (Exists.intro (0 : Fin 2) (Finset.mem_univ (0 : Fin 2))) (le_of_eq hgsum)
  rcases mp with ⟨a, ainuniv, gha⟩
  fin_cases a<;> simp_all[-halflt1]

  have MtoZ : (↑M:ℚ) = (↑M:ℤ) := by simp
  rw [MtoZ] at gha
  rw [← Rat.le_floor] at gha

  have MleqNeighbor0 := floormagic M (monochromaticVicinity (⊤:SimpleGraph (Fin (M + N))) 0 f 0).card (mkRat 1 2) halflt1 gha
  have cliquecases := monochromaticVicinity_Ramsey 0 f 0 ⟨[s.succ, t.succ.succ], by simp⟩ (RamseyMonotone RamseyM MleqNeighbor0)
  rcases cliquecases with ⟨S, Sclique⟩ |cliquecases
  use S, 0
  exact Sclique
  rcases cliquecases with ⟨i, ⟨S, Sclique⟩⟩
  use S, 1
  have ieq1 := notc Sclique.left (Fin.succ_ne_zero 0)
  simp [ieq1] at Sclique
  exact Sclique

  have NtoZ : (↑N:ℚ) = (↑N:ℤ) := by simp
  rw [NtoZ] at gha
  rw [← Rat.le_floor] at gha
  have NleqNeighbor1 := floormagic N (monochromaticVicinity (⊤:SimpleGraph (Fin (M + N))) 0 f 1).card (mkRat 1 2) halflt1 gha
  have cliquecases := monochromaticVicinity_Ramsey 0 f 1 ⟨[s.succ.succ, t.succ], by simp⟩ (RamseyMonotone RamseyN NleqNeighbor1)
  rcases cliquecases with ⟨T, Tclique⟩ |cliquecases
  use T, 1
  exact Tclique
  rcases cliquecases with ⟨i, ⟨T, Tclique⟩⟩
  use T, 0
  have ineq1 := notc Tclique.left Fin.zero_ne_one
  simp [ineq1] at Tclique
  exact Tclique
  done

theorem Ramsey₂PropStrictIneq : ∀ M N s t : ℕ, Even M → Even N → Ramsey₂Prop M s.succ t.succ.succ → Ramsey₂Prop N s.succ.succ t.succ → Ramsey₂Prop (M + N).pred s.succ.succ t.succ.succ := by
  intros M N s t evenM evenN RamseyM RamseyN
  rcases (Nat.exists_eq_succ_of_ne_zero (Ne.symm (ne_of_lt RamseyM.left))) with ⟨M', rfl⟩
  rcases (Nat.exists_eq_succ_of_ne_zero (Ne.symm (ne_of_lt RamseyN.left))) with ⟨N', rfl⟩
  simp [Nat.succ_add, Nat.add_succ]
  unfold Ramsey₂Prop RamseyProp
  simp
  intro f 
  let g : Fin 2 → ℕ := (λ x ↦ 2 * (Finset.filter (λ e ↦ f e = x) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset).card)
  let h : Fin 2 → ℕ := ![(M' + N').succ * M', (M' + N').succ * N']
  have hgsum : Finset.univ.sum h = Finset.univ.sum g
  simp [Finset.univ_fin2]
  rw [← Nat.left_distrib, ← Nat.left_distrib]
  have filterdisj : Disjoint (Finset.filter (λ e ↦ f e = 0) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset) (Finset.filter (λ e ↦ f e = 1) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset)
  simp [Finset.disjoint_iff_ne]
  intros a _ fa0 b _ fb1
  by_contra h
  simp [h,fb1] at fa0
  rw [← Finset.card_union_eq filterdisj]
  have seteq : (Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = 0) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset ∪ Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = 1) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset) = (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset
  simp[Finset.Subset.antisymm_iff,Finset.subset_iff]
  apply And.intro
  intros _ xprop ; cases xprop <;> simp_all  
  intros x xprop 
  by_contra h
  simp [not_or,not0_eq1, xprop] at h

  rw [seteq, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp
  have mp := missing_pigeonhole (Exists.intro (0 : Fin 2) (Finset.mem_univ (0 : Fin 2))) (Nat.le_of_eq hgsum)
  rcases mp with ⟨a, ainuniv, gha⟩

  have cardodd : Odd (M' + N').succ := by
    simp[← Nat.even_add_one]
    rw[← Nat.succ_add, Nat.add_assoc, Nat.add_one]
    simp[Nat.even_add, evenM, evenN]

  fin_cases a <;> simp_all[-cardodd]

  have evenrhs : Even (2 * (Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = 0) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset).card) := by simp
  have xoreven : Xor' (Even ((M' + N').succ * M')) (Even (2 * (Finset.filter (λ (e : Sym2 (Fin (M' + N').succ))↦ f e = 0) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset).card))
  right
  simp
  rw [← Nat.add_one, Nat.even_add_one, ← Nat.odd_iff_not_even] at evenM
  have oddlhs := Nat.odd_mul.mpr ⟨cardodd, evenM⟩
  simp at oddlhs
  exact oddlhs
  have ghalt := xor_even_le_implies_lt xoreven gha

  rw [dblcnt M' N' f 0] at ghalt
  have pghineq : (@Finset.univ (Fin (M' + N').succ) _).card • M' < ↑((Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart)↦ f ⟦x.toProd⟧ = 0) Finset.univ).card) := by simp [ghalt]
  have pgh := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (λ (e : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) _ ↦ Finset.mem_univ e.snd) pghineq
  rcases pgh with ⟨v, _, vprop⟩
  simp at vprop
  have cardeq : (Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart)↦ x.toProd.snd = v)
        (Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart)↦ f ⟦x.toProd⟧ = 0) Finset.univ)).card = (monochromaticVicinity (⊤ : SimpleGraph (Fin (M' + N').succ)) v f 0).card
  apply Finset.card_congr (λ (a : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) _ ↦ a.fst)
  intro a
  simp [monochromaticVicinity]
  intros f0 asndv
  have aprop := a.is_adj
  simp[asndv] at aprop
  simp[Ne.symm aprop]
  simp [Sym2.eq_swap, ← asndv]
  exact f0
  intros _ _
  simp
  intros _ asndv _ bsndv abfst
  rw [SimpleGraph.Dart.ext_iff, Prod.ext_iff]
  simp [abfst, asndv, bsndv]
  intro b
  simp [monochromaticVicinity]
  intros bnotv fvb0
  have bvAdj: (⊤ : SimpleGraph (Fin (M' + N').succ)).Adj b v := by simp [Ne.symm, bnotv]
  use SimpleGraph.Dart.mk (b,v) bvAdj 
  simp [Sym2.eq_swap, fvb0]
  rw [cardeq] at vprop
  have cliquecases := monochromaticVicinity_Ramsey v f 0 ⟨[s.succ, t.succ.succ], by simp⟩ (RamseyMonotone RamseyM vprop)
  rcases cliquecases with ⟨S, Sclique⟩ | cliquecases
  use S, 0
  exact Sclique
  rcases cliquecases with ⟨i, ⟨S, Sclique⟩⟩
  use S, 1
  have ieq1 := notc Sclique.left (Fin.succ_ne_zero 0)
  simp [ieq1] at Sclique
  exact Sclique

  have evenrhs : Even (2 * (Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = 1) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset).card) := by simp
  have xoreven : Xor' (Even ((M' + N').succ * N')) (Even (2 * (Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = 1) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset).card))
  right
  simp
  rw [← Nat.add_one, Nat.even_add_one, ← Nat.odd_iff_not_even] at evenN
  have oddlhs := Nat.odd_mul.mpr ⟨cardodd, evenN⟩
  simp at oddlhs
  exact oddlhs
  have ghalt := xor_even_le_implies_lt xoreven gha
  rw [dblcnt M' N' f 1] at ghalt
  have pghineq : (@Finset.univ (Fin (M' + N').succ) _).card • N' < ↑((Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) ↦ f ⟦x.toProd⟧ = 1) Finset.univ).card) := by simp [ghalt]
  have pgh := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (λ (e : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) _ ↦ Finset.mem_univ e.snd) pghineq
  rcases pgh with ⟨v, _, vprop⟩
  have cardeq : (Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) ↦ x.toProd.snd = v)
        (Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) ↦ f ⟦x.toProd⟧ = 1) Finset.univ)).card = (monochromaticVicinity (⊤ : SimpleGraph (Fin (M' + N').succ)) v f 1).card
  apply Finset.card_congr (λ (a : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) _ ↦ a.fst)
  intro a
  simp [monochromaticVicinity]
  intros f1 asndv
  apply And.intro
  intro afstv
  have aprop := a.is_adj
  simp [asndv, ← afstv] at aprop
  simp [Sym2.eq_swap, ← asndv, f1]
  intros _ _
  simp
  intros _ asndv _ bsndv abfst
  rw [SimpleGraph.Dart.ext_iff, Prod.ext_iff]
  simp [abfst, asndv, bsndv]
  intro b
  simp [monochromaticVicinity]
  intros bnotv fvb1
  have bvAdj: (⊤ : SimpleGraph (Fin (M' + N').succ)).Adj b v := by simp [Ne.symm, bnotv]
  use SimpleGraph.Dart.mk (b,v) bvAdj 
  simp [Sym2.eq_swap, fvb1]
  rw [cardeq] at vprop
  have cliquecases := monochromaticVicinity_Ramsey v f 1 ⟨[s.succ.succ, t.succ], by simp⟩ (RamseyMonotone RamseyN vprop)
  rcases cliquecases with ⟨T, Tclique⟩ | cliquecases
  use T, 1
  exact Tclique
  rcases cliquecases with ⟨i, ⟨T, Tclique⟩⟩
  use T, 0
  have ineq1 := notc Tclique.left Fin.zero_ne_one
  simp [ineq1] at Tclique
  exact Tclique
  done

theorem Ramsey₂Finite : ∀ s t : ℕ, { N : ℕ | Ramsey₂Prop N s.succ t.succ }.Nonempty := by 
  suffices Ramsey₂FiniteAdditive : ∀ m : ℕ, ∀ s t, m = s + t → { N : ℕ | Ramsey₂Prop N s.succ t.succ }.Nonempty
  intros s t
  simp [Ramsey₂FiniteAdditive (s + t) s t]
  
  intro m
  induction' m with st ih
  intros s t h
  have h' := Eq.symm h
  simp at h'
  rcases h' with ⟨s0, t0⟩ 
  simp [s0, t0]
  use 1
  simp
  simp [Ramsey₂Prop, RamseyProp]
  intro
  use {0}, 0
  constructor<;> simp [SimpleGraph.isClique_iff, Set.Pairwise, Vector.head]
  intros s t h
  cases s<;>
  cases t
  use 1
  simp [Ramsey₂1Prop]
  use 1
  simp [Ramsey₂1Prop]
  use 1
  simp
  rw [Ramsey₂PropSymm]
  simp [Ramsey₂1Prop]
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
  apply Ramsey₂PropIneq <;> assumption
  done

theorem Ramsey₂Ineq : ∀ s t : ℕ, Ramsey₂ s.succ.succ t.succ.succ ≤ Ramsey₂ s.succ t.succ.succ + Ramsey₂ s.succ.succ t.succ := by 
  intros s t
  have RamseyM := Nat.sInf_mem (Ramsey₂Finite s t.succ)
  have RamseyN := Nat.sInf_mem (Ramsey₂Finite s.succ t)
  apply Nat.sInf_le
  simp_all  
  apply Ramsey₂PropIneq<;> assumption
  done

theorem Ramsey₂StrictIneq : ∀ s t : ℕ, Even (Ramsey₂ s.succ t.succ.succ) → Even (Ramsey₂ s.succ.succ t.succ) → Ramsey₂ s.succ.succ t.succ.succ < Ramsey₂ s.succ t.succ.succ + Ramsey₂ s.succ.succ t.succ := by
  intros s t evenM evenN
  have lt_or_eq := Decidable.lt_or_eq_of_le (Ramsey₂Ineq s t)
  rcases lt_or_eq with lt | eq
  exact lt 

  have temp := Ramsey₂PropStrictIneq (Ramsey₂ s.succ t.succ.succ) (Ramsey₂ s.succ.succ t.succ) (s) (t) evenM evenN
  unfold Ramsey₂ at temp
  have RamseyM := Nat.sInf_mem (Ramsey₂Finite s t.succ)
  have RamseyN := Nat.sInf_mem (Ramsey₂Finite s.succ t)
  simp at RamseyM RamseyN
  unfold Ramsey₂ at eq

  have pos : (sInf {N : ℕ | Ramsey₂Prop N s.succ t.succ.succ} + sInf {N : ℕ | Ramsey₂Prop N s.succ.succ t.succ}) ≠ 0
  simp[← eq]
  by_contra h
  rcases h with h | h
  unfold Ramsey₂Prop RamseyProp at h
  simp at h
  have contra := Ramsey₂Finite s.succ t.succ
  simp [h] at contra

  have pred_lt : (sInf {N : ℕ | Ramsey₂Prop N s.succ t.succ.succ} + sInf {N : ℕ | Ramsey₂Prop N s.succ.succ t.succ}).pred < 
  (sInf {N : ℕ | Ramsey₂Prop N s.succ t.succ.succ} + sInf {N : ℕ | Ramsey₂Prop N s.succ.succ t.succ}) := by simp[ Nat.pred_lt pos]

  have predInSet : (sInf {N : ℕ | Ramsey₂Prop N s.succ t.succ.succ} + 
  sInf {N : ℕ | Ramsey₂Prop N s.succ.succ t.succ}).pred ∈ 
  {N : ℕ | Ramsey₂Prop N s.succ.succ t.succ.succ} := by simp[temp RamseyM RamseyN]

  have le_pred :=  Nat.sInf_le predInSet
  simp[eq] at le_pred
  have absurd := lt_of_le_of_lt le_pred pred_lt
  simp at absurd
  done

theorem Ramsey₂Symm : ∀  s t: ℕ, Ramsey₂ s.succ t.succ = Ramsey₂ t.succ s.succ := by 
  intros s t
  apply Nat.le_antisymm
  have RamseyM := Nat.sInf_mem (Ramsey₂Finite t s)
  apply Nat.sInf_le
  simp [Ramsey₂] at RamseyM ⊢
  rw [Ramsey₂PropSymm] at RamseyM
  assumption
  have RamseyN := Nat.sInf_mem (Ramsey₂Finite s t)
  apply Nat.sInf_le
  simp [Ramsey₂] at RamseyN ⊢
  rw [Ramsey₂PropSymm] at RamseyN
  assumption
  done

theorem friendship_upper_bound_alt : Ramsey₂ 3 3 ≤ 6 := by
  have R33 := Ramsey₂Ineq 1 1
  rw [Ramsey₂Symm 2 1, Ramsey₂2] at R33
  exact R33
  done

theorem friendship : Ramsey₂ 3 3 = 6 := sorry

theorem Ramsey₂_binomial_coefficient_ineq : ∀ s t : ℕ, Ramsey₂ s.succ t.succ 
≤ Nat.choose (s.succ + t.succ - 2) (s.succ - 1) := by
  intros s t

  induction' s with s' ihp₁ generalizing t
  simp [Ramsey₂1 t]

  induction' t with t' ihp₂
  rw [Ramsey₂Symm]
  simp [Ramsey₂1 s'.succ]
  transitivity Ramsey₂ s'.succ t'.succ.succ + Ramsey₂ s'.succ.succ t'.succ
  apply Ramsey₂Ineq s' t'

  have temp₁: Ramsey₂ s'.succ t'.succ.succ + Ramsey₂ s'.succ.succ t'.succ
  ≤ (s'.succ + t'.succ.succ - 2).choose s' + (s'.succ.succ + t'.succ - 2).choose s'.succ
  apply add_le_add
  exact ihp₁ t'.succ
  exact ihp₂

  have temp₂ :(s'.succ.succ + t'.succ.succ - 2).choose (s'.succ.succ - 1) = 
  (s'.succ + t'.succ.succ - 2).choose s' + (s'.succ.succ + t'.succ - 2).choose s'.succ
  := by simp [Nat.succ_add, Nat.add_succ,Nat.choose_succ_succ]
  rw [temp₂]
  exact temp₁
  done