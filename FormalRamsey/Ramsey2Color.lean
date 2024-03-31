import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Rat.NNRat

--import Mathlib.Tactic.PermuteGoals
import Lean.Parser.Tactic
import Mathlib.Tactic

-- import FormalRamsey.PickTactic
import FormalRamsey.RamseyBase
import FormalRamsey.RamseyGraphs
import FormalRamsey.Fin2

open Ramsey

def Ramsey₂Prop (N s t : ℕ) : Prop := RamseyProp N (s ::ᵥ t ::ᵥ Vector.nil)

def Ramsey₂GraphProp (N s t : ℕ) : Ramsey₂Prop N s t ↔ RamseyGraphProp N s t := by
  unfold Ramsey₂Prop RamseyProp RamseyGraphProp
  apply Iff.intro
  · intros Ramsey₂N G _
    have coloredClique := Ramsey₂N (λ e ↦ if e ∈ G.edgeSet then 0 else 1)
    rcases coloredClique with ⟨S, i, Sclique⟩
    fin_cases i <;> simp [graphAtColor] at Sclique <;>
    simp [SimpleGraph.isNClique_iff, SimpleGraph.IsClique, Set.Pairwise] at Sclique ⊢
    . left
      use S
      simp [Sclique.right]
      intros _ xInS _ yInS xneqy
      have tmp := Sclique.left xInS yInS xneqy
      by_contra h
      simp[h] at tmp
    · right
      use S
      simp [Sclique.right, Vector.get, List.nthLe]
      intros _ xInS _ yInS xneqy
      have tmp := Sclique.left xInS yInS xneqy
      simp[xneqy]
      by_contra h
      simp[h] at tmp

  · intros RamseyGraphN f
    let GAdj : Fin N → Fin N → Prop := λ u v ↦ ((u ≠ v) ∧ (f s(u, v) = 0))
    have GAdjSym : Symmetric GAdj := by
      simp [Symmetric]
      intros _ _ xneqy fxyeq0
      simp [Ne.symm xneqy, Sym2.eq_swap, fxyeq0]
    have GAdjLoopless : Irreflexive GAdj := by simp [Irreflexive]
    have graphClique := RamseyGraphN { Adj := GAdj, symm := GAdjSym, loopless := GAdjLoopless }
    rcases graphClique with ⟨S, Sclique⟩ | ⟨T, Tclique⟩
    · use S, 0
      simp [SimpleGraph.isNClique_iff, SimpleGraph.IsClique, Set.Pairwise] at Sclique ⊢
      simp [Sclique.right, graphAtColor]
      intros _ xInS _ yInS xneqy
      simp_all
    · use T, 1
      simp [SimpleGraph.isNClique_iff, SimpleGraph.IsClique, Set.Pairwise] at Tclique ⊢
      simp [Tclique.right, graphAtColor, Vector.get, List.nthLe]
      intros _ xInT _ yInT xneqy
      have tmp :=  (Tclique.left xInT yInT xneqy).right xneqy
      simp [not0_eq1] at tmp
      simp [xneqy, tmp]

theorem Ramsey₂PropSymm : ∀ {N s t}, Ramsey₂Prop N s t ↔ Ramsey₂Prop N t s := by

  suffices helper : ∀ N s t, Ramsey₂Prop N s t → Ramsey₂Prop N t s
  intros N s t
  use helper N s t, helper N t s

  simp [Ramsey₂Prop, RamseyProp]
  intros N s t R f
  let f' : Sym2 (Fin N) → Fin 2 := λ e ↦ if f e = 0 then 1 else 0
  rcases (R f') with ⟨S, ⟨i, ⟨SClique, SCard⟩⟩⟩
  use S
  fin_cases i; use 1; swap; use 0
  all_goals (
    simp_all
    constructor
    simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at SClique ⊢
    intros _ xinS _ yinS xneqy
    simp_all
  )
  · simp [Vector.get, List.nthLe] at SCard
    assumption
  · by_contra h; simp[← not0_eq1] at h; simp_all
  · simp [Vector.get, List.nthLe, SCard]
  done

theorem friendshipUpperbound : Ramsey₂Prop 6 3 3 := by
  unfold Ramsey₂Prop RamseyProp
  intro f
  haveI tmpInst := SimpleGraph.neighborSetFintype (⊤:SimpleGraph (Fin 6)) 0
  let g : ((⊤:SimpleGraph (Fin 6)).neighborFinset 0) → Fin 2 := λ x ↦  f s(0, x)
  have ghyp : Fintype.card (Fin 2) • 2 < Fintype.card ↑((completeGraph (Fin 6)).neighborFinset 0) := by simp
  have ghyp := Fintype.exists_lt_card_fiber_of_mul_lt_card g ghyp
  rcases ghyp with ⟨c, chyp⟩
  simp [Finset.two_lt_card_iff] at chyp
  rcases chyp with ⟨x, _, _, y, _, _, z, _, ⟨xneqy, ⟨_, xneqz⟩, yneqz⟩⟩
  -- pick x y z  from (Finset.filter (λ (x : (⊤:SimpleGraph (Fin 6)).neighborFinset 0)↦ g x = c) Finset.univ)
  -- simp at xIns yIns zIns

  -- have xneqy : ¬(↑x: Fin 6) = ↑y := by
  --   intro xeqy
  --   simp [← Subtype.ext_iff] at xeqy
  --   simp [xeqy] at xLty

  -- have yneqz :  ¬(↑y: Fin 6) = ↑z := by
  --   intro yeqz
  --   simp [← Subtype.ext_iff] at yeqz
  --   simp [yeqz] at yLtz

  -- have xneqz : ¬(↑x: Fin 6) = ↑z := by
  --   intro xeqz
  --   have xLtz : x < z := by
  --     transitivity y
  --     exact xLty
  --     exact yLtz
  --   simp [← Subtype.ext_iff] at xeqz
  --   simp [xeqz] at xLtz

  rcases Nat.eq_zero_or_pos (Finset.filter (λ e ↦ e = c) {f s(↑x, ↑y),f s(↑y, ↑z),f s(↑x, ↑z)}).card with h|h
  simp at h
  simp [Finset.filter_eq_empty_iff ] at h
  rcases h with ⟨fxyneqc, fyzneqc, fxzneqc⟩

  have fxy_eq_fyz:= notc fxyneqc fyzneqc
  have fxy_eq_fxz:= notc fxyneqc fxzneqc
  have d0 :(graphAtColor (⊤:SimpleGraph (Fin 6)) f  (f s(↑x, ↑y))).IsNClique 3 {↑x, ↑ y, ↑ z} := by
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
  simp[Vector.get,List.nthLe,d0]

  simp [← not0_eq1] at fxyneqc
  simp [fxyneqc] at d0
  use {↑x,↑y,↑z}, 0
  simp[Vector.get, List.nthLe,d0]

  simp [Finset.card_pos] at h
  have e := Finset.Nonempty.bex h
  rcases e with ⟨e, eIns⟩
  --simp at h
  --pick e from (Finset.filter (λ (e : Fin 2)↦ e = c) {f ⟦(↑x, ↑y)⟧,f ⟦(↑y, ↑z)⟧,f ⟦(↑x, ↑z)⟧})
  simp at eIns
  rcases eIns with ⟨eVal, eColor⟩
  suffices c0 : ∃ a b : (Fin 6), (graphAtColor (completeGraph (Fin 6)) f c).IsNClique 3 {0, a, b}

  -- have xProp := Subtype.prop x
  -- simp at xProp
  -- have yProp := Subtype.prop y
  -- simp at yProp
  -- have zProp := Subtype.prop z
  -- simp at zProp
  rcases c0 with ⟨a, b, _⟩
  fin_cases c
  · use {0, a, b}, 0
    assumption
  · use {0, a, b}, 1
    assumption

  rcases eVal with eVal | ⟨eVal | eVal⟩ <;>  rw [eVal] at eColor

  use ↑x, ↑y; rotate_left; use ↑y, ↑z; rotate_left; use ↑x, ↑z
  all_goals{
    simp [graphAtColor, completeGraph]
    constructor
    simp [SimpleGraph.isClique_iff, Set.Pairwise]
    first | rw [@Sym2.eq_swap (Fin 6) ↑x 0, @Sym2.eq_swap (Fin 6) ↑z 0, @Sym2.eq_swap (Fin 6) ↑z ↑x]
          | rw [@Sym2.eq_swap (Fin 6) ↑y 0, @Sym2.eq_swap (Fin 6) ↑z 0, @Sym2.eq_swap (Fin 6) ↑z ↑y]
          | rw [@Sym2.eq_swap (Fin 6) ↑x 0, @Sym2.eq_swap (Fin 6) ↑y 0, @Sym2.eq_swap (Fin 6) ↑y ↑x]
    tauto
    rw [Finset.card_eq_three]
    try{use 0, ↑x, ↑z}
    try{use 0, ↑y, ↑z}
    try{use 0, ↑x, ↑y}
  }
  done

noncomputable def Ramsey₂ (s t : ℕ) : ℕ := sInf { N : ℕ | Ramsey₂Prop N s t }

theorem Ramsey₂2 : ∀ k : ℕ, Ramsey₂ 2 k.succ = k.succ := by
  intros k
  unfold Ramsey₂

  have Ramsey₂2_monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | Ramsey₂Prop N 2 k.succ } → M₂ ∈ { N : ℕ | Ramsey₂Prop N 2 k.succ } := by
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
  let a: Sym2 (Fin (k + 1)) := s(x, y)
  rcases (Quot.exists_rep a) with ⟨⟨fst,snd⟩,aprop⟩
  simp_all
  have nDiag : ¬Sym2.IsDiag a := by simp_all
  cases aprop <;> simp[← not0_eq1, (h nDiag)]
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
  rw [← Sym2.mk_isDiag_iff] at h
  cases wprop.left h

  simp [Ramsey₂Prop, RamseyProp]
  let f : Sym2 (Fin k) → Fin 2 := λ _ ↦ 1
  use f
  intros S i
  fin_cases i
  · simp [SimpleGraph.isNClique_iff, graphAtColor, SimpleGraph.isClique_iff, Set.Pairwise]
    intros absurd Scard
    rw [Finset.card_eq_two] at Scard
    rcases Scard with ⟨x, y, ⟨xneqy, Sxy⟩⟩
    simp_all
  · simp [SimpleGraph.isNClique_iff, graphAtColor, SimpleGraph.isClique_iff, Set.Pairwise, Vector.get, List.nthLe]
    intros Scard
    have absurd := Finset.card_le_card (Finset.subset_univ S)
    simp_arith [Scard] at absurd
  assumption
  done

-- TODO Rename to Prop1
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
  have Ramsey1Monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | Ramsey₂Prop N 1 k.succ } → M₂ ∈ { N : ℕ | Ramsey₂Prop N 1 k.succ } := by
    intros M₁ M₂ M₁leM₂
    simp
    intro M₁Ramsey
    apply RamseyMonotone M₁Ramsey M₁leM₂
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  · simp
    apply And.intro
    apply Ramsey₂1Prop 0 k.succ
    simp [Ramsey₂Prop, RamseyProp]
    use (λ _ ↦ 0)
    intros S i
    have Sempty : S = ∅ := by simp[Finset.eq_empty_iff_forall_not_mem]
    fin_cases i <;> simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor, Sempty, Vector.get, List.nthLe]
  · assumption

theorem Ramsey₂PropIneq : ∀ {M N s t : ℕ}, 0 < M + N → Ramsey₂Prop M s t.succ → Ramsey₂Prop N s.succ t → Ramsey₂Prop (M + N) s.succ t.succ := by
  intros M N s t MNpos RamseyM RamseyN
  unfold Ramsey₂Prop RamseyProp
  intro f
  haveI : NeZero (M + N) := by
    constructor
    intro h
    simp [h] at MNpos
  let g : Fin 2 → ℚ := λ x ↦ (monochromaticVicinity (⊤:SimpleGraph (Fin (M + N))) 0 f x).card
  let h : Fin 2 → ℚ := ![↑M - mkRat 1 2, ↑N - mkRat 1 2]
  have hgsum : Finset.univ.sum h = Finset.univ.sum g := by
    simp [Finset.univ_fin2]
    have lhs :  ↑M - mkRat 1 2 + (↑N - mkRat 1 2) = ↑M + ↑N - 1 := by
      abel_nf
      cancel_denoms
      simp [add_comm]

    simp [lhs]
    have filterdisj : Disjoint (monochromaticVicinity (⊤:SimpleGraph (Fin (M + N))) 0 f 0) (monochromaticVicinity (⊤:SimpleGraph (Fin (M + N))) 0 f 1) := by
      rw [Finset.disjoint_iff_ne]
      intros _ ainS _ binT
      simp [monochromaticVicinity] at ainS binT
      intro aeqb
      rw [aeqb] at ainS
      cases Eq.trans (Eq.symm binT.right) ainS.right
  -- NOTE One should be able to get away with a few rewrites and then letting simp deal with the rest,
  --       but that approach causes whnf time out in my computer.
    rw [Rat.add_def' ↑(Finset.card (monochromaticVicinity ⊤ 0 f 0)) ↑(Finset.card (monochromaticVicinity ⊤ 0 f 1)), Rat.coe_nat_den (Finset.card (monochromaticVicinity ⊤ 0 f 0)), Rat.coe_nat_num (Finset.card (monochromaticVicinity ⊤ 0 f 0)), Rat.coe_nat_den (Finset.card (monochromaticVicinity ⊤ 0 f 1)), Rat.coe_nat_num (Finset.card (monochromaticVicinity ⊤ 0 f 1)), Int.ofNat_one, ← Distrib.right_distrib, Int.mul_one, ← Int.ofNat_add]

    have seteq : (monochromaticVicinity ⊤ 0 f 0) ∪ (monochromaticVicinity ⊤ 0 f 1) = ((⊤:SimpleGraph (Fin (M + N))).neighborFinset 0) := by
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
    rw [Int.ofNat_sub MNpos]
  -- NOTE Again, these lines should all be part of a single simp call but we get whnf timeout
    rw [Rat.add_def', Rat.coe_nat_num M, Rat.coe_nat_den M, Rat.coe_nat_num N, Rat.coe_nat_den N, Int.ofNat_one, ← Distrib.right_distrib, Int.mul_one, ← Int.ofNat_add, Nat.mul_one]
    rw [Rat.sub_def', Rat.one_den, Rat.one_num, Int.ofNat_one, Int.mul_one, Int.one_mul, Nat.mul_one, Rat.mkRat_one_num, Rat.mkRat_one_den, Int.ofNat_one]

  have mp := missing_pigeonhole (Exists.intro (0 : Fin 2) (Finset.mem_univ (0 : Fin 2))) (le_of_eq hgsum)
  rcases mp with ⟨a, _, gha⟩
  have floor0 :  ⌊mkRat 1 2⌋ = 0 := by simp; tauto
  fin_cases a <;> simp at gha <;> rw [Rat.add_comm] at gha <;>
  have leqNeighbor := Int.floor_mono gha <;> simp [floor0] at leqNeighbor
  · have cliquecases := monochromaticVicinity_Ramsey (RamseyMonotone RamseyM leqNeighbor)
    rcases cliquecases with ⟨S, Sclique⟩ |cliquecases
    use S, 0
    exact Sclique
    rcases cliquecases with ⟨i, ⟨S, Sclique⟩⟩
    use S, 1
    have ieq1 := notc Sclique.left (Fin.succ_ne_zero 0)
    simp [ieq1] at Sclique
    exact Sclique
  · have cliquecases := monochromaticVicinity_Ramsey (RamseyMonotone RamseyN leqNeighbor)
    rcases cliquecases with ⟨T, Tclique⟩ |cliquecases
    use T, 1
    exact Tclique
    rcases cliquecases with ⟨i, ⟨T, Tclique⟩⟩
    use T, 0
    have ineq1 := notc Tclique.left Fin.zero_ne_one
    simp [ineq1] at Tclique
    exact Tclique
  done

theorem Ramsey₂PropStrictIneq : ∀ {M N s t : ℕ}, Odd M → Odd N → Ramsey₂Prop M.succ s t.succ → Ramsey₂Prop N.succ s.succ t → Ramsey₂Prop (M + N).succ s.succ t.succ := by
  intros M N s t oddM oddN RamseyM RamseyN
  unfold Ramsey₂Prop RamseyProp
  simp
  intro f
  let g : Fin 2 → ℕ := (λ x ↦ 2 * (Finset.filter (λ e ↦ f e = x) (Finset.filter (fun e => ¬Sym2.IsDiag e) Finset.univ)).card)
  let h : Fin 2 → ℕ := ![(M + N).succ * M, (M + N).succ * N]
  have hgsum : Finset.univ.sum h = Finset.univ.sum g := by
    simp [Finset.univ_fin2]
    rw [← Nat.left_distrib, ← Nat.left_distrib]
    have filterdisj : Disjoint (Finset.filter (λ e ↦ f e = 0) (⊤ : SimpleGraph (Fin (M + N).succ)).edgeFinset) (Finset.filter (λ e ↦ f e = 1) (⊤ : SimpleGraph (Fin (M + N).succ)).edgeFinset) := by
      simp [Finset.disjoint_iff_ne]
      intros a _ fa0 b _ fb1
      by_contra h
      simp [h,fb1] at fa0
    simp at filterdisj
    rw [← Finset.card_union_eq filterdisj]
    have seteq : Finset.filter (fun e => f e = 0) (Finset.filter (fun e => ¬Sym2.IsDiag e) Finset.univ) ∪
    Finset.filter (fun e => f e = 1) (Finset.filter (fun e => ¬Sym2.IsDiag e) Finset.univ) =
    Finset.filter (fun e => ¬Sym2.IsDiag e) Finset.univ := by
      simp [Finset.Subset.antisymm_iff, Finset.subset_iff]
      apply And.intro
      intros _ xprop ; cases xprop <;> simp_all
      intros x xprop
      by_contra h
      simp [not_or,not0_eq1, xprop] at h

    rw [seteq, ← SimpleGraph.edgeFinset_top,  ← SimpleGraph.sum_degrees_eq_twice_card_edges]
    simp
  have mp := missing_pigeonhole (Exists.intro (0 : Fin 2) (Finset.mem_univ (0 : Fin 2))) (Nat.le_of_eq hgsum)
  rcases mp with ⟨a, ainuniv, gha⟩

  -- NOTEL: Maybe state this as ¬Even since we need to simplify later anyways?
  have cardodd : Odd (M + N).succ := by
    simp [Nat.even_add_one]
    simp at oddM oddN
    simp [Nat.even_add, oddM, oddN]

  have xoreven : ∀ {O : ℕ}, Odd O → Xor' (Even ((M + N).succ * O)) (Even (2 * (Finset.filter (λ (e : Sym2 (Fin (M + N).succ))↦ f e = a) (Finset.filter (fun e => ¬Sym2.IsDiag e) Finset.univ)).card)) := by
    intros O OddO
    right
    simp at OddO ⊢
    intro evenMul
    rw [Nat.even_mul] at evenMul
    rcases evenMul with absurd | absurd
    · simp at cardodd
      contradiction
    · contradiction

  have cardeq : ∀ (v : Fin (M + N).succ) (i : Fin 2), (Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M + N).succ)).Dart)↦ x.toProd.snd = v)
        (Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M + N).succ)).Dart)↦ f (Sym2.mk x.toProd) = i) Finset.univ)).card = (monochromaticVicinity (⊤ : SimpleGraph (Fin (M + N).succ)) v f i).card := by
    intro v i
    apply Finset.card_congr (λ (a : (⊤ : SimpleGraph (Fin (M + N).succ)).Dart) _ ↦ a.fst)
    · intro a
      simp [monochromaticVicinity]
      intros fi asndv
      have aprop := a.is_adj
      simp[asndv] at aprop
      simp[Ne.symm aprop]
      simp [Sym2.eq_swap, ← asndv]
      exact fi
    · intros _ _
      simp
      intros _ asndv _ bsndv abfst
      rw [SimpleGraph.Dart.ext_iff, Prod.ext_iff]
      simp [abfst, asndv, bsndv]
    · intro b
      simp [monochromaticVicinity]
      intros bnotv fvb0
      have bvAdj: (⊤ : SimpleGraph (Fin (M + N).succ)).Adj b v := by simp [Ne.symm, bnotv]
      use SimpleGraph.Dart.mk (b,v) bvAdj
      simp [Sym2.eq_swap, fvb0]

  fin_cases a <;> simp at gha
  · have ghalt := xor_even_le_implies_lt (xoreven oddM) gha
    simp at ghalt
    rw [← SimpleGraph.edgeFinset_top, dblcnt M N f 0] at ghalt
    have pghineq : (@Finset.univ (Fin (M + N).succ) _).card • M < ↑((Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M + N).succ)).Dart) ↦ f (Sym2.mk x.toProd) = 0) Finset.univ).card) := by simp [ghalt]
    have pgh := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (λ (e : (⊤ : SimpleGraph (Fin (M + N).succ)).Dart) _ ↦ Finset.mem_univ e.snd) pghineq
    rcases pgh with ⟨v, _, vprop⟩
    rw [cardeq] at vprop
    have cliquecases := monochromaticVicinity_Ramsey (RamseyMonotone RamseyM vprop)
    rcases cliquecases with ⟨S, Sclique⟩ | ⟨i, ⟨S, Sclique⟩⟩
    · use S, 0
      exact Sclique
    · use S, 1
      have ieq1 := notc Sclique.left (Fin.succ_ne_zero 0)
      simp [ieq1] at Sclique
      exact Sclique
  · have ghalt := xor_even_le_implies_lt (xoreven oddN) gha
    simp at ghalt
    rw [← SimpleGraph.edgeFinset_top, dblcnt M N f 1] at ghalt
    have pghineq : (@Finset.univ (Fin (M + N).succ) _).card • N < ↑((Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M + N).succ)).Dart) ↦ f (Sym2.mk x.toProd) = 1) Finset.univ).card) := by simp [ghalt]
    have pgh := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (λ (e : (⊤ : SimpleGraph (Fin (M + N).succ)).Dart) _ ↦ Finset.mem_univ e.snd) pghineq
    rcases pgh with ⟨v, _, vprop⟩
    rw [cardeq] at vprop
    have cliquecases := monochromaticVicinity_Ramsey (RamseyMonotone RamseyN vprop)
    rcases cliquecases with ⟨T, Tclique⟩ | ⟨i, ⟨T, Tclique⟩⟩
    · use T, 1
      exact Tclique
    · use T, 0
      have ieq1 := notc Tclique.left (Fin.succ_ne_zero 0).symm
      simp [ieq1] at Tclique
      exact Tclique
  done

theorem Ramsey₂Finite : ∀ s t : ℕ, { N : ℕ | Ramsey₂Prop N s t }.Nonempty := by
  suffices Ramsey₂FiniteAdditive : ∀ m : ℕ, ∀ s t, m = s + t → { N : ℕ | Ramsey₂Prop N s t }.Nonempty
  · intros s t
    simp [Ramsey₂FiniteAdditive (s + t) s t]
  · intro m
    induction m with
    | zero =>
      intros s t st
      rcases (Nat.eq_zero_of_add_eq_zero st.symm) with ⟨rfl, rfl⟩
      use 0
      simp [Ramsey₂Prop, RamseyProp]
      intro f
      use {}, 0
      simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, graphAtColor, Vector.get, List.nthLe]
    | succ m' ih =>
      intros s t h
      cases s with
      | zero =>
        use 0
        simp [Ramsey₂Prop, RamseyProp]
        intro f
        use {}, 0
        simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, graphAtColor, Vector.get, List.nthLe]
      | succ s =>
        cases t with
        | zero =>
          use 0
          simp [Ramsey₂Prop, RamseyProp]
          intro f
          use {}, 1
          simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, graphAtColor, Vector.get, List.nthLe]
        | succ t =>
          apply_fun Nat.pred at h
          simp at h
          have s1t : m' = s + t.succ := by simp [h, Nat.succ_add]
          have st1 : m' = s.succ + t := by simp [h, Nat.add_succ]
          rcases (ih s t.succ s1t) with ⟨S, Sprop⟩
          rcases (ih s.succ t st1) with ⟨T, Tprop⟩
          simp at Sprop Tprop
          cases Nat.eq_zero_or_eq_succ_pred (S + T) with
          | inl ST0 =>
            rcases (Nat.eq_zero_of_add_eq_zero ST0) with ⟨rfl, rfl⟩
            unfold Ramsey₂Prop at Sprop Tprop
            rcases (RamseyProp0 Sprop) with ⟨i, i0⟩
            fin_cases i <;> simp [Vector.get, List.nthLe] at i0
            · use 1
              simp [i0]
              apply Ramsey₂1Prop
          | inr STPos =>
            use S + T
            apply Ramsey₂PropIneq (by rw [STPos]; simp) <;> assumption

theorem Ramsey₂ToRamsey₂Prop : ∀ {N s t : ℕ}, Ramsey₂ s t = N → Ramsey₂Prop N s t := by
  intros N s t Ramsey
  simp [Ramsey₂] at Ramsey
  simp [← Ramsey]
  have RamseyMem := Nat.sInf_mem (Ramsey₂Finite s t)
  simp at RamseyMem
  exact RamseyMem

theorem Ramsey₂Ineq : ∀ s t : ℕ, 0 < Ramsey₂ s t.succ + Ramsey₂ s.succ t → Ramsey₂ s.succ t.succ ≤ Ramsey₂ s t.succ + Ramsey₂ s.succ t := by
  intros s t RPos
  have RamseyM := Nat.sInf_mem (Ramsey₂Finite s t.succ)
  have RamseyN := Nat.sInf_mem (Ramsey₂Finite s.succ t)
  apply Nat.sInf_le
  simp at RamseyM RamseyN
  apply Ramsey₂PropIneq <;> assumption

theorem Ramsey₂0 : ∀ {s : ℕ}, Ramsey₂ 0 s = 0 := by
  intro s
  unfold Ramsey₂
  simp [Nat.sInf_eq_zero]
  left
  unfold Ramsey₂Prop RamseyProp
  intros f
  use ∅, 0
  simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise]

theorem Ramsey₂Symm : ∀  {s t: ℕ}, Ramsey₂ s t = Ramsey₂ t s := by
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

theorem Ramsey₂StrictIneq : ∀ s t : ℕ, 0 < Ramsey₂ s t.succ + Ramsey₂ s.succ t → Even (Ramsey₂ s t.succ) → Even (Ramsey₂ s.succ t) → Ramsey₂ s.succ t.succ < Ramsey₂ s t.succ + Ramsey₂ s.succ t := by
  intros s t stPos evenM evenN
  have lt_or_eq := Decidable.lt_or_eq_of_le (Ramsey₂Ineq s t stPos)
  rcases lt_or_eq with lt | eq
  exact lt
  rcases (Nat.eq_zero_or_eq_succ_pred (Ramsey₂ s t.succ)) with Rst1 | Rst1succ
  · have Ramsey0 := Nat.sInf_mem (Ramsey₂Finite s t.succ)
    unfold Ramsey₂ at Rst1
    simp [Rst1] at Ramsey0
    unfold Ramsey₂Prop at Ramsey0
    rcases (RamseyProp0 Ramsey0) with ⟨i, s0⟩
    fin_cases i <;> simp [Vector.get, List.nthLe] at s0
    · cases t with
      | zero =>
        simp [s0, Ramsey₂0, Ramsey₂Symm, Ramsey₂0] at stPos
      | succ t =>
        simp [s0, Ramsey₂1] at evenN
  · rcases (Nat.eq_zero_or_eq_succ_pred (Ramsey₂ s.succ t)) with Rs1t | Rs1tsucc
    · have Ramsey0 := Nat.sInf_mem (Ramsey₂Finite s.succ t)
      unfold Ramsey₂ at Rs1t
      simp [Rs1t] at Ramsey0
      unfold Ramsey₂Prop at Ramsey0
      rcases (RamseyProp0 Ramsey0) with ⟨i, t0⟩
      fin_cases i <;> simp [Vector.get, List.nthLe] at t0
      · cases s with
        | zero =>
          simp [t0, Ramsey₂0, Ramsey₂Symm, Ramsey₂0] at stPos
        | succ s =>
          rw [Ramsey₂Symm, t0, Ramsey₂1] at evenM
          simp at evenM
    have R2 : Ramsey₂ s.succ t.succ = sInf { N | Ramsey₂Prop N s.succ t.succ } := by simp [Ramsey₂]
    rw [R2, Rst1succ, Nat.succ_add]
    apply Nat.lt_succ_of_le
    apply Nat.sInf_le
    simp
    rw [Rst1succ, Nat.succ_eq_add_one, Nat.even_add_one, ← Nat.odd_iff_not_even] at evenM
    rw [Rs1tsucc, Nat.succ_eq_add_one, Nat.even_add_one, ← Nat.odd_iff_not_even] at evenN
    have RamseyM : Ramsey₂Prop (Ramsey₂ s t.succ) s t.succ := by
      have RMem := Nat.sInf_mem (Ramsey₂Finite s t.succ)
      simp [Ramsey₂] at RMem ⊢
      exact RMem
    have RamseyN : Ramsey₂Prop (Ramsey₂ s.succ t) s.succ t := by
      have RMem := Nat.sInf_mem (Ramsey₂Finite s.succ t)
      simp [Ramsey₂] at RMem ⊢
      exact RMem
    rw [Rst1succ] at RamseyM
    rw [Rs1tsucc] at RamseyN
    have temp := Ramsey₂PropStrictIneq evenM evenN RamseyM RamseyN
    rw [← Nat.succ_add, ← Rst1succ] at temp
    have Rst1Pos := Nat.succ_pos (Nat.pred (Ramsey₂ s (Nat.succ t)))
    have Rs1tPos := Nat.succ_pos (Nat.pred (Ramsey₂ (Nat.succ s) t))
    rw [← Rst1succ] at Rst1Pos; rw [← Rs1tsucc] at Rs1tPos
    change 1 ≤ (Ramsey₂ s (Nat.succ t)) at Rst1Pos
    rw [Nat.pred_eq_sub_one, Rst1succ, ← Nat.add_sub_assoc (Rs1tPos) (Nat.succ (Nat.pred (Ramsey₂ s (Nat.succ t)))), Nat.succ_add_sub_one] at temp
    simp [temp]

theorem friendship_upper_bound_alt : Ramsey₂ 3 3 ≤ 6 := by
  have R33 := Ramsey₂Ineq 2 2
  rw [@Ramsey₂Symm 3 2, Ramsey₂2] at R33
  exact R33 (by simp)
  done

theorem Ramsey₂ByList : ∀ (N s t : ℕ), Ramsey₂Prop N s.succ t.succ ↔ (∀ (f : Sym2 (Fin N) → Fin 2), (∃ (l : List (Fin N)), l ∈ (List.finRange N).sublistsLen s.succ ∧ (List.Pairwise (λ u v ↦ (f s(u, v) )= 0) l)) ∨ (∃ (l : List (Fin N)), l ∈ (List.finRange N).sublistsLen t.succ ∧ (List.Pairwise (λ u v ↦ (f s(u, v)) = 1) l))) := by
  intros N s t
  unfold Ramsey₂Prop RamseyProp
  apply Iff.intro
  · intros h f
    simp [SimpleGraph.isNClique_iff,SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at h
    rcases h f with ⟨S, i,SProp⟩
    let Slist := Finset.sort instLEFin.le S
    have hs: Symmetric fun u v => f (Quot.mk (Sym2.Rel (Fin N)) (u, v)) = i := by
      unfold Symmetric
      simp[Sym2.eq_swap]
    fin_cases i; simp [Vector.head] at SProp hs; left; swap; simp [Vector.get, List.nthLe] at SProp hs; right;
    all_goals {
      use Slist
      apply And.intro
      simp only [List.mem_sublistsLen, List.sublist_iff_exists_fin_orderEmbedding_get_eq, Finset.length_sort instLEFin.le, SProp.right, and_true]
      let f' : Fin Slist.length → Fin N := λ (i: Fin Slist.length) ↦ Slist.get i
      let idxMap : Fin Slist.length → Fin (List.finRange N).length := (λ idx ↦
        let mappedIdx := f' idx;
        Fin.cast (List.length_finRange N).symm mappedIdx)
      have idxMapInj : Function.Injective idxMap := by
        unfold Function.Injective
        intros a₁ a₂
        intro h
        simp [Fin.cast, ← Fin.ext_iff, List.Nodup.get_inj_iff (Finset.sort_nodup instLEFin.le S)] at h
        exact h
      have idxOrdered : ∀ {a₁ a₂ : Fin Slist.length}, idxMap a₁ ≤ idxMap a₂ ↔ a₁ ≤ a₂ := by
        intros a₁ a₂
        simp[Fin.cast]
        apply Iff.intro
        · intro valCond
          cases a₁.decLe a₂ with
          | isTrue p => exact p
          | isFalse p =>
            simp at p
            have a₂lea₁ := List.Sorted.rel_get_of_lt (Finset.sort_sorted instLEFin.le S) p
            have a₂eqa₁ := le_antisymm valCond a₂lea₁
            rw [List.Nodup.get_inj_iff (Finset.sort_nodup instLEFin.le S)] at a₂eqa₁
            simp [a₂eqa₁] at p
        · intro idCond
          exact List.Sorted.rel_get_of_le (Finset.sort_sorted instLEFin.le S) idCond
      use { toFun := idxMap, inj' := idxMapInj, map_rel_iff' := idxOrdered }
      simp[Fin.cast]
      simp_all
      simp [← List.pairwise_iff_coe_toFinset_pairwise (Finset.sort_nodup instLEFin.le S) hs, Set.Pairwise]
      exact SProp.left
    }
  · intros RamseyProp f
    rcases (RamseyProp f) with ⟨l, lSubl, lPairwise⟩|⟨l, lSubl, lPairwise⟩
    use l.toFinset, 0
    have fSymm : Symmetric fun u v => f (Quot.mk (Sym2.Rel (Fin N)) (u, v)) = 0 := by
      unfold Symmetric
      simp[Sym2.eq_swap]
    swap
    use l.toFinset, 1
    have fSymm : Symmetric fun u v => f (Quot.mk (Sym2.Rel (Fin N)) (u, v)) = 1 := by
      unfold Symmetric
      simp[Sym2.eq_swap]
    all_goals{
      simp [SimpleGraph.isNClique_iff,SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor, Vector.get, List.nthLe]
      simp at lSubl
      have lNodup : l.Nodup := List.Nodup.sublist lSubl.left (List.nodup_finRange N)
      simp [← List.pairwise_iff_coe_toFinset_pairwise lNodup fSymm, Set.Pairwise] at lPairwise
      simp only[List.toFinset_card_of_nodup lNodup]
      intros
      simp_all
    }


theorem friendship : Ramsey₂ 3 3 = 6 := by
  unfold Ramsey₂
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  · simp
    apply And.intro
    · exact friendshipUpperbound
    · rw [Ramsey₂ByList, not_forall]
      use (λ (e : Sym2 (Fin 5)) ↦ if e ∈ ({s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0)}:Finset (Sym2 (Fin 5))) then 0 else 1)
      simp_arith

  · simp [Ramsey₂Prop]
    intros M N MleN Ramsey₂M
    exact RamseyMonotone Ramsey₂M MleN

theorem R43 : Ramsey₂ 4 3 = 9 := by
  unfold Ramsey₂
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  · simp
    apply And.intro
    · have Ramsey4 := Ramsey₂ToRamsey₂Prop (Ramsey₂2 3)
      rw [Ramsey₂PropSymm] at Ramsey4
      have Ramsey9 := Ramsey₂PropStrictIneq (by simp_arith) (by simp_arith) friendshipUpperbound Ramsey4
      exact Ramsey9
    · -- Proof 1
      -- rw [Ramsey₂ByList, not_forall]
      -- use (λ (e : Sym2 (Fin 8)) ↦ if e ∈ ({⟦(0, 1)⟧, ⟦(1, 2)⟧, ⟦(2, 3)⟧, ⟦(3, 4)⟧, ⟦(4, 5)⟧, ⟦(5, 6)⟧, ⟦(6, 7)⟧, ⟦(7, 0)⟧, ⟦(0, 4)⟧, ⟦(1, 5)⟧}:Finset (Sym2 (Fin 8))) then 1 else 0)
      -- simp
      -- Proof 2
      rw [Ramsey₂PropSymm, Ramsey₂GraphProp]
      exact R34
  · simp [Ramsey₂Prop]
    intros M N MleN Ramsey₂M
    exact RamseyMonotone Ramsey₂M MleN

theorem R53 : Ramsey₂ 5 3 = 14 := by
  unfold Ramsey₂
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  · simp
    apply And.intro
    · have Ramsey5 := Ramsey₂ToRamsey₂Prop (Ramsey₂2 4)
      rw [Ramsey₂PropSymm] at Ramsey5
      have Ramsey4 := Ramsey₂ToRamsey₂Prop (R43)
      have Ramsey14 := Ramsey₂PropIneq (by simp) Ramsey4 Ramsey5
      exact Ramsey14
    · rw [Ramsey₂PropSymm, Ramsey₂GraphProp]
      exact R35
  · simp [Ramsey₂Prop]
    intros M N MleN Ramsey₂M
    exact RamseyMonotone Ramsey₂M MleN

theorem R44 : Ramsey₂ 4 4 = 18 := by
  unfold Ramsey₂
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  · simp
    apply And.intro
    · have Ramsey34 := Ramsey₂ToRamsey₂Prop (R43)
      rw [Ramsey₂PropSymm] at Ramsey34
      have Ramsey43 := Ramsey₂ToRamsey₂Prop (R43)
      have Ramsey18 := Ramsey₂PropIneq (by simp)  Ramsey34 Ramsey43
      exact Ramsey18
    · rw [Ramsey₂GraphProp]
      exact R44'
  · simp [Ramsey₂Prop]
    intros M N MleN Ramsey₂M
    exact RamseyMonotone Ramsey₂M MleN

theorem Ramsey₂_binomial_coefficient_ineq : ∀ s t : ℕ, Ramsey₂ s.succ t.succ
≤ Nat.choose (s + t) s := by
  intros s t

  induction' s with s' ihp₁ generalizing t
  simp [Ramsey₂1 t]

  induction' t with t' ihp₂
  rw [Ramsey₂Symm]
  simp [Ramsey₂1 s'.succ]
  transitivity Ramsey₂ s'.succ t'.succ.succ + Ramsey₂ s'.succ.succ t'.succ
  apply Ramsey₂Ineq s'.succ t'.succ

  by_contra h
  simp [not_or] at h
  have RamseyMem := Nat.sInf_mem (Ramsey₂Finite (Nat.succ s') (Nat.succ (Nat.succ t')))
  unfold Ramsey₂ at h
  rw [h.left] at RamseyMem
  simp [Ramsey₂Prop] at RamseyMem
  rcases RamseyProp0 RamseyMem with ⟨i, i0⟩
  fin_cases i <;> simp [Vector.get, List.nthLe] at i0

  have temp₁: Ramsey₂ s'.succ t'.succ.succ + Ramsey₂ s'.succ.succ t'.succ
  ≤ (s' + t'.succ).choose s' + (s'.succ + t').choose s'.succ := by
    apply add_le_add
    exact ihp₁ t'.succ
    exact ihp₂

  have temp₂ :(s'.succ + t'.succ).choose s'.succ =
  (s' + t'.succ).choose s' + (s'.succ + t').choose s'.succ
  := by simp [Nat.succ_add, Nat.add_succ,Nat.choose_succ_succ]

  rw [temp₂]
  exact temp₁
  done
