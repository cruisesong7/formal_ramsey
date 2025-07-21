import Mathlib.Data.Vector.Mem

import FormalRamsey.Ramsey2Color
import FormalRamsey.G6Visualizer

open Ramsey
open List

theorem RamseyPropSymm : ∀ {N k : ℕ} {s s' : List.Vector ℕ k.succ}, RamseyProp N s → s.toList ~ s'.toList → RamseyProp N s' := by
  intros N k s s' RamseyN sPerm
  unfold RamseyProp at RamseyN ⊢
  intro f
  cases s
  next s sLength =>
    cases s'
    next s' s'Length =>
      simp [Vector.toList] at sPerm
      rcases (bijection_of_List_perm sPerm.symm) with ⟨μ, ⟨μBij, μProp⟩⟩
      rcases (RamseyN (λ e ↦ Fin.cast sLength (μ (Fin.cast s'Length.symm (f e))))) with ⟨S, i, Sclique⟩
      simp [List.Vector.get] at Sclique
      haveI : Nonempty (Fin s'.length) := by simp [s'Length]; infer_instance
      use S, Fin.cast s'Length ((Function.invFun μ) (Fin.cast sLength.symm i))
      cases Sclique
      next Sclique Scard =>
        simp [List.Vector.get] at Scard ⊢
        constructor
        · simp [graphAtColor, SimpleGraph.isClique_iff, Set.Pairwise] at Sclique ⊢
          intro u uIns v vIns uneqv
          apply And.intro
          · exact uneqv
          · have fuv := (Sclique uIns vIns uneqv).right
            apply_fun (Fin.cast sLength.symm) at fuv
            apply_fun (Function.invFun μ) at fuv
            simp at fuv
            have fuvcomp := congr_fun (Function.invFun_comp μBij.left) (Fin.cast s'Length.symm (f s(u, v)))
            simp [Function.comp] at fuvcomp
            rw [fuvcomp] at fuv
            simp [← fuv]
        · rw [Scard]
          have si := μProp (Function.invFun μ (Fin.cast sLength.symm i))
          have μinv := Function.rightInverse_invFun μBij.right
          rw [Function.rightInverse_iff_comp] at μinv
          have μinvi := congr_fun μinv (Fin.cast sLength.symm i)
          unfold Function.comp at μinvi
          simp [μinvi] at si
          simp_rw [si]

theorem RamseyFinite : ∀ {k : ℕ} (s : List.Vector ℕ k.succ), { N : ℕ | RamseyProp N s }.Nonempty := by
  intro k
  cases k with
  | zero =>
    intro s
    use s.head.succ
    simp [RamseyProp]
    intro f
    use (Finset.univ.map Fin.castSuccEmb), 0
    constructor <;>  simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor]
    intros
    simpa [eq_iff_true_of_subsingleton]
  | succ k =>
    induction k with
    | zero =>
      intro s
      cases s
      next s sLength =>
        rw [List.length_eq_two] at sLength
        rcases sLength with ⟨a, b, sEq⟩
        rcases (Ramsey₂Finite a b) with ⟨R, RProp⟩
        simp [Ramsey₂Prop] at RProp
        use R
        simp [sEq]
        exact RProp
    | succ k' ih =>
      intro s
      rcases (ih s.tail) with ⟨R, RProp⟩
      rcases (Ramsey₂Finite s.head R) with ⟨R', R'Prop⟩
      simp at RProp R'Prop
      simp [Ramsey₂Prop, RamseyProp] at R'Prop
      use R'
      simp [RamseyProp]
      intro f
      rcases (R'Prop (λ e ↦ if f e = 0 then 0 else 1)) with ⟨R'', i, R''Prop⟩
      fin_cases i
      · use R'', 0
        simp [graphAtColor] at R''Prop ⊢
        cases R''Prop
        next R''Clique R''Card =>
          constructor
          · simp [SimpleGraph.IsClique, Set.Pairwise] at R''Clique ⊢
            intros x xinR y yinR xneqy
            cases (R''Clique xinR yinR xneqy)
            next _ notnot =>
              simp [xneqy]
              exact notnot
          · exact R''Card
      · simp at R''Prop
        unfold RamseyProp at RProp
        rcases R''Prop with ⟨R''Clique, R''Card⟩
        have Rcard : (Finset.univ : Finset (Fin R)).card = R''.card := by
          simp [List.Vector.get] at R''Card
          simp [R''Card]
        have cardBij := bijection_of_eq_card Rcard
        cases cardBij with
        | inl finREmpty =>
          have R0 : R = 0 := by
            cases Nat.decEq R 0 with
            | isTrue p =>
              exact p
            | isFalse p =>
              haveI : NeZero R := ⟨p⟩
              have mem0 := Finset.mem_univ (0 : Fin R)
              simp [finREmpty.left] at mem0
          rcases (RProp (λ _ ↦ 0)) with ⟨S, i, SNclique⟩
          simp [SimpleGraph.isNClique_iff] at SNclique
          have Sempty : S = ∅ := by
            cases Finset.eq_empty_or_nonempty S with
            | inl _ => assumption
            | inr Snonempty =>
              rcases Snonempty with ⟨⟨s, sLt0⟩, _⟩
              simp [R0] at sLt0
          simp [Sempty] at SNclique
          use ∅, i.succ
          simp [← SNclique, SimpleGraph.isNClique_iff]
        | inr vertexMapEx =>
          rcases vertexMapEx with ⟨vmap, vmapBij⟩
          have fneq0 : ∀ {e : Sym2 (Fin R)}, ¬e.IsDiag → f (e.map (λ v ↦ (vmap (Subtype.mk v (Finset.mem_univ v ))).val)) ≠ 0 := by
            intros e eNotDiag feq0
            rcases (Quot.exists_rep e) with ⟨⟨u, v⟩, uvProp⟩
            simp [← uvProp] at eNotDiag
            simp [SimpleGraph.isClique_iff, Set.Pairwise] at R''Clique
            have vmapneq : ¬(vmap (Subtype.mk u (Finset.mem_univ u))).val = (vmap (Subtype.mk v (Finset.mem_univ v))).val := by
              intro vmapeq
              rw [← Subtype.ext_iff] at vmapeq
              have uvEq := vmapBij.left vmapeq
              simp at uvEq
              contradiction
            have cliqueInfo := R''Clique (vmap (Subtype.mk u (Finset.mem_univ u))).property (vmap (Subtype.mk v (Finset.mem_univ v))).property vmapneq
            simp [graphAtColor] at cliqueInfo
            rcases cliqueInfo with ⟨_, trouble⟩
            simp [← uvProp] at feq0
            contradiction
          have exClique := RProp (λ (e : Sym2 (Fin R)) ↦ match (Sym2.IsDiag.decidablePred (Fin R) e) with
  | isTrue p => 0
  | isFalse p => (f (e.map (λ v ↦ (vmap (Subtype.mk v (Finset.mem_univ v))).val))).pred (fneq0 p))
          rcases exClique with ⟨S, i, Sclique⟩
          let vmap' := λ v ↦ (vmap (Subtype.mk v (Finset.mem_univ v))).val
          have vmapInj : Function.Injective vmap' := by
            simp [Function.Injective]
            intros a₁ a₂ vmapa₁a₂
            rw [← Subtype.ext_iff] at vmapa₁a₂
            exact Subtype.ext_iff.mp (vmapBij.left vmapa₁a₂)
          let vmapEmb : Function.Embedding (Fin R) (Fin R') := ⟨vmap', vmapInj⟩
          use S.map vmapEmb, i.succ
          rcases Sclique with ⟨Sclique, Scard⟩
          constructor
          · simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor, vmapEmb, vmap'] at Sclique ⊢
            intros x xinS y yinS xneqy
            apply And.intro
            · exact xneqy
            · rw [← Subtype.ext_iff, ← ne_eq, Function.Injective.ne_iff vmapBij.left, ne_eq, Subtype.mk_eq_mk] at xneqy
              have fVal := (Sclique xinS yinS xneqy).right
              split at fVal
              next _ h _ =>
                simp at h
                contradiction
              next =>
                rw [Fin.pred_eq_iff_eq_succ] at fVal
                exact fVal
          · simp at Scard ⊢
            exact Scard

def Ramsey {k : ℕ} (s : List.Vector ℕ k.succ) : ℕ := Nat.find (RamseyFinite s)

-- TODO: This could be generalized into a function suitable for the Fin namespace
def nonzero_mapper {N k : ℕ} {f : Sym2 (Fin N) → Fin k.succ.succ} (fPos : ∀ {e}, ¬e.IsDiag → f e ≠ 0) : Sym2 (Fin N) → Fin k.succ := λ e ↦ match Sym2.IsDiag.decidablePred (Fin N) e with
  | isTrue _ => 0
  | isFalse p => (f e).pred (λ fe0 ↦ fPos p fe0)

theorem Ramsey1Prop : ∀ {k : ℕ} (N : ℕ) (s : List.Vector ℕ k.succ), RamseyProp N.succ (1 ::ᵥ s) := by
  simp [RamseyProp]
  intros
  use {0}, 0
  constructor
  · simp [SimpleGraph.isClique_iff, Set.Pairwise]
  · simp [Vector.get_zero]

theorem Ramsey1 : ∀ {k : ℕ} (s : List.Vector ℕ k.succ), Ramsey (1 ::ᵥ s) ≤ 1 := by
  intro _ s
  simp [Ramsey]
  have oneIns : 1 ∈ {N | RamseyProp N (1 ::ᵥ s)} := by simp [Ramsey1Prop]
  simp at oneIns
  use 1

theorem RamseyProp2 : ∀ {k N : ℕ} {s : List.Vector ℕ k.succ}, RamseyProp N s ↔ RamseyProp N (2 ::ᵥ s) := by
  intros k N s
  apply Iff.intro
  · intro RamseyN
    simp [RamseyProp] at RamseyN ⊢
    intro f
    by_cases h: (∃ u v, u ≠ v ∧ f s(u, v) = 0)
    · rcases h with ⟨u, v, fuv0⟩
      use {u, v}, 0
      constructor
      · simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor, fuv0.left, fuv0.left.symm, Sym2.eq_swap, fuv0.right]
      · simp [Finset.card_eq_two]
        use u, v
        simp [fuv0.left]
    · simp at h
      have fProp : ∀ {e}, ¬e.IsDiag → f e ≠ 0 := by
        intros e eNotDiag
        rcases (Quot.exists_rep e) with ⟨⟨u, v⟩, euv⟩
        rw [← euv] at eNotDiag ⊢
        simp at eNotDiag
        exact (h u v eNotDiag)
      let f' := nonzero_mapper fProp
      rcases (RamseyN f') with ⟨S, i, Sclique⟩
      use S, i.succ
      rw [SimpleGraph.isNClique_iff] at Sclique
      rcases Sclique with ⟨Sclique, Scard⟩
      constructor
      · simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor, nonzero_mapper] at Sclique ⊢
        intros u uinS v vinS uneqv
        apply And.intro
        · exact uneqv
        · have fmapped := (Sclique uinS vinS uneqv).right
          simp [f', nonzero_mapper] at fmapped
          split at fmapped
          next _ h _ =>
            simp at h
            contradiction
          next =>
            simp [← fmapped]
      · simp [Scard]
  · unfold RamseyProp
    intro Ramsey2s
    intro f
    rcases (Ramsey2s (λ i ↦ (f i).succ)) with ⟨S, Sprop⟩
    rw [Fin.exists_fin_succ] at Sprop
    cases Sprop with
    | inl Sprop =>
      simp at Sprop
      rcases Sprop with ⟨Sclique, Scard⟩
      simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at Sclique
      simp [Finset.card_eq_two] at Scard
      rcases Scard with ⟨u, v, uneqv, Suv⟩
      simp [uneqv, Suv, Fin.succ_ne_zero] at Sclique
    | inr Sprop =>
      simp at Sprop
      rcases Sprop with ⟨i, Sclique, Scard⟩
      use S, i
      constructor
      · simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at Sclique ⊢
        assumption
      · assumption

def increaseVector {k : ℕ} (s : List.Vector ℕ k) : List.Vector ℕ k := List.Vector.ofFn (λ i ↦ (s.get i).succ)

def increaseVectorExcept {k : ℕ} (s : List.Vector ℕ k) (i : Fin k) : List.Vector ℕ k := List.Vector.ofFn (λ j ↦ if i = j then s.get i else (s.get j).succ)

theorem RamseyPropIneq : ∀ {k : ℕ} (M : List.Vector ℕ k.succ.succ) (s : List.Vector ℕ k.succ.succ), (∀ (i : Fin k.succ.succ), RamseyProp (M.get i).succ (increaseVectorExcept s i)) → RamseyProp M.toList.sum.succ.succ (increaseVector s) := by
  intros k M s RamseyM f
  let g : Fin k.succ.succ → ℚ := λ i ↦ ↑(M.get i) + mkRat 1 k.succ.succ
  let h : Fin k.succ.succ → ℚ := λ c ↦ (((⊤ : SimpleGraph (Fin M.toList.sum.succ.succ)).neighborFinset 0).filter (λ v : Fin M.toList.sum.succ.succ ↦ f s(0, v) = c)).card
  have ghsum : Finset.univ.sum g = Finset.univ.sum h := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Rat.natCast_eq_divInt, ← Int.natCast_one, Rat.divInt_ofNat, Rat.mkRat_mul_mkRat, Nat.mul_comm, Rat.mkRat_mul_left k.succ.succ_ne_zero, Rat.mkRat_one]
    simp
    trans ↑((⊤ : SimpleGraph (Fin M.toList.sum.succ.succ)).neighborFinset 0).card
    · simp [← vector_list_finset_sum]
    · trans ↑(Finset.sum Finset.univ (λ x ↦ (Finset.filter (λ v ↦ f s(0, v) = x) ((⊤ : SimpleGraph (Fin M.toList.sum.succ.succ)).neighborFinset 0)).card))
      · rw [Nat.cast_inj]
        have partCard : ∀ {n m : ℕ} (f' : Sym2 (Fin n.succ) → Fin m.succ), Finset.univ.sum (λ x ↦ (((⊤ : SimpleGraph (Fin n.succ)).neighborFinset 0).filter (λ v ↦ f' s(0, v) = x)).card) = ((⊤ : SimpleGraph (Fin n.succ)).neighborFinset 0).card := by
          intro n
          cases n with
          | zero => simp [Finset.eq_empty_iff_forall_notMem]; decide
          | succ n' =>
            simp
            intro m f'
            let partition : Finset (Finset (Fin n'.succ.succ)) := Finset.univ.image (λ x ↦ ((⊤ : SimpleGraph (Fin n'.succ.succ)).neighborFinset 0).filter (λ v ↦ f' s(0, v) = x))
            have partitionPwDisj : Set.PairwiseDisjoint ↑partition (@id (Finset (Fin n'.succ.succ))) := by
              unfold Set.PairwiseDisjoint Set.Pairwise _root_.Disjoint id
              intros x xinPart y yinPart xneqy
              simp only [partition, List.coe_toFinset, List.mem_ofFn] at xinPart yinPart
              simp [Function.onFun_apply] at xinPart yinPart ⊢
              intros a ainx ainy
              rcases xinPart with ⟨x', xProp⟩
              rcases yinPart with ⟨y', yProp⟩
              rw [← xProp] at ainx
              rw [← yProp] at ainy
              rw [Finset.subset_iff] at ainx ainy
              rw [Finset.eq_empty_iff_forall_notMem]
              intros b bina
              have binx := ainx bina
              have biny := ainy bina
              simp at binx biny
              have x'eqy' := Eq.trans binx.right.symm biny.right
              rw [x'eqy'] at xProp
              have xeqy := Eq.trans xProp.symm yProp
              contradiction
            have partitionSupParts : partition.sup id = ((⊤ : SimpleGraph (Fin n'.succ.succ)).neighborFinset 0) := by
              apply subset_antisymm <;> rw [Finset.subset_iff]
              · intros v vinSup
                simp only [Finset.mem_sup, id] at vinSup
                rcases vinSup with ⟨a, ⟨aProp, vina⟩⟩
                simp [partition] at aProp
                rcases aProp with ⟨i, aProp⟩
                simp [← aProp] at vina ⊢
                exact vina.left
              · intros v vneq0
                simp only [Finset.mem_sup, id]
                use ((⊤ : SimpleGraph (Fin n'.succ.succ)).neighborFinset 0).filter (λ u ↦ f' s(0, u) = f' s(0, v))
                simp [partition] at vneq0 ⊢
                exact vneq0
            let parted : Finset.FinpartitionWithEmpty ((⊤ : SimpleGraph (Fin n'.succ.succ)).neighborFinset 0) := ⟨partition, partitionPwDisj, partitionSupParts⟩
            have partedSum := parted.sum_card_parts_with_empty
            simp at partedSum
            rw [Finset.sum_image_vanishing] at partedSum
            · exact partedSum
            · simp
              intros x y filtereq filternonempty
              rw [← ne_eq, ← Finset.nonempty_iff_ne_empty] at filternonempty
              rcases filternonempty with ⟨u, uinxFilter⟩
              have uinyFilter := uinxFilter
              rw [filtereq] at uinyFilter
              simp at uinxFilter uinyFilter
              exact Eq.trans uinxFilter.right.symm uinyFilter.right
        have partRw := partCard f
        simp at partRw ⊢
        -- NOTE: Fixing the ghsum lemma made the reasoning above be reversed so here we need .symm
        exact partRw.symm
      · simp [h]
  have mp := Finset.exists_le_of_sum_le (Exists.intro (0 : Fin k.succ.succ) (Finset.mem_univ 0)) (le_of_eq ghsum)
  rcases mp with ⟨a, _, gha⟩
  simp at gha
  rw [Rat.add_comm] at gha
  have ceilOne : ⌈mkRat 1 k.succ.succ⌉ = 1 := by
    rw [Int.ceil_eq_iff]
    apply And.intro
    · simp [← Rat.num_pos, Rat.mkRat_num_one]
    · rw [← Rat.mkRat_one, Rat.le_def, Rat.mkRat_den_one, Rat.mkRat_num_one, Rat.mkRat_num_one, Rat.mkRat_den_one, Int.one_mul, Int.one_mul, Nat.cast_le]
      simp +arith
  have MleqNeighbora := Int.ceil_mono gha
  simp [ceilOne] at MleqNeighbora
  rw [Int.add_comm, Int.ofNat_add_one_out, Nat.cast_le] at MleqNeighbora
  have cliqueCases := monochromaticVicinity_Ramsey (RamseyMonotone (RamseyM a) MleqNeighbora)
  cases cliqueCases with
  | inl cliqueCase =>
    rcases cliqueCase with ⟨S, Sclique⟩
    use S, a
    rw [SimpleGraph.isNClique_iff] at Sclique
    rcases Sclique with ⟨Sclique, Scard⟩
    constructor
    · simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at Sclique ⊢
      exact Sclique
    · simp [increaseVector, increaseVectorExcept] at Scard ⊢
      exact Scard
  | inr cliqueCase =>
    rcases cliqueCase with ⟨b, S, bneqa, Sclique⟩
    use S, b
    rw [SimpleGraph.isNClique_iff] at Sclique
    rcases Sclique with ⟨Sclique, Scard⟩
    constructor
    · simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at Sclique ⊢
      exact Sclique
    · simp [increaseVector, increaseVectorExcept, bneqa.symm] at Scard ⊢
      exact Scard

theorem RamseyToRamseyProp : ∀ {N k : ℕ} {s : List.Vector ℕ k.succ}, Ramsey s = N → RamseyProp N s := by
  intros N k s R
  unfold Ramsey at R
  rw [← R]
  apply Nat.find_spec (RamseyFinite s)

theorem Ramsey2 : ∀ {k : ℕ} (s : List.Vector ℕ k.succ), Ramsey s = Ramsey (2 ::ᵥ s) := by
  intros k s
  apply Nat.find_congr'
  intro n
  simp
  exact RamseyProp2

lemma RamseyPropG6Partition : ∀ {N r : ℕ} {s : List.Vector ℕ r.succ}, (∃ (V : List.Vector String r.succ) (VProp : ∀ {s : String}, s ∈ V.toList → N = (readG6Header s).toNat), (∀ (i : Fin r.succ), (readG6 (V.get i)).CliqueFree (s.get i)) ∧ (∀ (u v : Fin N), u ≠ v → ∃ (i : Fin r.succ), (readG6 (V.get i)).Adj (Fin.cast (VProp (V.get_mem i)) u) (Fin.cast (VProp (V.get_mem i)) v))) → ¬(RamseyProp N s) := by
  intros N r s exProp
  rcases exProp with ⟨V, Vheader, ⟨VcliqueFree, Vunique⟩⟩
  simp [RamseyProp]
  use (λ e ↦ match Fin.find (λ i ↦ e.map (Fin.cast (Vheader (V.get_mem i))) ∈ (readG6 (V.get i)).edgeSet) with
  | some r => r
  | none => 0)
  intros S i SNClique
  simp [graphAtColor] at SNClique
  -- NOTE: Don't we have some other mapper from Fin N to Fin M when N = M somewhere?
  have NotSNClique := VcliqueFree i (S.map (Fin.castOrderIso (Vheader (V.get_mem i))).toOrderEmbedding.toEmbedding)
  rw [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff] at SNClique NotSNClique
  rw [not_and] at NotSNClique
  suffices SMapClique : Set.Pairwise (S.map (Fin.castOrderIso (Vheader (V.get_mem i))).toOrderEmbedding.toEmbedding).toSet (readG6 (V.get i)).Adj by
    have absurd := NotSNClique SMapClique
    simp at absurd
    exact absurd SNClique.right
  simp [Set.Pairwise] at SNClique ⊢
  intros u uinS v vinS uneqv
  simp [Fin.ext_iff] at uneqv
  rw [← Fin.ext_iff] at uneqv
  have uvCases := (SNClique.left uinS vinS uneqv).right
  split at uvCases
  next j findSome =>
    simp [Fin.find_eq_some_iff] at findSome
    rw [uvCases] at findSome
    exact findSome.left
  next findNone =>
    simp [Fin.find_eq_none_iff] at findNone
    rcases (Vunique u v uneqv) with ⟨j, jProp⟩
    cases (findNone j) jProp

def castGraph {M N : ℕ} (MeqN : M = N) (G : SimpleGraph (Fin N)) : SimpleGraph (Fin M) := {
  Adj := λ u v ↦ G.Adj (Fin.cast MeqN u) (Fin.cast MeqN v)
  symm := λ _ _ uvAdj ↦  G.symm uvAdj
  loopless := λ _ vvAdj ↦  G.loopless _ vvAdj
}

set_option maxHeartbeats 4000000

open ProofWidgets

namespace List.Vector

-- We need to teach Lean how to count to 3
@[simp]
lemma get_cons_cons_one {α : Type} (a b : α) (v : List.Vector α n) : List.Vector.get (a ::ᵥ b ::ᵥ v) 1 = b := by
  have one : 1 = (0 : Fin v.length.succ).succ := by simp
  rw [one, get_cons_succ, get_zero]
  rfl

@[simp]
lemma get_cons_cons_cons_two {α : Type} (a b c : α) (v : List.Vector α n) : List.Vector.get (a ::ᵥ b ::ᵥ c ::ᵥ v) 2 = c := by
  have two : 2 = (0 : Fin v.length.succ).succ.succ := by simp
  rw [two, get_cons_succ, get_cons_succ, get_zero]
  rfl

end List.Vector

-- NOTE: Maybe a theorem like Rleq should become the standard theorem
theorem R333 : Ramsey (3 ::ᵥ 3 ::ᵥ 3 ::ᵥ Vector.nil) = 17 := by
  simp [Ramsey]
  rw [Nat.find_upward_closed_eq_succ_iff (RamseyFinite (3 ::ᵥ 3 ::ᵥ 3 ::ᵥ Vector.nil))]
  apply And.intro
  · simp [List.Vector.ofFn]
    apply RamseyPropIneq (5 ::ᵥ 5 ::ᵥ 5 ::ᵥ Vector.nil) (2 ::ᵥ 2 ::ᵥ 2 ::ᵥ Vector.nil)
    intro i
    have R33 := friendship
    simp [Ramsey₂, Ramsey₂Prop] at R33
    have Ramsey233 := RamseyToRamseyProp (Ramsey2 (List.Vector.ofFn ![3, 3])).symm
    simp [Ramsey, R33] at Ramsey233
    fin_cases i <;> simp [increaseVectorExcept, List.Vector.ofFn, List.Vector.get]
    · exact Ramsey233
    · have vecPerm : (2 ::ᵥ 3 ::ᵥ 3 ::ᵥ Vector.nil).toList ~ (3 ::ᵥ 2 ::ᵥ 3 ::ᵥ Vector.nil).toList := by decide
      apply RamseyPropSymm Ramsey233 vecPerm
    · have vecPerm : (2 ::ᵥ 3 ::ᵥ 3 ::ᵥ Vector.nil).toList ~ (3 ::ᵥ 3 ::ᵥ 2 ::ᵥ Vector.nil).toList := by decide
      apply RamseyPropSymm Ramsey233 vecPerm
  · simp
    apply RamseyPropG6Partition
    let V : List.Vector String 3 := "O_k_ClSCDD`S[_`DkIa[_" ::ᵥ "OWBYaAJIaOQJ@SMOOPX`S" ::ᵥ "OFODXO_pWiK_aJOiBcCAJ" ::ᵥ Vector.nil
    with_panel_widgets [SelectionPanel]
    have VProp : ∀ {s : String}, s ∈ V.toList → 16 = (readG6Header s).toNat := by decide
    use V, VProp
    apply And.intro
    · intro i
      fin_cases i <;> simp +arith [V, SimpleGraph.CliqueFree] <;> intros S SNClique <;> rw [← SimpleGraph.mem_cliqueFinset_iff] at SNClique
      · have myReplace : (readG6 (("O_k_ClSCDD`S[_`DkIa[_" ::ᵥ "OWBYaAJIaOQJ@SMOOPX`S" ::ᵥ "OFODXO_pWiK_aJOiBcCAJ" ::ᵥ Vector.nil).get 0)).cliqueFinset 3 = ∅ := by
          rw [← @exists_eq_left String (λ s ↦ (readG6 s).cliqueFinset 3 = ∅)]
          use "O_k_ClSCDD`S[_`DkIa[_"
          apply And.intro
          · simp
          · native_decide
        simp [myReplace] at SNClique
      · have myReplace : (readG6 (("O_k_ClSCDD`S[_`DkIa[_" ::ᵥ "OWBYaAJIaOQJ@SMOOPX`S" ::ᵥ "OFODXO_pWiK_aJOiBcCAJ" ::ᵥ Vector.nil).get 1)).cliqueFinset 3 = ∅ := by
          rw [← @exists_eq_left String (λ s ↦ (readG6 s).cliqueFinset 3 = ∅)]
          use "OWBYaAJIaOQJ@SMOOPX`S"
          apply And.intro
          · simp [List.Vector.get]
          · native_decide
        simp [myReplace] at SNClique
      · have myReplace : (readG6 (("O_k_ClSCDD`S[_`DkIa[_" ::ᵥ "OWBYaAJIaOQJ@SMOOPX`S" ::ᵥ "OFODXO_pWiK_aJOiBcCAJ" ::ᵥ Vector.nil).get 2)).cliqueFinset 3 = ∅ := by
          rw [← @exists_eq_left String (λ s ↦ (readG6 s).cliqueFinset 3 = ∅)]
          use "OFODXO_pWiK_aJOiBcCAJ"
          apply And.intro
          · simp
          · native_decide
        simp [myReplace] at SNClique
    · intros u v uneqv
      suffices vecSup : sSup { castGraph (VProp (V.get_mem i)) (readG6 (V.get i)) | i : Fin 3 } = ⊤ by
        have uvAdj : (⊤ : SimpleGraph (Fin 16)).Adj u v := by simp [uneqv]
        rw [← vecSup] at uvAdj
        simp at uvAdj
        rcases uvAdj with ⟨i, iProp⟩
        simp [castGraph] at iProp
        use i
      rw [SimpleGraph.ext_iff]
      simp only [castGraph, readG6]
      ext x y
      simp
      rw [Fin.ext_iff, Fin.exists_fin_succ, Fin.exists_fin_succ, Fin.exists_fin_succ]
      simp
      fin_cases x <;> fin_cases y <;> dsimp <;> norm_num <;> native_decide
  · intros _ _ kleq kRamsey
    simp at kRamsey ⊢
    exact RamseyMonotone kRamsey kleq
