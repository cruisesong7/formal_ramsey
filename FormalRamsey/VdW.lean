import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Group.Fin.Basic
-- NOTE: In the future this should change to the next import in comments (see mathlib4:eb486ff)
import Mathlib.Algebra.GroupPower.IterateHom
-- import Mathlib.Algebra.Group.Basic

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Sat.FromLRAT
import Mathlib.Tactic.Linarith
-- import Mathlib.Tactic.SlimCheck

-- import FormalRamsey.PickTactic
import Mathlib.Tactic.WLOG

import FormalRamsey.Fin2

structure Arithprog (α : Type) (length : ℕ) [HAdd α α α] where (start : α) (diff : α)

instance {α : Type} {l : ℕ} [HAdd α α α] : Membership α (Arithprog α l) := ⟨λ s a => ∃ (i : Fin l), a = Nat.iterate (λ j : α => j + s.diff) i.val s.start⟩

def vdWProp (N : ℕ) (k : ℕ) (r : ℕ) : Prop := ∀ f : ℕ → Fin r.succ, ∃ (s : Arithprog ℕ k) (c : Fin r.succ), s.diff > 0 ∧ (∀ e ∈ s, e < N ∧ f e = c)

lemma vdWMonotone : ∀ m k r, vdWProp m k r → ∀ n, m ≤ n → vdWProp n k r := by
  unfold vdWProp
  intros m k r vdWM n nLEm f
  rcases (vdWM f) with ⟨s, c, sDiff, eProp⟩
  use s, c
  apply And.intro
  · exact sDiff
  · intros e eIns
    rcases (eProp e eIns) with ⟨eLTn, eColor⟩
    apply And.intro
    · apply lt_of_lt_of_le eLTn nLEm
    · exact eColor

lemma vdWProp2 : ∀ r : ℕ, vdWProp r.succ.succ 2 r := by
  unfold vdWProp
  intros r f
  let g : Fin r.succ.succ → Fin r.succ := λ n : Fin r.succ.succ ↦ f n.val
  have finrrsucc : Fintype.card (Fin r.succ) • 1 < Fintype.card (Fin r.succ.succ) := by simp
  rcases (Fintype.exists_lt_card_fiber_of_mul_lt_card g finrrsucc) with ⟨y, yProp⟩
  rw [Finset.one_lt_card_iff] at yProp
  rcases yProp with ⟨a, b, aProp, bProp, aneb⟩
  simp at aProp bProp
  wlog aLtb : a.val < b.val
  · rw [Nat.not_lt, Nat.le_iff_lt_or_eq] at aLtb
    cases aLtb with
    | inl bLta =>
      apply this r f finrrsucc y b a aneb.symm bProp aProp bLta
    | inr beqa =>
      rw [← Fin.ext_iff] at beqa
      cases (aneb.symm beqa)
  use { start := a, diff := b - a }, y
  simp
  apply And.intro
  · assumption
  · intros e eins
    rcases eins with ⟨i, rfl⟩
    simp
    fin_cases i <;> simp
    · exact aProp
    · simpa [← Nat.add_sub_assoc (Nat.le_of_lt aLtb)]

set_option maxHeartbeats 300000

lemma vdW325 : vdWProp 325 3 1 := by
  unfold vdWProp
  intros f
  -- let fsucc := λ x => (f x).succ
  let g : Fin 33 → List.Vector Bool 5 := λ k => List.Vector.ofFn (λ i=> f (5 * k + i) = 0)
  have fin533 : Fintype.card (List.Vector Bool 5) • 1 < Fintype.card (Fin 33) := by simp_arith
  have ghyp := Fintype.exists_lt_card_fiber_of_mul_lt_card g fin533
  rcases ghyp with ⟨y₅, y₅hyp⟩
  -- pick block₁ block₂ from (Finset.filter (λ (x : Fin 33) => g x = y₅) Finset.univ)
  rw [Finset.one_lt_card_iff] at y₅hyp
  rcases y₅hyp with ⟨block₁, block₂, block₁Ins, block₂Ins, block₁Neblock₂⟩
  simp at block₁Ins block₂Ins
  wlog block₁Ltblock₂ : block₁ < block₂
  have tmp₁ := this f
  simp at tmp₁
  have tmp₂ := tmp₁ y₅ block₂ block₁ block₁Neblock₂.symm block₂Ins block₁Ins
  have block₂Ltblock₁ := lt_trichotomy block₁ block₂
  simp [block₁Ltblock₂, block₁Neblock₂] at block₂Ltblock₁
  rcases (tmp₂ block₂Ltblock₁) with ⟨s, sdiff, c, sc⟩
  use s, c
  --
  have blockeq : ∀ (i : Fin 5), f (5 * ↑block₁ + i) = f (5 * ↑block₂ + i) := by
    intro i
    have fb₁b₂ := congrArg (λ v ↦ List.Vector.get v i) (block₂Ins.trans block₁Ins.symm)
    simp at fb₁b₂
    have fb := Finset.mem_univ (f (5 * ↑block₁ + ↑i))
    simp [univ_fin2] at fb
    cases fb with
    | inl f0 => simp (config := { zetaDelta := true }) [f0] at fb₁b₂
                simp [f0, fb₁b₂]
    | inr f1 => simp (config := { zetaDelta := true }) [f1, not0_eq1] at fb₁b₂
                simp [f1, fb₁b₂]
  let targetfinset: Finset ℕ := {5 * block₁.val, 5 * block₁.val + 1, 5 * block₁.val + 2}
  have fin25 : Fintype.card (Fin 2) * 1 <  Fintype.card { x // x ∈ targetfinset } := by simp [targetfinset]
  -- Define f': takes one of the elemnet in finset ∅, return its color
  let f' : targetfinset → Fin 2 := λ k => f k
  -- There exists more than 1 elements that have the same color
  have fh' := Fintype.exists_lt_card_fiber_of_mul_lt_card f' fin25
  rcases fh' with ⟨c, chyp⟩
  -- pick a₁ a₂ from (Finset.filter (λ (x :({5 * block₁.val, 5 * block₁.val + 1, 5 * block₁.val + 2}:Finset ℕ )) => f' x = c) Finset.univ)
  rw [Finset.one_lt_card_iff] at chyp
  rcases chyp with ⟨a₁, a₂, a₁Ins, a₂Ins, a₁Nea₂⟩
  simp [f', targetfinset] at a₁Ins a₂Ins
  clear f' -- Bug #21396
  wlog a₁Lta₂ : a₁ < a₂
  have a₂Lta₁ := lt_trichotomy a₁ a₂
  simp [a₁Lta₂, a₁Nea₂] at a₂Lta₁
  have tmp₁ := this f fin533 y₅ block₁ block₂ block₁Neblock₂ block₁Ins block₂Ins block₁Ltblock₂ blockeq fin25 c a₂ a₁ a₁Nea₂.symm a₂Ins a₁Ins a₂Lta₁
  rcases tmp₁ with ⟨s, c, sdiff, sc⟩
  use s, c
  clear fin25 -- chyp
  -- express a₂ as 5b₂+i and prove
  have out₂ : ∃ i, (↑a₂ = 5 * block₁.val + i) ∧ (i < 3):= by
    -- three cases for a2: i =0,1,2
    rcases a₂Ins.left with rfl | rfl | rfl
    use 0
    simp
    use 1
    simp
    use 2
    simp
  rcases out₂ with ⟨i₂, a₂eq, i₂ineq⟩
  -- express a1 as 5b1+i and prove
  have out₁ : ∃ i, (↑a₁ = 5 * block₁.val + i) ∧ (i < i₂):= by
    -- three cases for a1: i =0,1,2
    rcases a₁Ins.left with rfl | rfl | rfl <;> rw [Subtype.mk_lt_mk] at a₁Lta₂ <;> simp [a₂eq] at a₁Lta₂
    use 0
    simp [a₁Lta₂]
    use 1
    use 2
  rcases out₁ with ⟨i₁, a₁eq, i₁ineq⟩
  -- clear targetfinset a₁.lt.a₂ a₁.lt.a₂.cast_bound,
  let I := i₂ - i₁
  let B : ℕ := ↑block₂ - ↑block₁
  have Ibound : i₁ + I < 3 := by
    change i₁ + (i₂ - i₁) < 3
    simp [←Nat.add_sub_assoc (le_of_lt i₁ineq) i₁, i₂ineq]
  have Bbound : ↑block₁ + B < 33 := by simp [B, ←Nat.add_sub_assoc (le_of_lt block₁Ltblock₂) block₁]
  let a₃ : ℕ := a₁.val + (I + I)
  -- two cases: same color vs. different color
  cases instDecidableEqFin 2 (f a₃) (f a₁) with
  | isFalse fa₃a₁ =>
    cases instDecidableEqFin 2 (f (↑a₁ + (I + 5 * B + (I + 5 * B)))) (f a₁) with
    | isFalse fblock₂ =>
      --Case III:  5block₁ + i₃, 5block₂ + i₃, 5block₃ + i₃
      use {start := a₃, diff := 5 * B}, f a₃
      simp (config := { zeta := false })
      apply And.intro
      · simp [B]
        assumption
      · intros e H
        cases H with
        | intro i ehyp =>
          apply And.intro
          · -- prove < 325
            fin_cases i <;> simp (config := { zetaDelta := true }) [ehyp] <;> linarith
          · --prove color ≠ c
            fin_cases i
            · simp at ehyp
              tauto
            · simp [ehyp]
              have temp₁ : a₃ + 5 * B = 5 * block₂.val + (i₁ + (I + I)) := by
                change a₃ + 5 * (block₂.val - block₁.val)  = 5 * block₂.val + (i₁ + (I + I))
                rw [Nat.mul_sub_left_distrib 5 block₂.val block₁.val]
                rw [Fin.lt_def, ← Nat.mul_lt_mul_left (by trivial : 0 < 5)] at block₁Ltblock₂
                have h₂ : 5 * block₁.val ≤ a₃ := by  simp_arith [a₁eq, a₃]
                rw [← Nat.add_sub_assoc (Nat.le_of_lt block₁Ltblock₂), Nat.sub_add_comm h₂, Nat.add_comm (5 * block₂.val)]
                simp_arith (config := { zeta := false }) [a₁eq, a₃, Nat.add_assoc (5 * block₁.val) i₁]
              have beqiII := blockeq ⟨i₁ + (I + I), by linarith⟩
              simp at beqiII
              rw [temp₁, ← beqiII, ← Nat.add_assoc]
              simp [a₁eq, a₃]
            · simp [ehyp]
              have temp : a₃ + 5 * B + 5 * B = ↑a₁ + (I + 5 * B + (I + 5 * B)) := by simp_arith [a₃]
              have temp₁: f a₃ = f (↑a₁ + (I + 5 * B + (I + 5 * B))) := notc fa₃a₁ fblock₂
              rw [temp, temp₁]
    | isTrue fblock₂ =>
      use {start := a₁, diff := I + 5 * B}, f a₁
      simp [i₁ineq, I, B]
      intros e H
      cases H with
      | intro i ehyp =>
        simp (config := { zeta := false }) at ehyp
        apply And.intro
        · fin_cases i <;> simp (config := { zeta := false }) [ehyp, a₁eq] <;> linarith only [i₁ineq, i₂ineq, Bbound, Ibound]
        · fin_cases i
          · simp [ehyp]
          · have a₁plusI: a₁.val + I = a₂.val := by simp [I, a₁eq, a₂eq, Nat.add_assoc (5 * block₁.val) i₁ (i₂ - i₁), Nat.add_sub_of_le (le_of_lt i₁ineq)]
            -- NOTE: Should we rw block₁Ltblock₂ earlier?
            rw [Fin.lt_def] at block₁Ltblock₂
            have tmp₁ : 5 * block₁.val ≤ 5 * block₂.val := by linarith only [block₁Ltblock₂]
            simp (config := { zeta := false }) [ehyp]
            rw [← Nat.add_assoc, a₁plusI, a₂eq]
            simp [Nat.mul_sub_left_distrib 5, ← Nat.add_sub_assoc tmp₁, Nat.add_assoc (5 * ↑block₁), Nat.add_comm i₂]
            have i₂lt5 : i₂ < 5 := by trans 3 <;> simp_arith [i₂ineq]
            have beqi₂ := blockeq (Fin.mk i₂ i₂lt5)
            simp at beqi₂
            aesop
          · rw [← fblock₂]
            simp [ehyp]
            congr
            simp_arith [I, B]
  | isTrue fa₃a₁=>
    use {start := a₁, diff := I}
    simp (config := { zeta := false })
    apply And.intro
    · simp [I]
      assumption
    · use c
      intros e H
      cases H with
      | intro i ehyp =>
        simp at ehyp
        apply And.intro
        · fin_cases i <;> simp [ehyp, targetfinset] <;> linarith
        · simp [ehyp]
          fin_cases i <;> aesop

noncomputable def vdW (k : ℕ) (r : ℕ) : ℕ := sInf { n : ℕ | vdWProp n k r.pred }

syntax "monotone" : tactic
macro_rules
  | `(tactic| monotone) => `(tactic|intros k₁ k₂ k₁leqk₂ k₁elem; simp at k₁elem ⊢; intro f; apply vdWMonotone k₁ <;> assumption)

theorem vdW1 :∀ {k : ℕ}, vdW k.succ 1 = k.succ := by
  intro k
  simp [vdW]
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  · apply And.intro
    · simp [vdWProp, eq_iff_true_of_subsingleton]
      use { start := 0, diff := 1}
      simp
      intros _ eins
      rcases eins with ⟨_, rfl⟩
      simp
    · simp
      intro vdWk
      simp [vdWProp, eq_iff_true_of_subsingleton] at vdWk
      rcases vdWk with ⟨s, sdiff, eProp⟩
      change 1 ≤ s.diff at sdiff
      have eend := eProp (s.start + k * s.diff) ⟨k, by simp⟩
      have contra : k ≤ s.start + k * s.diff := by cases k with
        |zero => simp
        |succ k' => trans (k'.succ * s.diff); simp [Nat.mul_le_mul_left, sdiff]; simp
      rw [lt_iff_not_ge] at eend
      simp [eend] at contra
  · monotone

theorem vdW2 : ∀ {r : ℕ}, vdW 2 r.succ = r.succ.succ := by
  intro r
  simp [vdW]
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  · apply And.intro
    · simp
      apply vdWProp2
    · simp
      intro vdWr
      simp [vdWProp] at vdWr
      rcases (vdWr (λ n ↦ Fin.ofNat' (r + 1) n)) with ⟨s, sdiff, ⟨_, eProp⟩⟩
      have estart := eProp s.start ⟨0, by simp⟩
      have eend := eProp (s.start + s.diff)  ⟨1, by simp⟩
      rw [← eend.right, ← Fin.val_eq_val, Fin.val_ofNat', Fin.val_ofNat'] at estart
      simp [Nat.mod_eq_of_lt estart.left, Nat.mod_eq_of_lt eend.left] at estart
      simp [estart.right] at sdiff
  · monotone

def isArithProg {N : ℕ} (l : List (Fin N)) (d : Fin N) := List.Chain' (λ m n => m < n ∧ m + d = n) l

lemma isArithProgIffGet {N : ℕ} {t : List (Fin N.succ)} {h h' d : Fin N.succ} : isArithProg (h :: h' :: t) d ↔ ((d > 0) ∧ ∀ (i : Fin t.length.succ.succ), ((h :: h' :: t).get i).val = h.val + i.val * d.val) := by
  induction t generalizing h h' with
  | nil =>
    simp [isArithProg]
    apply Iff.intro
    · intro hh'Prop
      cases hh'Prop
      next hLth' hdh' =>
        have hd := h.val_add_eq_ite d
        split at hd
        · simp [← hdh', hd, Fin.lt_def, lt_tsub_iff_right] at hLth'
          have ctr := (Nat.lt_trans d.prop hLth')
          simp at ctr
        · apply And.intro
          · simp [← hdh', Fin.lt_def, hd] at hLth' ⊢
            exact hLth'
          · intro i
            fin_cases i
            · simp
            · simp
              have hd := h.val_add_eq_ite d
              split at hd
              · have ctr := add_tsub_le_assoc (a := ↑h) (b := ↑d) (c := N.succ)
                simp [Nat.sub_eq_zero_iff_le.mpr (le_of_lt d.prop), ← hd, hdh'] at ctr
                cases (not_le_of_lt hLth' ctr)
              · simp [← hdh', hd]
    · simp
      intros dpos iprop
      have i1 := iprop ((0 : Fin N.succ).succ)
      simp at i1
      simp [Fin.lt_def] at dpos
      apply And.intro
      · simp [Fin.lt_def, i1]
        exact dpos
      · have hd := h.val_add_eq_ite d
        split at hd
        next ctr =>
          rw [← i1] at ctr
          cases (not_lt_of_le ctr) h'.prop
        next =>
          rw [← i1] at hd
          exact Fin.ext hd
  | cons h'' t ih =>
    simp [isArithProg]
    apply Iff.intro
    · intros isAP
      rcases isAP with ⟨⟨hLth', hdh'⟩, ⟨h'Lth'', h'dh''⟩, tIsAP⟩
      apply And.intro
      · rw [Fin.pos_iff_ne_zero]
        intro d0
        simp [d0] at hdh'
        simp [hdh'] at hLth'
      · apply Fin.cases
        · simp
        · intro i
          have h'tIsAP : isArithProg (h' :: h'' :: t) d := by
            simp [isArithProg]
            exact And.intro (And.intro h'Lth'' h'dh'') tIsAP
          rw [List.getElem_cons]
          have ihmul := (ih.mp h'tIsAP).right i
          simp [← hdh'] at ihmul ⊢
          simp [ihmul]
          have hd := h.val_add_eq_ite d
          split at hd
          · simp [← hdh', hd, Fin.lt_def, lt_tsub_iff_right] at hLth'
            have ctr := (Nat.lt_trans d.prop hLth')
            simp at ctr
          · simp [hd, Nat.add_assoc ↑h ↑d (↑i * ↑d), Nat.add_comm ↑d, ← Nat.succ_mul]
    · intro getProp
      cases getProp
      next dpos getProp =>
        have g1 := getProp 1
        simp at g1
        have hd := h.val_add_eq_ite d
        split at hd
        next ctr =>
          rw [← g1] at ctr
          cases (not_lt_of_le ctr) h'.prop
        · have getRest : ∀ (i : Fin (Nat.succ (Nat.succ (List.length t)))), ↑(List.get (h' :: h'' :: t) i) = h'.val + i.val * d.val := by
            intro i
            have gi := getProp i.succ
            simp at gi
            simp [gi, g1, Nat.add_assoc ↑h ↑d (↑i * ↑d), Nat.add_comm ↑d (↑i * ↑d), ← Nat.succ_mul]
          have isAPRest := ih.mpr (And.intro dpos getRest)
          simp [isArithProg] at isAPRest
          simp [isAPRest]
          apply And.intro
          · simp [Fin.lt_def, g1] at dpos ⊢
            exact dpos
          · apply Fin.ext
            simp [hd, g1]

instance existsIsArithProgDec {N : ℕ} : ∀ (l : List (Fin N.succ)), Decidable (∃ d : (Fin N.succ), isArithProg l d) := by
  intros l
  cases l with
  | nil =>
    apply isTrue
    simp [isArithProg]
  | cons h t =>
    cases t with
    | nil =>
      apply isTrue
      simp [isArithProg]
    | cons h' t =>
      cases (Fin.decLt h h') with
      | isFalse hGth' =>
        apply isFalse
        intro absurd
        rcases absurd with ⟨d, apProp⟩
        simp [isArithProg] at apProp
        cases hGth' apProp.left.left
      | isTrue hLth' =>
        cases (@List.decidableChain' (Fin N.succ) (λ m n => m < n ∧ m + (h' - h) = n) _ (h' :: t)) with
        | isFalse rest =>
          apply isFalse
          intro absurd
          rcases absurd with ⟨d, apProp⟩
          simp [isArithProg] at apProp
          rcases apProp with ⟨headChain, restChain⟩
          rcases headChain with ⟨_, ddiff⟩
          simp only [← ddiff, add_sub_cancel_left] at rest restChain
          contradiction
        | isTrue rest =>
          apply isTrue
          use h' - h
          simp [isArithProg, hLth', rest]

lrat_proof vdW9
  "p cnf 9 32 7 8 9 0 6 7 8 0 5 7 9 0 5 6 7 0 4 6 8 0 4 5 6 0 3 6 9 0 3 5 7 0 3 4 5 0 2 5 8 0 2 4 6 0 2 3 4 0 1 5 9 0 1 4 7 0 1 3 5 0 1 2 3 0 -7 -8 -9 0 -6 -7 -8 0 -5 -7 -9 0 -5 -6 -7 0 -4 -6 -8 0 -4 -5 -6 0 -3 -6 -9 0 -3 -5 -7 0 -3 -4 -5 0 -2 -5 -8 0 -2 -4 -6 0 -2 -3 -4 0 -1 -5 -9 0 -1 -4 -7 0 -1 -3 -5 0 -1 -2 -3 0"
  "33 -6 -8 -9 0 17 21 23 9 14 29 0 34 -8 -9 0 17 33 4 29 26 14 16 25 0 34 d 17 0 35 -8 -9 0 34 0 35 d 33 0 36 7 -9 0 35 2 23 8 22 29 14 0 37 -6 -9 0 36 19 35 10 23 27 9 0 38 -9 0 35 36 19 10 37 6 30 28 15 0 39 5 6 0 38 3 13 6 30 0 40 -5 -3 0 24 31 25 14 0 40 d 24 0 41 6 0 38 7 39 40 0 42 -5 0 41 38 20 22 40 1 12 26 0 43 7 0 42 38 3 0 44 1 0 42 38 13 0 45 -8 0 43 41 18 0 46 -4 0 44 43 30 0 47 2 0 45 42 10 0 48 3 0 46 42 9 0 49 0 47 48 44 32 0"

theorem vdWByList (N : ℕ) (k : ℕ) (r : ℕ) : vdWProp N.succ k r ↔ ∀ (f : Fin N.succ → Fin r.succ), ∃ (c : Fin r.succ) (l : List (Fin N.succ)) (_ : l ∈ List.sublistsLen k (List.finRange N.succ)) (_ : ∃ (d : Fin N.succ), isArithProg l d), ∀ n, n ∈ l → f n = c := by
  apply Iff.intro
  · intros vdW f
    let f' : ℕ → Fin r.succ := (λ n ↦ match Nat.decLt n N.succ with
                                       | isTrue p => f ⟨n, p⟩
                                       | isFalse _ => ⟨0, Nat.zero_lt_succ r⟩)
    rcases (vdW f') with ⟨s, c, sdiff, sprop⟩
    let f'' : Fin k → Fin N.succ := (λ (i : Fin k) ↦ let e := Nat.iterate (λ (j : ℕ) ↦ j + s.diff) i.val s.start; ⟨e, (sprop e ⟨i, refl e⟩).left⟩)
    let l : List (Fin N.succ) := List.ofFn f''
    have lsublk : l ∈ List.sublistsLen k (List.finRange N.succ) := by
      simp only [List.mem_sublistsLen, List.sublist_iff_exists_fin_orderEmbedding_get_eq, l, List.length_ofFn, and_true]
      let idxMap : Fin (List.ofFn f'').length → Fin (List.finRange N.succ).length := (λ idx ↦
        let mappedIdx := f'' (Fin.cast (List.length_ofFn f'') idx);
        Fin.cast (List.length_finRange N.succ).symm mappedIdx)
      have idxMapInj : Function.Injective idxMap := by
        intros a₁ a₂
        simp [idxMap, f'']
        intro conditions
        cases conditions with
        | inl p => exact Fin.ext p
        | inr p => rw [p] at sdiff; simp at sdiff
      have idxOrdered : ∀ {a₁ a₂ : Fin (List.ofFn f'').length}, idxMap a₁ ≤ idxMap a₂ ↔ a₁ ≤ a₂ := by
        intros a₁ a₂
        simp [idxMap, f'']
        apply Iff.intro
        · intro mulCond
          rw [Nat.mul_comm ↑a₁ s.diff, Nat.mul_comm ↑a₂ s.diff] at mulCond
          exact Fin.le_def.mpr (Nat.le_of_mul_le_mul_left mulCond sdiff.lt)
        · intro leCond
          rw [Fin.le_def] at leCond
          exact Nat.mul_le_mul_right s.diff leCond
      use { toFun := idxMap, inj' := idxMapInj, map_rel_iff' := idxOrdered }
      simp [idxMap, f'']
    have lArithP : ∃ (d : Fin N.succ), isArithProg l d := by
      use s.diff
      induction k with
      | zero => simp [isArithProg, l]
      | succ k' ih =>
        cases k' with
        | zero => simp [isArithProg, l]
        | succ k'' =>
          simp [l, isArithProgIffGet]
          have sdiffN : s.diff < N.succ := by
            calc
              s.diff ≤ s.start + s.diff := Nat.le_add_left s.diff s.start
              _ < N.succ := (sprop (s.start + s.diff) ⟨1, refl (s.start + s.diff)⟩).left
          apply And.intro
          · rw [Fin.lt_def, Fin.val_cast_of_lt sdiffN]
            simp [sdiff.lt]
          · apply Fin.cases
            · simp
            · rw [← Nat.mod_eq_iff_lt] at sdiffN
              · apply Fin.cases <;> simp [f'', sdiffN]
              · simp
    use c, l, lsublk, lArithP
    intros n nInl
    simp [List.mem_ofFn, l, f''] at nInl
    rcases nInl with ⟨y, ny⟩
    have fy := let e := Nat.iterate (λ (j : ℕ) ↦ j + s.diff) y.val s.start; (sprop e ⟨y, refl e⟩)
    simp [f'] at fy
    rcases fy with ⟨fyIneq, fyc⟩
    suffices f'n : f' n.val = c by aesop
    next =>
    simp [f', ← ny]
    split <;> aesop
  · intro vdWList
    unfold vdWProp
    intro f
    rcases (vdWList (λ n ↦ f n.val)) with ⟨c, l, lsublk, lArithP, lcolor⟩
    simp at lsublk
    rcases lsublk with ⟨lsubl, llength⟩
    cases k with
    | zero =>
      use { start := 0, diff := 1 }, c
      simp
      intros e ein
      simp [Membership.mem] at ein
    | succ k' =>
      cases l with
      | nil => simp at llength
      | cons h t =>
        rcases lArithP with ⟨d, dprop⟩
        cases k' with
        | zero =>
          use { start := h.val, diff := 1 }, c
          simp
          intros e ein
          simp [Membership.mem] at ein
          simp [ein, h.prop]
          apply lcolor
          simp
        | succ k'' =>
          cases t with
          | nil => simp [← Nat.succ_eq_add_one] at llength
          | cons h' t =>
            use { start := h.val, diff := d.val }, c
            rw [isArithProgIffGet] at dprop
            cases dprop
            next dpos iprop =>
              simp [Fin.lt_def] at dpos
              simp [dpos]
              intros e ein
              simp [Membership.mem] at ein
              rcases ein with ⟨i, eprop⟩
              simp at llength
              have gi := iprop (Fin.cast (congrArg Nat.succ (congrArg Nat.succ llength.symm)) i)
              simp at gi
              simp [eprop, ← gi]
              apply lcolor
              rw [List.mem_iff_get]
              use (Fin.cast (congrArg Nat.succ (congrArg Nat.succ llength.symm)) i)
              simp

open Lean Lean.Meta Lean.Parser.Tactic Lean.Parser.Term Lean.Elab.Tactic Lean.Elab.Term

private partial def explodeAss (g : MVarId) (h : Name) : TacticM (List MVarId) :=
g.withContext do {
  let some hDecl := (← getLCtx).findFromUserName? h | throwError ("No declaration " ++ h);
  let lType ← instantiateMVars hDecl.type;
  let .app (.app (.const `Or _) _) _ := lType | do {
    -- let ctx ← Simp.Context.mkDefault;
    let newG ← g.rename hDecl.fvarId `ass;
    return [newG]
    -- TODO Simplify here
  }

  let nameLeft ← getUnusedUserName `nameLeft;
  let nameRight ← getUnusedUserName `nameRight;
  let caseResults ← g.cases hDecl.fvarId #[⟨true, [nameLeft]⟩, ⟨true, [nameRight]⟩];
  let [leftG, rightG] := caseResults.toList.map (λ s => s.mvarId) | throwError ("cases at " ++ h ++ " did not create exactly two goals!");
  let leftGoals ← explodeAss leftG nameLeft;
  let rightGoals ← explodeAss rightG nameRight;
  return leftGoals ++ rightGoals;
}

syntax (name := explode_assignments) "explode_assignments " (ppSpace ident) : tactic

@[tactic explode_assignments] elab_rules : tactic
  | `(tactic| explode_assignments $name) => do let mg ← getMainGoal; let newGoals ← explodeAss mg (getNameOfIdent' name); replaceMainGoal newGoals;

theorem vdW32 : vdW 3 2 = 9 := by
  simp [vdW]
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  · simp
    apply And.intro <;> rw [vdWByList]
    · intro f
      by_contra h
      simp at h
      have h' : ∀ (c : Fin (Nat.succ 1)) (l : List (Fin (Nat.succ 8))) (_ : l ∈ List.filter (fun l' => decide (∃ d, isArithProg l' d)) (List.sublistsLen 3 (List.finRange (Nat.succ 8)))), ∃ n, n ∈ l ∧ ¬f n = c := by
        intros c l H
        rw [List.mem_filter, List.mem_sublistsLen] at H
        rcases H with ⟨⟨subl, length3⟩, isAP⟩
        simp at isAP
        rcases isAP with ⟨d, isAP⟩
        exact h c l d isAP subl length3
      have myReplace : (List.sublistsLen 3 (List.finRange (Nat.succ 8))).filter (λ l' => ∃ d, isArithProg l' d) = [[6, 7, 8], [5, 6, 7], [4, 6, 8], [4, 5, 6], [3, 5, 7], [3, 4, 5], [2, 5, 8], [2, 4, 6], [2, 3, 4], [1, 4, 7], [1, 3, 5], [1, 2, 3], [0, 4, 8], [0, 3, 6], [0, 2, 4], [0, 1, 2]] := by native_decide
      rw [myReplace] at h'
      have miniNotC : ∀ (x : Fin 2), ¬(x = 1) ↔ (x = 0) := by simp [← not0_eq1]
      simp only [List.find?, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, exists_eq_or_imp] at h'
      simp at h'
      have h1 := h' 1
      simp [miniNotC] at h1
      have h0 := h' 0
      have v := vdW9 (f 0 = 0) (f 1 = 0) (f 2 = 0) (f 3 = 0) (f 4 = 0) (f 5 = 0) (f 6 = 0) (f 7 = 0) (f 8 = 0)
      explode_assignments v <;> simp [ass] at h0 h1
    · simp only [List.find?, Function.id_comp, Function.comp_apply, Fin.mk_one, Fin.mk_zero, exists_and_left, exists_prop, not_forall, not_exists, not_and, and_imp, forall_exists_index]
      use ![0, 1, 1, 0, 0, 1, 1, 0]
      intros c l d isAP lsubl
      have lFiltered : l ∈ ((List.finRange (Nat.succ 7)).sublistsLen 3).filter (λ l' => (∃ (d : Fin (Nat.succ 7)), isArithProg l' d)) := by
        rw [List.mem_filter]
        apply And.intro
        · exact lsubl
        · simp
          exact ⟨d, isAP⟩
      have myReplace : ((List.finRange (Nat.succ 7)).sublistsLen 3).filter (λ l' => ∃ d, isArithProg l' d) = [[(5:Fin (Nat.succ 7)), 6, 7], [4, 5, 6], [3, 5, 7], [3, 4, 5], [2, 4, 6], [2, 3, 4], [1, 4, 7], [1, 3, 5], [1, 2, 3], [0, 3, 6], [0, 2, 4], [0, 1, 2]] := by native_decide
      rw [myReplace] at lFiltered
      fin_cases c <;> fin_cases lFiltered <;> simp_arith
  · monotone
