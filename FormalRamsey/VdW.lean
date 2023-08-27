import Mathlib.Data.Bitvec.Defs
import Mathlib.Tactic.Linarith.Frontend
import Std.Data.Fin.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Data.Vector
import Init.Prelude
import FormalRamsey.Utils
import Mathlib.Data.Nat.Lattice

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Sat.FromLRAT
-- import Mathlib.Tactic.SlimCheck

import FormalRamsey.PickTactic
set_option maxHeartbeats 4000000

structure Arithprog (α : Type) (length : ℕ) [HAdd α α α] := (start : α) (diff : α)

instance {α : Type} {l : ℕ} [HAdd α α α] : Membership α (Arithprog α l) := ⟨λ a s => ∃ (i : Fin l), a = Nat.iterate (λ j : α => j + s.diff) i.val s.start⟩

def vdWProp (N : ℕ) (k : ℕ) (r : ℕ) : Prop := ∀ f : ℕ → Fin r.succ, ∃ (s : Arithprog ℕ k) (c : Fin r.succ), s.diff > 0 ∧ (∀ e ∈ s, e < N ∧ f e = c)

lemma vdWMonotone : ∀ m k r, vdWProp m k r → ∀ n, m ≤ n → vdWProp n k r := by
  unfold vdWProp
  intros m k r vdWM n nLEm f
  rcases (vdWM f) with ⟨s, c, sDiff, eProp⟩
  use s
  use c
  apply And.intro
  exact sDiff
  intros e eIns
  rcases (eProp e eIns) with ⟨eLTn, eColor⟩
  apply And.intro
  apply lt_of_lt_of_le eLTn nLEm
  exact eColor

example : ∀ f : Fin 5 → Fin 2, ∃ a b c : Fin 5, (a ≠ b) ∧ (b ≠ c) ∧ (a ≠ c) ∧ (f a = f b) ∧ (f b = f c) := by
  intro f

  -- --2*2<5
  have inq : Fintype.card (Fin 2) • 2 < ↑(Fintype.card (Fin 5)) := by simp

  --exist y<2 st. the set of x st. f(x)=y have cardinality >2
  have fh' : ∃ y, 2 < Finset.card (Finset.filter (fun x => f x = y) Finset.univ) := Fintype.exists_lt_card_fiber_of_mul_lt_card f inq

  rcases fh' with ⟨y, fh''⟩

  pick a b c from (Finset.filter (fun x => f x = y) Finset.univ)
  use a, b, c

  simp_all

  apply And.intro
  apply ne_of_lt
  assumption
  apply And.intro
  apply ne_of_lt
  assumption
  apply ne_of_lt
  transitivity b
  assumption
  assumption

example : ∀ f : Fin 5 → Fin 2, ∃ a b c, (a < b) ∧ (b < c) ∧ (f a = f b) ∧ (f b = f c) := by
  intro f

  -- --2*2<5
  have inq : Fintype.card (Fin 2) • 2 < ↑(Fintype.card (Fin 5)) := by simp

  --exist y<2 st. the set of x st. f(x)=y have cardinality >2
  have fh' : ∃ y, 2 < Finset.card (Finset.filter (fun x => f x = y) Finset.univ) := Fintype.exists_lt_card_fiber_of_mul_lt_card f inq

  rcases fh' with ⟨y, fh''⟩

  pick a b c from (Finset.filter (fun x => f x = y) Finset.univ)
  use a, b, c

  simp_all

lemma vdW325 : vdWProp 325 3 2 := by
  unfold vdWProp
  intros f
  let g : Fin 33 → Bitvec 5 := λ k => Vector.ofFn (λ i=> f (5 * k + i) = 0)
  have fin533 : Fintype.card (Bitvec 5) • 1 < Fintype.card (Fin 33)
  simp
  have ghyp := Fintype.exists_lt_card_fiber_of_mul_lt_card g fin533
  rcases ghyp with ⟨y₅, y₅hyp⟩
  pick block₁ block₂ from (Finset.filter (λ (x : Fin 33) => g x = y₅) Finset.univ)
  simp at block₁Ins block₂Ins
  have notc : ∀ {c : Fin 2}, ∀ {x y : ℕ}, f x ≠ c → f y ≠ c → f x = f y := sorry
  have blockeq : ∀ (i : Fin 5), f (5 * ↑block₁ + i) = f (5 * ↑block₂ + i):=sorry
  --intro i
  --have fb₁b₂ := congr_arg (λ v => Vector.get v i) (Eq.trans block₂_1 (Eq.symm block₁_1))
  --let fb := f (5 * ↑block₁ + ↑i)
  --fin_cases i
  --simp_all
  --by_contra fbneq
  --simp at fbneq
  
  have block₁.lt.block₂.cast_bound : ↑block₁ < ↑block₂ := block₁Ltblock₂
  let targetfinset:Finset ℕ := {5 * block₁.val, 5 * block₁.val + 1, 5 * block₁.val + 2}
  have fin25 : Fintype.card (Fin 2) • 1 <  Fintype.card { x // x ∈ targetfinset} := by simp
 -- Define f': takes one of the elemnet in finset ∅, return its color
 -- let f' : ({5 * block₁.val, 5 * block₁.val + 1,  5 * block₁.val + 2}:Finset ℕ)→ Fin 2 := λ k => f k
  let f' :({5*block₁.val, 5*block₁.val+1, block₁.val+2}:Finset ℕ) → Fin 2 := λ k => f k 
 -- There exists more than 1 elements that have the same color
  have fh' := Fintype.exists_lt_card_fiber_of_mul_lt_card f' fin25
  rcases fh' with ⟨c, chyp⟩
  pick a₁ a₂ from (Finset.filter (λ (x :({5 * block₁.val, 5 * block₁.val + 1, 5 * block₁.val + 2}:Finset ℕ )) => f' x = c) Finset.univ)
  simp at a₁.Ins a₂.Ins
-- clear fin25 chyp,

  have a₁.lt.a₂.cast_bound : ↑a₁ < ↑a₂ := by exact a₁.lt.a₂
-- -- express a2 as 5b2+i and prove
  have out₂ : ∃ i, (↑a₂ = 5 * ↑block₁ + i) ∧ (i < 3):=sorry
-- -- three cases for a2: i =0,1,2
--  rcases a₂.elem.left with rfl | rfl | rfl
--  use 0,
--  simp,
--  use 1,
--  simp,
--  use 2,
--  simp,
 rcases out₂ with ⟨i₂, a₂eq, i₂ineq⟩
--  simp [a₂eq] at a₁.lt.a₂.cast_bound,

-- express a1 as 5b1+i and prove
have out₁ : ∃ i, (↑a₁ = 5 * ↑block₁ + i) ∧ (i < i₂):=sorry
-- three cases for a1: i =0,1,2
-- rcases a₁.elem.left with rfl | rfl | rfl,
-- use 0,
-- simp at a₁.lt.a₂.cast_bound ⊢,
-- exact a₁.lt.a₂.cast_bound,
-- use 1,
-- simp at a₁.lt.a₂.cast_bound ⊢,
-- exact a₁.lt.a₂.cast_bound,
-- use 2,
-- simp at a₁.lt.a₂.cast_bound ⊢,
-- exact a₁.lt.a₂.cast_bound,
rcases out₁ with ⟨i₁, a₁eq, i₁ineq⟩
-- simp [a₁eq, a₂eq, tsub_add_eq_tsub_tsub],
-- clear targetfinset a₁.lt.a₂ a₁.lt.a₂.cast_bound,

let I := i₂ - i₁
let B : ℕ := ↑block₂ - ↑block₁
have Ibound : i₁ + I < 3
change i₁ + (i₂ - i₁) < 3,
rw ← nat.add_sub_assoc (le_of_lt i₁ineq) i₁
simp
exact i₂ineq

have Bbound : ↑block₁ + B < 33
change ↑block₁ + (↑block₂ - ↑block₁) < 33
rw ← Nat.add_sub_assoc (le_of_lt block₁.lt.block₂.cast_bound) block₁
simp
have b₂.cast_bound: ↑block₂ < 33 := by exact block₂.property
exact b₂.cast_bound

let a₃ : ℕ := ↑a₁ + (I + I)

  



-- lemma vdW325 : vdW_prop 325 3 2 :=
-- begin
-- unfold vdW_prop,
-- intros,
-- -- f is the color function
-- -- Define g: takes any number between 1-33 groups, and return the color combination of that group
-- let g : fin 33 → bitvec 5 := λ k, vector.of_fn (λ i, f (5 * k + i) = 0),
-- -- There are only 32 types of coloring, thus 32<33
-- have fin533 : fintype.card (bitvec 5) • 1 < fintype.card (fin 33),
-- simp,
-- linarith,
-- -- There exists more than 1 blocks that have the same color combination
-- have ghyp := fintype.exists_lt_card_fiber_of_mul_lt_card g fin533,
-- rcases ghyp with ⟨y₅, y₅hyp⟩,
-- -- pick 2 blocks with same color combination
-- pick 2 from (finset.filter (λ (x : fin 33), g x = y₅) finset.univ) with block₁ block₂,
-- simp at block₁.elem block₂.elem,


-- have notc : ∀ {c : fin 2}, ∀ {x y : ℕ}, f x ≠ c → f y ≠ c → f x = f y,
-- intros c x y h₁ h₂,
-- let c₁ := f x,
-- let c₂ := f y,
-- change c₁ = c₂,

-- fin_cases c,

-- fin_cases c₁ using h_1,
-- contradiction,
-- fin_cases c₂ using h_2,
-- contradiction,
-- rw [h_1, h_2],

-- fin_cases c₁ using h_1,
-- fin_cases c₂ using h_2,
-- rw [h_1, h_2],
-- contradiction,
-- contradiction,

-- have blockeq : ∀ (i : fin 5), f (5 * ↑block₁ + i) = f (5 * ↑block₂ + i),
-- intro,
-- have fb₁b₂ := congr_arg (λ v, vector.nth v i) (eq.trans block₂.elem (eq.symm block₁.elem)),
-- let fb := f (5 * ↑block₁ + ↑i),
-- simp [← fb] at fb₁b₂ ⊢,
-- fin_cases i; {
--   fin_cases fb using fbeq,
--   simp [fbeq] at fb₁b₂ ⊢,
--   rw fb₁b₂,
--   have fbneq0 : fb ≠ 0,
--   simp [fbeq],
--   simp [← fb, fbeq] at fb₁b₂,
--   exact notc fbneq0 fb₁b₂,
-- },

-- clear fin533 y₅hyp block₂.elem block₁.elem y₅,

-- have block₁.lt.block₂.cast_bound : ↑block₁ < ↑block₂ := by exact block₁.lt.block₂,

-- -- let targetfinset be the first three element in block1
-- let targetfinset := (insert (5 * block₁.val) (insert (5 * block₁.val + 1) (insert (5 * block₁.val + 2) (∅:(finset ℕ))))),
-- -- at least two elememts have the same color
-- have fin25 : fintype.card (fin 2) • 1 <  fintype.card ↥targetfinset := by simp,
-- -- Define f': takes one of the elemnet in finset ∅, return its color
-- let f' : (insert (5 * block₁.val) (insert (5 * block₁.val + 1) (insert (5 * block₁.val + 2) (∅:(finset ℕ))))) → fin 2 := λ k, f k,
-- -- There exists more than 1 elements that have the same color
-- have fh' := fintype.exists_lt_card_fiber_of_mul_lt_card f' fin25,
-- rcases fh' with ⟨c, chyp⟩,
-- -- Among the selected three elements, pick two elements that have the same color
-- pick 2 from (finset.filter (λ (x : ↥{5 * block₁.val, 5 * block₁.val + 1, 5 * block₁.val + 2}), f' x = c) finset.univ) with a₁ a₂,
-- simp at a₁.elem a₂.elem,
-- clear fin25 chyp,
<<<<<<< HEAD
-- have a₁.lt.a₂.cast_bound : ↑a₁ < ↑a₂ := by exact a₁.lt.a₂, 
=======

-- have a₁.lt.a₂.cast_bound : ↑a₁ < ↑a₂ := by exact a₁.lt.a₂,
>>>>>>> bd01e6e (Completed a Proof of vdW 2 3 = 9)
-- -- express a2 as 5b2+i and prove
-- have out₂ : ∃ i, (↑a₂ = 5 * ↑block₁ + i) ∧ (i < 3),
-- -- three cases for a2: i =0,1,2
-- rcases a₂.elem.left with rfl | rfl | rfl,
-- use 0,
-- simp,
-- use 1,
-- simp,
-- use 2,
-- simp,
-- rcases out₂ with ⟨i₂, a₂eq, i₂ineq⟩,
-- simp [a₂eq] at a₁.lt.a₂.cast_bound,

-- -- express a1 as 5b1+i and prove
-- have out₁ : ∃ i, (↑a₁ = 5 * ↑block₁ + i) ∧ (i < i₂),
-- -- three cases for a1: i =0,1,2
-- rcases a₁.elem.left with rfl | rfl | rfl,
-- use 0,
-- simp at a₁.lt.a₂.cast_bound ⊢,
-- exact a₁.lt.a₂.cast_bound,
-- use 1,
-- simp at a₁.lt.a₂.cast_bound ⊢,
-- exact a₁.lt.a₂.cast_bound,
-- use 2,
-- simp at a₁.lt.a₂.cast_bound ⊢,
-- exact a₁.lt.a₂.cast_bound,
-- rcases out₁ with ⟨i₁, a₁eq, i₁ineq⟩,
-- simp [a₁eq, a₂eq, tsub_add_eq_tsub_tsub],
-- clear targetfinset a₁.lt.a₂ a₁.lt.a₂.cast_bound,

-- let I := i₂ - i₁,
-- let B : ℕ := ↑block₂ - ↑block₁,
-- have Ibound : i₁ + I < 3,
-- change i₁ + (i₂ - i₁) < 3,
-- rw ← nat.add_sub_assoc (le_of_lt i₁ineq) i₁,
-- simp,
-- exact i₂ineq,

-- have Bbound : ↑block₁ + B < 33,
-- change ↑block₁ + (↑block₂ - ↑block₁) < 33,
-- rw ← nat.add_sub_assoc (le_of_lt block₁.lt.block₂.cast_bound) block₁,
-- simp,
-- have b₂.cast_bound: ↑block₂ < 33 := by exact block₂.property,
-- exact b₂.cast_bound,

-- let a₃ : ℕ := ↑a₁ + (I + I),
-- -- two cases: same color vs. different color
-- cases (fin.decidable_eq 2) (f a₃) (f a₁),
-- rotate,

-- --- Same color case
-- -- Case I: 5block₁ + i₁, 5block₁ + i₂, 5block₁ + i₃
-- use {start := a₁, diff := I},
-- simp,
-- split,

-- assumption,
-- use c,
-- intros,
-- cases H with i ehyp,
-- split,

-- --Prove a₁ a₂ a₃ < 325
-- fin_cases i; simp [ehyp]; linarith,

-- -- Prove a₁ a₂ a₃ have same color
-- fin_cases i,
-- simp [ehyp],
-- exact a₁.elem.right,

-- --f(a₂) = c
-- simp [ehyp],

-- -- have temp: ↑a₁ + I = ↑a₂,
-- -- change ↑a₁ + (i₂ - i₁) = ↑a₂,
-- -- rw a₁eq,
-- -- rw add_assoc (5*↑block₁) i₁ (i₂-i₁),
-- -- rw (add_tsub_cancel_of_le (le_of_lt i₁ineq)),
-- -- rw ← a₂eq,

-- have a₁plusI: ↑a₁ + I = ↑a₂,
-- change ↑a₁ + (i₂ - i₁) = ↑a₂,
-- rw a₁eq,
-- rw add_assoc (5*↑block₁) i₁ (i₂-i₁),
-- rw (add_tsub_cancel_of_le (le_of_lt i₁ineq)),
-- rw ← a₂eq,

-- rw a₁plusI,
-- exact a₂.elem.right,

-- -- f(a₃) = c
-- simp [← a₃, ehyp, h],
-- exact a₁.elem.right,
-- cases (fin.decidable_eq 2) (f (↑a₁ + (I + 5 * B + (I + 5 * B)))) (f a₁),
-- rotate,

-- --Case II: 5block₁ + i₁, 5block₂ + i₂, 5block₃ + i₃
-- use {start := a₁, diff := I + 5*B},
-- simp,
-- split,

-- left,
-- assumption,

-- use c,
-- intros,
-- cases H with i ehyp,
-- split,

-- have b₁.cast_bound: ↑block₁ < 33 := by exact block₁.property,

-- --prove <325
-- fin_cases i,

-- simp [ehyp],
-- transitivity 170,
-- rcases a₁.elem.left with rfl | rfl | rfl; simp; linarith only [b₁.cast_bound],
-- simp,

-- simp [ehyp],
-- linarith,

-- simp [ehyp, a₁eq],
-- linarith only [Ibound, Bbound, b₁.cast_bound, i₁ineq],
-- --prove color = c
-- fin_cases i,

-- simp [ehyp],
-- exact a₁.elem.right,

-- simp [ehyp],
-- have temp: ↑a₁ + (I + 5 * B) = 5*block₂ + i₂,
-- rw ← add_assoc (↑a₁) I (5*B),

-- have a₁plusI: ↑a₁ + I = ↑a₂,
-- change ↑a₁ + (i₂ - i₁) = ↑a₂,
-- rw a₁eq,
-- rw add_assoc (5*↑block₁) i₁ (i₂-i₁),
-- rw (add_tsub_cancel_of_le (le_of_lt i₁ineq)),
-- rw ← a₂eq,

-- rw a₁plusI,
-- change ↑a₂ + 5*(↑block₂ - ↑block₁) = 5*↑block₂ + i₂,
-- rw (nat.mul_sub_left_distrib (5) (↑block₂) (↑block₁)),
-- have h₂:5 * ↑block₁ ≤ ↑a₂ := by simp [a₂eq],
-- rw ← (nat.add_sub_assoc (nat.mul_le_mul_left 5 (le_of_lt block₁.lt.block₂.cast_bound))),
-- rw (nat.sub_add_comm (h₂)),
-- simp [a₂eq],
-- apply add_comm,

-- rw temp,
-- have i₂lt5 : i₂ < 5 := by transitivity 3; simp [i₂ineq],
-- have beqi₂ := (blockeq (fin.mk (i₂) i₂lt5)),
-- simp at beqi₂,
-- rw ← beqi₂,
-- rw ← a₂eq,
-- exact a₂.elem.right,

-- simp [ehyp, h_1],
-- exact a₁.elem.right,

-- --Case III:  5block₁ + i₃, 5block₂ + i₃, 5block₃ + i₃
-- use {start := a₃, diff := 5*B},
-- simp,
-- split,

-- assumption,

-- use f(a₃),
-- intros,
-- cases H with i ehyp,
-- split,
-- --prove < 325
-- fin_cases i; simp [ehyp]; linarith,
-- --prove color ≠ c
-- fin_cases i,

-- simp at ehyp,
-- tauto,

-- simp [ehyp],
-- have a₃eq : a₃ = a₁ + (I + I) := by tauto,

-- have temp : a₃ + 5 * B = 5 * ↑block₂ + (i₁ + (I + I)),
-- change a₃ + 5*(↑block₂ - ↑block₁)  = 5 * ↑block₂ + (i₁ + (I + I)),
-- rw (nat.mul_sub_left_distrib (5) (↑block₂) (↑block₁)),
-- have h₀:↑block₁ < ↑block₂ := by exact block₁.lt.block₂,
-- have h₁:5 * ↑block₁ ≤ 5 * ↑block₂ := by linarith only [h₀],
-- have h₂:5 * ↑block₁ ≤ a₃ := by linarith only[a₁eq,a₃eq],
-- rw ← (nat.add_sub_assoc (h₁)),
-- rw (nat.sub_add_comm (h₂)),
-- rw a₃eq,
-- rw a₁eq,
-- rw add_assoc (5 * ↑block₁) (i₁) (I + I),
-- rw ( add_tsub_cancel_left (5*↑block₁) (i₁ + (I + I))),
-- rw add_comm (i₁ + (I + I)) (5*↑block₂),


-- have test : i₁ + (I + I) < 5 := by linarith,
-- have beqiII := (blockeq (fin.mk (i₁ + (I + I)) test)),
-- simp at beqiII,

-- rw temp,
-- rw ← beqiII,

-- have temp1 : 5 * ↑block₁ + (i₁ + (I + I)) = a₃ := by linarith,
-- rw temp1,


-- simp [ehyp],
-- have temp : a₃ + (5 * B + 5 * B) = ↑a₁ + (I + 5 * B + (I + 5 * B)),
-- change ↑a₁ + (I + I) + (5 * B + 5 * B) = ↑a₁ + (I + 5 * B + (I + 5 * B)),
-- linarith,
-- --rw nat.add_assoc (↑a₁) (I + I) (5 * B + 5 * B),
-- --rw ← nat.add_assoc (I + I) (5 * B) (5 * B),
-- --rw add_comm (I) (5 * B),
-- rw temp,
-- have temp₁: f(a₃) = f(↑a₁ + (I + 5*B + (I + 5*B))) := by exact notc h h_1,
-- rw ← temp₁,
-- end

noncomputable def vdW (k : ℕ) (r : ℕ) : ℕ := sInf { n : ℕ | vdWProp n k r.pred }

<<<<<<< HEAD
-- theorem vdW3 : vdW 3 2 = 9 :=
-- begin
-- unfold vdW,
-- have hs : ∀ (k₁ k₂ : ℕ), k₁ ≤ k₂ → k₁ ∈ {n : ℕ | vdW_prop n 3 2} → k₂ ∈ {n : ℕ | vdW_prop n 3 2},
-- intros _ _ k₁leqk₂ k₁elem,
-- simp at k₁elem ⊢,
-- intro f,
-- apply vdW_monotone k₁; assumption,
-- rw (nat.Inf_upward_closed_eq_succ_iff hs 8),
-- simp,
  --sorry
  --end

=======
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
          simp [(ih.mp h'tIsAP).right i, ← hdh']
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
  rcases l with _ | ⟨h, t⟩
  apply isTrue
  simp [isArithProg]
  rcases t with _ | ⟨h', t⟩
  apply isTrue
  simp [isArithProg]
  rcases (Fin.decLt h h') with hGth' | hLth'
  apply isFalse
  intro absurd
  rcases absurd with ⟨d, apProp⟩
  simp [isArithProg] at apProp
  cases hGth' apProp.left.left
  rcases (@List.decidableChain' (Fin N.succ) (λ m n => m < n ∧ m + (h' - h) = n) _ (h' :: t)) with rest | rest
  apply isFalse
  intro absurd
  rcases absurd with ⟨d, apProp⟩
  simp [isArithProg] at apProp
  rcases apProp with ⟨headChain, restChain⟩
  rcases headChain with ⟨_, ddiff⟩
  simp [← ddiff] at rest restChain
  contradiction
  apply isTrue
  use h' - h
  simp [isArithProg]
  tauto

-- #eval let allVars := List.filter (fun l' => decide (∃ d, isArithProg l' d)) (List.sublistsLen 3 (List.finRange (Nat.succ 8))); "p cnf " ++ (reprStr (List.finRange (Nat.succ 8)).length) ++ " " ++ (reprStr (2 * allVars.length)) ++ " " ++ " 0 ".intercalate (List.map (fun c => " ".intercalate (c.map (λ l => reprStr (l.val + 1)))) allVars) ++ " 0 " ++ " 0 ".intercalate (List.map (fun c => " ".intercalate (c.map (λ l => reprStr (Int.negSucc l.val)))) allVars) ++ " 0"

lrat_proof vdW9
  "p cnf 9 32 7 8 9 0 6 7 8 0 5 7 9 0 5 6 7 0 4 6 8 0 4 5 6 0 3 6 9 0 3 5 7 0 3 4 5 0 2 5 8 0 2 4 6 0 2 3 4 0 1 5 9 0 1 4 7 0 1 3 5 0 1 2 3 0 -7 -8 -9 0 -6 -7 -8 0 -5 -7 -9 0 -5 -6 -7 0 -4 -6 -8 0 -4 -5 -6 0 -3 -6 -9 0 -3 -5 -7 0 -3 -4 -5 0 -2 -5 -8 0 -2 -4 -6 0 -2 -3 -4 0 -1 -5 -9 0 -1 -4 -7 0 -1 -3 -5 0 -1 -2 -3 0"
  "33 -6 -8 -9 0 17 21 23 9 14 29 0 34 -8 -9 0 17 33 4 29 26 14 16 25 0 34 d 17 0 35 -8 -9 0 34 0 35 d 33 0 36 7 -9 0 35 2 23 8 22 29 14 0 37 -6 -9 0 36 19 35 10 23 27 9 0 38 -9 0 35 36 19 10 37 6 30 28 15 0 39 5 6 0 38 3 13 6 30 0 40 -5 -3 0 24 31 25 14 0 40 d 24 0 41 6 0 38 7 39 40 0 42 -5 0 41 38 20 22 40 1 12 26 0 43 7 0 42 38 3 0 44 1 0 42 38 13 0 45 -8 0 43 41 18 0 46 -4 0 44 43 30 0 47 2 0 45 42 10 0 48 3 0 46 42 9 0 49 0 47 48 44 32 0"

-- TODO Move these general properties up to around vdWMonotone

lemma vdWAntitone : ∀ {N k r : ℕ}, vdWProp N k r → ∀ {k' : ℕ}, k' ≤ k → vdWProp N k' r := by
  unfold vdWProp
  intros N k r vdW k' k'leqk f
  rcases vdW f with ⟨s, c, ⟨sdiff, sprop⟩⟩
  use { start := s.start, diff := s.diff }, c
  simp [sdiff, Membership.mem] at sprop ⊢
  intro a
  exact sprop (Fin.castLE k'leqk a)

lemma vdWGE : ∀ {N k r : ℕ}, vdWProp N k r → k ≤ N := by
  unfold vdWProp
  intros N k h vdW
  cases k with
  | zero => simp
  | succ k' =>
    rcases (vdW (λ _ ↦ 0)) with ⟨s, ⟨c, ⟨sDiff, sProp⟩⟩⟩
    have lastIneq := (let e := (Nat.iterate (λ j : ℕ ↦ j + s.diff) (Fin.last k').val s.start); sProp e ⟨Fin.last k', refl e⟩).left
    simp at lastIneq
    have k'ltN : k' < N := by
      calc
        k' = k' * 1 := (Nat.mul_one k').symm
        _ ≤ k' * s.diff := Nat.mul_le_mul Nat.le.refl sDiff.lt
        _ ≤ s.start + k' * s.diff := Nat.le_add_left (k' * s.diff) s.start
        _ < N := lastIneq
    exact k'ltN

-- set_option tactic.simp.trace true

theorem vdWByList (N : ℕ) (k : ℕ) (r : ℕ) : vdWProp N.succ k r ↔ ∀ (f : Fin N.succ → Fin r.succ), ∃ (c : Fin r.succ) (l : List (Fin N.succ)) (_ : l ∈ List.sublistsLen k (List.finRange N.succ)) (_ : ∃ (d : Fin N.succ), isArithProg l d), ∀ n, n ∈ l → f n = c := by
  apply Iff.intro
  intros vdW f
  let f' : ℕ → Fin r.succ := (λ n ↦ match Nat.decLt n N.succ with
                                     | isTrue p => f ⟨n, p⟩
                                     | isFalse _ => ⟨0, Nat.zero_lt_succ r⟩)
  rcases (vdW f') with ⟨s, c, sdiff, sprop⟩
  let f'' : Fin k → Fin N.succ := (λ (i : Fin k) ↦ let e := Nat.iterate (λ (j : ℕ) ↦ j + s.diff) i.val s.start; ⟨e, (sprop e ⟨i, refl e⟩).left⟩)
  let l : List (Fin N.succ) := List.ofFn f''
  have lsublk : l ∈ List.sublistsLen k (List.finRange N.succ) := by
    simp only [List.mem_sublistsLen, List.sublist_iff_exists_fin_orderEmbedding_get_eq, List.length_ofFn, and_true]
    let idxMap : Fin (List.ofFn f'').length → Fin (List.finRange N.succ).length := (λ idx ↦
      let mappedIdx := f'' (Fin.cast (List.length_ofFn f'') idx);
      Fin.cast (List.length_finRange N.succ).symm mappedIdx)
    have idxMapInj : Function.Injective idxMap := by
      unfold Function.Injective
      intros a₁ a₂
      simp
      intro conditions
      cases conditions with 
      | inl p => exact Fin.ext p
      | inr p => rw [p] at sdiff; simp at sdiff
    have idxOrdered : ∀ {a₁ a₂ : Fin (List.ofFn f'').length}, idxMap a₁ ≤ idxMap a₂ ↔ a₁ ≤ a₂ := by
      intros a₁ a₂
      simp
      apply Iff.intro
      · intro mulCond
        rw [Nat.mul_comm ↑a₁ s.diff, Nat.mul_comm ↑a₂ s.diff] at mulCond
        exact Fin.le_def.mpr (Nat.le_of_mul_le_mul_left mulCond sdiff.lt)
      · intro leCond
        rw [Fin.le_def] at leCond
        exact Nat.mul_le_mul_right s.diff leCond
    use { toFun := idxMap, inj' := idxMapInj, map_rel_iff' := idxOrdered }
    simp
  have lArithP : ∃ (d : Fin N.succ), isArithProg l d := by
    use s.diff
    unfold isArithProg
    induction k with
    | zero => simp
    | succ k' ih =>
      cases k' with
      | zero => simp
      | succ k'' =>
        simp [-add_right_iterate, sdiff]
        apply And.intro
        · simp [Fin.add_def]
          have l1prop := (l.get ⟨1, by simp⟩).prop
          simp at l1prop
          exact l1prop
        · have s'prop := ih (vdWAntitone vdW (le_of_lt Nat.le.refl)) { start := s.start + s.diff, diff := s.diff } sdiff
          simp [-add_right_iterate] at s'prop
          apply s'prop
          · apply List.Sublist.trans (l₂ := l)
            · simp [-add_right_iterate]
            · simp at lsublk
              simp [lsublk]
            · intro e ein
              simp [Membership.mem] at ein
              rcases ein with ⟨i, iprop⟩
              apply sprop
              · simp [iprop, Membership.mem]
                use i.succ.castLE Nat.le.refl
                simp
                rw [Nat.add_assoc s.start, Nat.add_comm s.diff (↑i * s.diff), ← Nat.succ_mul]
  use c, l, lsublk, lArithP
  intros n nInl
  simp [List.mem_ofFn] at nInl
  rcases nInl with ⟨y, ny⟩
  have fy := let e := Nat.iterate (λ (j : ℕ) ↦ j + s.diff) y.val s.start; (sprop e ⟨y, refl e⟩)
  simp at fy
  rcases fy with ⟨fyIneq, fyc⟩
  suffices f'n : f' n.val = c
  simp at f'n
  split at f'n
  · exact f'n
  · next _ nGEN _ =>
    split at fyc
    · next _ nLtN _ =>
      simp
      have fn : f' ↑n = c := by
        simp
        split
        · simp [← ny, ← fyc]
        · exact f'n
      simp at fn
      split at fn
      · exact fn
      · simp [n.prop] at nGEN
    · next => simp [n.prop] at nGEN
  · next =>
    simp [← ny]
    split
    · next ineq _ =>
      split at fyc
      · assumption
      . contradiction
    . next _ ineq _ => contradiction
  intro vdWList
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
    simp [Membership.mem, instMembershipArithprog] at ein
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
        simp [Membership.mem, instMembershipArithprog] at ein
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
            simp [Membership.mem, instMembershipArithprog] at ein
            rcases ein with ⟨i, eprop⟩
            simp at llength
            have gi := iprop (Fin.cast (congrArg Nat.succ (congrArg Nat.succ llength.symm)) i)
            simp at gi
            simp [eprop, ← gi]
            apply lcolor
            rw [List.mem_iff_get]
            use (Fin.cast (congrArg Nat.succ (congrArg Nat.succ llength.symm)) i)

open Lean Lean.Meta Lean.Parser.Tactic Lean.Parser.Term Lean.Elab.Tactic Lean.Elab.Term

private def explodeAss (g : MVarId) (h : Name) : TacticM (List MVarId) :=
g.withContext do {
  let some hDecl := (← getLCtx).findFromUserName? h | throwError ("No declaration " ++ h);
  let lType ← instantiateMVars hDecl.type;
  let .app (.app (.const `Or _) P) Q := lType | do {
    let ctx ← Simp.Context.mkDefault;
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

@[tactic pick] elab_rules : tactic
  | `(tactic| explode_assignments $name) => do let mg ← getMainGoal; let newGoals ← explodeAss mg (getNameOfIdent' name); replaceMainGoal newGoals;

example : (∃ (d : Fin 8), isArithProg ([3, 4, 7]:List (Fin 8)) d) → 1 = 2 := by
  intro isAP
  have isNotAP : ¬(∃ (d : Fin 8), isArithProg ([3, 4, 7]:List (Fin 8)) d) := by native_decide
  contradiction

theorem vdW3 : vdW 3 2 = 9 := by
  simp [vdW]
  have hs : ∀ (k₁ k₂ : ℕ), k₁ ≤ k₂ → k₁ ∈ {n : ℕ | vdWProp n 3 1} → k₂ ∈ {n : ℕ | vdWProp n 3 1} := by
    intros k₁ k₂ k₁leqk₂ k₁elem
    simp at k₁elem ⊢
    intro f
    apply vdWMonotone k₁ <;> assumption
  rw [Nat.sInf_upward_closed_eq_succ_iff hs 8]
  simp
  apply And.intro <;> rw [vdWByList]
  intro f
  by_contra h
  simp at h
  have h' : ∀ (c : Fin (Nat.succ 1)) (l : List (Fin (Nat.succ 8))) (_ : l ∈ List.filter (fun l' => decide (∃ d, isArithProg l' d)) (List.sublistsLen 3 (List.finRange (Nat.succ 8)))), ∃ n, n ∈ l ∧ ¬f n = c := by
    intros c l H
    rw [List.mem_filter, List.mem_sublistsLen] at H
    rcases H with ⟨⟨subl, length3⟩, isAP⟩
    simp at isAP
    rcases isAP with ⟨d, isAP⟩
    exact h c l d isAP subl length3
  have myReplace : List.filter (fun l' => decide (∃ d, isArithProg l' d)) (List.sublistsLen 3 (List.finRange (Nat.succ 8))) = [[6, 7, 8], [5, 6, 7], [4, 6, 8], [4, 5, 6], [3, 5, 7], [3, 4, 5], [2, 5, 8], [2, 4, 6], [2, 3, 4], [1, 4, 7], [1, 3, 5], [1, 2, 3], [0, 4, 8], [0, 3, 6], [0, 2, 4], [0, 1, 2]] := by native_decide
  rw [myReplace] at h'
  have miniNotC : ∀ (x : Fin 2), ¬(x = 1) ↔ (x = 0) := by
    intro x
    fin_cases x <;> apply Iff.intro <;> simp
  simp only [List.find?, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, exists_eq_or_imp] at h'
  simp at h'
  have h1 := h' 1
  rw [miniNotC (f 0), miniNotC (f 1), miniNotC (f 2), miniNotC (f 3), miniNotC (f 4), miniNotC (f 5), miniNotC (f 6), miniNotC (f 7), miniNotC (f 8)] at h1
  have h0 := h' 0
  have v := vdW9 (f 0 = 0) (f 1 = 0) (f 2 = 0) (f 3 = 0) (f 4 = 0) (f 5 = 0) (f 6 = 0) (f 7 = 0) (f 8 = 0)
  explode_assignments v <;> simp [ass] at h0 h1
  simp only [List.find?, Function.comp.left_id, Function.comp_apply, Fin.mk_one, Fin.mk_zero, exists_and_left, exists_prop, not_forall, not_exists, not_and, and_imp, forall_exists_index]
  use ![0, 1, 1, 0, 0, 1, 1, 0]
  intros c l d isAP lsubl
  have lFiltered : l ∈ ((List.finRange (Nat.succ 7)).sublistsLen 3).filter (λ l' => (∃ (d : Fin (Nat.succ 7)), isArithProg l' d)) := by
    rw [List.mem_filter]
    apply And.intro
    exact lsubl
    simp
    exact ⟨d, isAP⟩
  have myReplace : ((List.finRange (Nat.succ 7)).sublistsLen 3).filter (λ l' => (∃ (d : Fin (Nat.succ 7)), isArithProg l' d)) = [[(5:Fin (Nat.succ 7)), 6, 7], [4, 5, 6], [3, 5, 7], [3, 4, 5], [2, 4, 6], [2, 3, 4], [1, 4, 7], [1, 3, 5], [1, 2, 3], [0, 3, 6], [0, 2, 4], [0, 1, 2]] := by native_decide
  rw [myReplace] at lFiltered
  fin_cases c <;> fin_cases lFiltered <;> simp
>>>>>>> bd01e6e (Completed a Proof of vdW 2 3 = 9)
