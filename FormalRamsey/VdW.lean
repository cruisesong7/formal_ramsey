import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
-- import data.bitvec.core
-- import Mathlib.Data.Fin.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Bitvec.Defs
import Mathlib.Tactic.Linarith.Frontend


-- import data.nat.lattice
-- import tactic.fin_cases
import Std.Data.Fin.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Data.Vector
import Init.Prelude
import FormalRamsey.Utils

-- import data.nat.cast
-- import data.nat.basic

import FormalRamsey.PickTactic
set_option maxHeartbeats 4000000

structure Arithprog (α : Type) (length : ℕ) [HAdd α α α] := (start : α) (diff : α)

instance {α : Type} {l : ℕ} [HAdd α α α] : Membership α (Arithprog α l) := ⟨λ a s => ∃ (i : Fin l), a = Nat.iterate (λ j : α => j + s.diff) i.val s.start⟩

def vdWProp (N : ℕ) (k : ℕ) (r : ℕ) : Prop := ∀ f : ℕ → Fin r, ∃ (s : Arithprog ℕ k) (c : Fin r), s.diff > 0 ∧ (∀ e ∈ s, e < N ∧ f e = c)

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


-- intro aEqb
-- rw [aEqb] at aNotInt
-- rw [← aInst_1] at aNotInt
-- simp at aNotInt
-- apply And.intro
-- intro bEqc
-- rw [bEqc] at aNotInt_1
-- rw [← aInst_2] at aNotInt_1
-- simp at aNotInt_1
-- apply And.intro
-- intro aEqc
-- rw [aEqc] at aNotInt
-- rw [← aInst_2] at aInst_1
-- rw [← aInst_1] at aNotInt
-- simp at aNotInt

-- simp at newBound
-- pick s3 from (finset.filter (λ (x : fin 5), f x = y) finset.univ) with a b c,
-- use [a, b, c],
-- simp at a.elem b.elem c.elem,

-- repeat{split},
-- apply ne_of_lt a.lt.b,
-- apply ne_of_lt b.lt.c,

-- have a.lt.c : a < c,
-- transitivity b,
-- exact a.lt.b, 
-- exact b.lt.c,

-- apply ne_of_lt a.lt.c,

-- rw [a.elem, b.elem],
-- rw [b.elem, c.elem],
-- end

-- example : ∀ f : fin 5 → fin 2, ∃ a b c, (a < b) ∧ (b < c) ∧ (f a = f b) ∧ (f b = f c) := 
-- begin
-- intros,

-- --2*2<5
-- have inq : fintype.card (fin 2) • 2 < ↑(fintype.card (fin 5)),
-- {simp,
-- linarith,},

-- --exist y<2 st. the set of x st. f(x)=y have cardinality >2
-- have fh' := fintype.exists_lt_card_fiber_of_mul_lt_card f inq,
-- cases fh' with y fh'',
-- pick 3 from (finset.filter (λ (x : fin 5), f x = y) finset.univ) with a b c,
-- use [a,b,c],

-- simp at a.elem b.elem c.elem,
-- repeat {split},
-- exact a.lt.b,
-- exact b.lt.c,
-- rw [a.elem,b.elem],
-- rw [b.elem,c.elem],
-- end

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
-- have a₁.lt.a₂.cast_bound : ↑a₁ < ↑a₂ := by exact a₁.lt.a₂, 
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

-- noncomputable def vdW (k : ℕ) (r : ℕ) : ℕ := Inf { n : ℕ | vdW_prop n k r }

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

