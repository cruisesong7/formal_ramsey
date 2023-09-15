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
set_option maxHeartbeats 400000

structure Arithprog (α : Type) (length : ℕ) [HAdd α α α] := (start : α) (diff : α)

instance {α : Type} {l : ℕ} [HAdd α α α] : Membership α (Arithprog α l) := ⟨λ a s => ∃ (i : Fin l), a = Nat.iterate (λ j : α => j + s.diff) i.val s.start⟩

def vdWProp (N : ℕ) (k : ℕ) (r : ℕ) : Prop := ∀ f : ℕ → Fin r, ∃ (s : Arithprog ℕ k) (c : Fin r), s.diff > 0 ∧ (∀ e ∈ s, e < N ∧ f e = c)

-- lemma vdWMonotone : ∀ m k r, vdWProp m k r → ∀ n, m ≤ n → vdWProp n k r := by
--   unfold vdWProp
--   intros m k r vdWM n nLEm f
--   rcases (vdWM f) with ⟨s, c, sDiff, eProp⟩
--   use s
--   use c
--   apply And.intro
--   exact sDiff
--   intros e eIns
--   rcases (eProp e eIns) with ⟨eLTn, eColor⟩
--   apply And.intro
--   apply lt_of_lt_of_le eLTn nLEm
--   exact eColor

-- example : ∀ f : Fin 5 → Fin 2, ∃ a b c : Fin 5, (a ≠ b) ∧ (b ≠ c) ∧ (a ≠ c) ∧ (f a = f b) ∧ (f b = f c) := by
--   intro f

--   -- --2*2<5
--   have inq : Fintype.card (Fin 2) • 2 < ↑(Fintype.card (Fin 5)) := by simp

--   --exist y<2 st. the set of x st. f(x)=y have cardinality >2
--   have fh' : ∃ y, 2 < Finset.card (Finset.filter (fun x => f x = y) Finset.univ) := Fintype.exists_lt_card_fiber_of_mul_lt_card f inq

--   rcases fh' with ⟨y, fh''⟩

--   pick a b c from (Finset.filter (fun x => f x = y) Finset.univ)
--   use a, b, c

--   simp_all


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
  simp_all
  have notc : ∀ {c : Fin 2}, ∀ {x y : ℕ}, f x ≠ c → f y ≠ c → f x = f y := sorry
  have blockeq : ∀ (i : Fin 5), f (5 * ↑block₁ + i) = f (5 * ↑block₂ + i):= by
    intro i
    --have fRange : f (5*↑block₁+ ↑i) = 0 ∨ f (5*↑block₁+ ↑i) ≠ 0 := sorry
    --let fb := f (5 * ↑block₁ + ↑i)
    by_contra h
    have fb₁b₂ := congr_arg (λ v => Vector.get v i) (Eq.trans block₂Ins (Eq.symm block₁Ins))
    cases instDecidableEqFin _ (f (5 * ↑block₁ + ↑i)) 0 with 
    |isFalse h1 => fin_cases i <;> {
      simp[not0_eq1] at h1
      simp[h1, not0_eq1] at h
      simp [h, h1, not0_eq1] at fb₁b₂
      simp[fb₁b₂] at h
    } 
    |isTrue h1 => fin_cases i <;> {
      simp[not0_eq1] at h1
      simp[h1, not0_eq1] at h
      simp [h, h1, not0_eq1] at fb₁b₂
      simp[fb₁b₂] at h
    } 
    done

--   have block₁.lt.block₂.cast_bound : ↑block₁ < ↑block₂ := sorry
--   let targetfinset := (insert (5 * block₁.val) (insert (5 * block₁.val + 1) (insert (5 * block₁.val + 2) (∅:(Finset ℕ)))))
--   have fin25 : Fintype.card (Fin 2) • 1 <  Fintype.card targetfinset := by simp
--  -- Define f': takes one of the elemnet in finset ∅, return its color
--   let f' : (insert (5 * block₁.val) (insert (5 * block₁.val + 1) (insert (5 * block₁.val + 2) (∅:(Finset ℕ))))) → Fin 2 := λ k => f k
--  -- There exists more than 1 elements that have the same color
--   have fh' := Fintype.exists_lt_card_fiber_of_mul_lt_card f' fin25
--   rcases fh' with ⟨c, chyp⟩
--   sorry

  

