import Mathlib.Combinatorics.SimpleGraph.Basic

open Std

def readG6Header (s : String) : UInt32 :=
match s.toList with
| [] => 0
| h :: _ => h.val - (UInt32.ofNatLT 63 (by simp +arith [UInt32.size]))

def addIdx {α : Type} : List α → ℕ → ℕ → List (α × ℕ × ℕ)
| [], _, _ => []
| h :: t, i, j => if i = j then (h, 0, j + 1) :: (addIdx t 1 (j + 1))  else (h, i, j) :: (addIdx t (i + 1) j)

lemma addIdxLt {α : Type} : ∀ (l : List α) n m, n ≤ m → ∀ {x i j}, (x, i, j) ∈ addIdx l n m → i < j := by
  intro l
  induction l with
  | nil => simp [addIdx]
  | cons h t ih =>
    simp [addIdx]
    intros n m nLem x i j ih
    split at ih
    next nEqm =>
      simp at ih
      cases ih
      next xijVals =>
        rcases xijVals with ⟨_, rfl, rfl⟩
        simp
      next xijInt =>
        apply ih 1 (m + 1)
        · simp
        · exact xijInt
    next nNeqm =>
      simp at ih
      cases ih
      next xijVals =>
        rcases xijVals with ⟨_, rfl, rfl⟩
        exact Nat.lt_of_le_of_ne nLem nNeqm
      next xijInt =>
        apply ih (n + 1) m
        · rw [Nat.add_one]
          exact Nat.lt_of_le_of_ne nLem nNeqm
        · exact xijInt

def collectInFinset {α : Type} [DecidableEq α] : List (Bool × α) → Finset α
| [] => Finset.empty
| ((true, h) :: t) => insert h (collectInFinset t)
| ((false, _) :: t) => collectInFinset t

lemma collectInFinsetMem {α : Type} [DecidableEq α] : ∀ x (l : List (Bool × α)), x ∈ collectInFinset l ↔ (true, x) ∈ l := by
  intros x l
  induction l with
  | nil =>
    simp [collectInFinset]
    exact Finset.not_mem_empty x
  | cons h t ih =>
    simp [collectInFinset]
    apply Iff.intro
    · intro xin
      cases h
      next b y =>
        cases b <;> simp [collectInFinset, ih] at xin <;> simp [xin]    
    · intro xin
      cases h
      next b y =>
        cases b <;> simp [← ih] at xin <;>  simp [collectInFinset, xin]

def readG6AdjAux (l : List Char) : Finset (Sym2 (ℕ)) := collectInFinset ((addIdx (List.foldl (λ l (x : Char) ↦ l ++ (List.ofFn (BitVec.ofNat 6 (x.val.toNat - 63)).getMsb')) [] l) 0 0).map (λ p ↦ (p.fst, Sym2.mk p.snd)))

def readG6Adj (s : String) : Finset (Sym2 (ℕ)) :=
match s.toList with
| [] => Finset.empty
| _ :: t => readG6AdjAux t

def readG6 (s : String) : SimpleGraph (Fin (readG6Header s).toNat) := {
  Adj := λ u v ↦ s(u.val, v.val) ∈ readG6Adj s,
  symm := by
    unfold Symmetric
    intros _ _ xyIn
    rw [Sym2.eq_swap]
    exact xyIn,
  loopless := by
    simp [Irreflexive, readG6Adj, String.toList]
    intros v loop
    cases s
    split at loop
    next snil =>
      simp at snil
      simp [snil, readG6Header] at v
      exact Fin.elim0 v
    next h t _ =>
      simp [readG6AdjAux, collectInFinsetMem] at loop
      have vLtv := addIdxLt _ 0 0 (Nat.le_refl 0) loop
      simp at vLtv
}

instance : ∀ s, DecidableRel (readG6 s).Adj := by
  simp [DecidableRel, readG6, readG6Adj]
  intros s a b
  cases s
  next s =>
    cases s with
    | nil =>
      apply isFalse
      apply Finset.not_mem_empty
    | cons h t =>
      dsimp [readG6AdjAux]
      rw [collectInFinsetMem, List.mem_map]
      apply List.decidableBEx

open Lean.Parser

macro "g6" g6str:strLit : tactic => `(tactic| use readG6 $g6str, (by infer_instance))
macro_rules
  | `(tactic| g6 $g6str) => `(tactic| use readG6 $g6str, (by infer_instance))
  
-- def c_k_succ_s (k : ℕ) : simple_graph (fin k.succ.succ) := { adj := λ u v, ((min u v + 1 = max u v) ∨ ((min u v = 0) ∧ (max u v = fin.last k.succ))), symm := begin unfold symmetric, finish end, loopless := begin unfold irreflexive, simp, intro h, have h' := fin.veq_of_eq h, tauto end }

-- def c5 := c_k_succ_s 3

-- example : readG6 "DUW" ≃g c5 := sorry
