import Std.Data.List.Basic
import Std.Data.HashMap

open Std List String

def sublistsLenAux {α β : Type} : Nat → List α → (List α → β) → List β → List β
  | 0, _, f, r => f []::r
  | _ + 1, [], _, r => r
  | n + 1, a :: l, f, r => sublistsLenAux (n + 1) l f (sublistsLenAux n l (f ∘ List.cons a) r)

def sublistsLen {α : Type} (n : Nat) (l : List α) : List (List α) := sublistsLenAux n l id []

def keyToValue (i j: Nat): Nat := j + i * (i - 1) / 2 + 1

def negateLit (s : String): String :=
  match s.front with
  | '-' => s.drop 1
  | _ => "-" ++ s

def tseitinEncoding (Dnf: List String) (max_var: Nat): List String :=
  let Cnf := Dnf.map λlit => negateLit (toString (max_var)) ++ " " ++ toString (lit)
  let clause :List String:= (toString (max_var) ++ " " ++ intercalate " " (Dnf.map λlit => negateLit (toString (lit)))) :: []
  Cnf ++ clause

def transform : List (List String) → Nat →  (List String) × List (Nat)
 | [] ,_ => ([], [])
 | x :: t, maxvar => let result := (transform t (maxvar.succ)) ; ((tseitinEncoding x maxvar) ++ result.1, maxvar :: result.2)

def main (argv : List String) : IO UInt32 := do
  let N := argv[0]!.toNat!; let S := argv[1]!.toNat!; let T := argv[2]!.toNat!; let K := argv[3]!.toNat!
  let avoid_cliques := (sublistsLen K (range N))
  let s_cliques := (sublistsLen S (range N))
  let t_cliques := (sublistsLen T (range N))
  let max_var := N*(N-1) + 1

  let result := "p cnf " ++ toString (N*(N-1) + length s_cliques + length t_cliques)
  ++ " " ++ toString (length avoid_cliques + (1+ (length s_cliques)*(S*(S-1) + 1) + (length t_cliques)*(T*(T-1) + 1))) ++ "\n"

  let perm₁ := ["e " ++ intercalate " " ((range (N*(N-1)/2)).map λx => toString (x + 1))]
  let perm₂ := ["a " ++ intercalate " " ((range (N*(N-1)/2)).map λx => toString (x + 1 + (N*(N-1)/2)))]
  let perm₃ := ["e " ++ intercalate " " ((range (length s_cliques + length t_cliques)).map λx => toString (x + max_var))]


  let clauses₁ := avoid_cliques.map λclique => (intercalate " "
    ((sublistsLen 2 clique).map λx => negateLit (toString (keyToValue x.getLast! x.head!))))


  let clauses₂ := (s_cliques.map (λclique => join ((sublistsLen 2 clique).map
    (λx => toString (keyToValue x.getLast! x.head!)::toString (keyToValue x.getLast! x.head! + N*(N-1)/2)::[]))))
  let clauses₂ := join ((clauses₂.zip (range' max_var (length s_cliques))).map (λ Dnf => tseitinEncoding Dnf.fst (Dnf.snd)))

  let clauses₃ := (t_cliques.map (λclique => join ((sublistsLen 2 clique).map
    (λx => toString (keyToValue x.getLast! x.head!)::negateLit (toString (keyToValue x.getLast! x.head! + N*(N-1)/2))::[]))))
  let clauses₃ := join ((clauses₃.zip (range' (max_var + length s_cliques)  (length t_cliques))).map (λ Dnf => tseitinEncoding Dnf.fst (Dnf.snd)))

  let clauses₄ := [intercalate " " ((range' (max_var) (length s_cliques + length t_cliques)).map λx => toString (x))]

  IO.print ( result ++ intercalate " 0\n" (perm₁ ++ perm₂ ++ perm₃ ++ clauses₁ ++ clauses₂ ++ clauses₃++ clauses₄) ++ " 0\n")
  return 0
