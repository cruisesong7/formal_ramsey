import Std.Data.List.Basic

-- def isArithProgRec : List Nat → Nat → Bool
-- | [], _ => true
-- | [x], _ => true
-- | (x :: y :: xs), d => if y - x = d then isArithProgRec (y :: xs) d else false

-- def isArithProg (l : List Nat) : Bool :=
--   match l with
--   | [] => true
--   | [x] => true
--   | x :: y :: xs => isArithProgRec l (y - x)

def isArithProg (l : List Nat) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: xs =>
    let d := y - x
    List.foldl (fun acc (pair : Nat × Nat) => acc && (pair.snd - pair.fst = d)) true (List.zip l (y :: xs))
--list.all

def arithprogHelper (N k : Nat) : List (List Nat) :=
  let sublists := List.sublists ((List.range N).map λ x => x + 1)
  let filtered := sublists.filter (λ l => l.length = k && isArithProg l)
  filtered

--#eval (arithprogHelper 9 3)


def main (argv : List String) : IO UInt32 := do
  let N := argv[0]!.toNat!;  let k := argv[1]!.toNat!
  let progs := arithprogHelper N k
  let result := "p cnf " ++ toString N ++ " " ++ toString (2*progs.length) ++ "\n"
  let clauses := progs.map λprog => (String.intercalate " " (prog.map toString))
  let clauses' := progs.map λprog => (String.intercalate " " (prog.map λx => "-" ++ toString x))
  IO.print ( result ++ String.intercalate " 0\n" (clauses ++ clauses') ++ " 0\n")
  return 0

--#eval (main ["9", "3"])
