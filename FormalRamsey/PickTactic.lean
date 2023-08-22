import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice

open Lean Lean.Meta Lean.Parser.Tactic Lean.Parser.Term Lean.Elab.Tactic Lean.Elab.Term

inductive PickMode where | lo : PickMode | eq : PickMode

namespace Pick

lemma pick_one_eq {α : Type} {s : Finset α} [DecidableEq α] : 0 < s.card → ∃ (a : α) (t : Finset α), (t.card = s.card.pred) ∧ (a ∉ t) ∧ (insert a t = s) := by
  intro sPos
  have scard : s.card = s.card.pred + 1 := (s.card.eq_zero_or_eq_succ_pred).resolve_left (ne_of_lt sPos).symm
  rw [Finset.card_eq_succ] at scard
  rcases scard with ⟨a, t, x⟩
  use a
  use t
  tauto

lemma pick_one_lo {α : Type} {s : Finset α} [LinearOrder α] : 0 < s.card → ∃ (a : α) (t : Finset α), (t.card = s.card.pred) ∧ (∀ a' ∈ t, a < a') ∧ (insert a t = s) := by
  intro sPos
  rw [Finset.card_pos] at sPos
  let a := s.min' sPos
  let t := s.erase a
  use a
  use t
  have aIns := s.min'_mem sPos
  apply And.intro
  exact Finset.card_erase_of_mem aIns
  apply And.intro
  intros b bInt
  apply s.min'_lt_of_mem_erase_min' sPos bInt
  apply s.insert_erase aIns

end Pick

private def diffHyp (a : Name) (aNotInt : Expr) (info : Name × Expr) : TacticM PUnit :=
withMainContext do {
  let some aDecl := (← getLCtx).findFromUserName? a | throwError ("Could not find " ++ a ++ " in current context!");
  let some bDecl := (← getLCtx).findFromUserName? info.fst | throwError ("Could not find " ++ info.fst ++ " in current context!");
  let .app (.const `Not _) setEqExpr ← inferType aNotInt | throwError ("Could not parse expression " ++ aNotInt);
  let .app (.app (.app (.app (.app (.const `Membership.mem levels) eType) sType) memInst) _) s := setEqExpr | throwError ("Could not parse expression " ++ aNotInt);
  let neqExpr ← instantiateMVars (mkApp3 (.const `Ne [(← mkFreshLevelMVar)]) eType aDecl.toExpr bDecl.toExpr);
  let neqProof ← instantiateMVars (.lam `x (mkApp3 (.const `Eq [← mkFreshLevelMVar]) eType aDecl.toExpr bDecl.toExpr) (.app aNotInt (mkApp6 (.const `Eq.subst [(← mkFreshLevelMVar)]) eType (.lam `y eType (mkApp5 (.const `Membership.mem levels) eType sType memInst (.bvar 0) s) .default) bDecl.toExpr aDecl.toExpr (mkApp4 (.const `Eq.symm [(← mkFreshLevelMVar)]) (← mkFreshTypeMVar) aDecl.toExpr bDecl.toExpr (.bvar 0)) info.snd)) .default);
  let neqName ← getUnusedUserName (a ++ "Neq" ++ info.fst);
  -- DO NOT REMOVE
  check neqExpr;
  check neqProof;
  let ngs ← (← getMainGoal).assertHypotheses #[{ userName := neqName, type := neqExpr, value := neqProof }];
  replaceMainGoal [ngs.snd];
}

private def ltHyp [Monad m] [MonadLCtx m] (a : Name) (altt : Expr) (info : Name × Expr) : m Unit :=
do {
  let aexpr := (← getLCtx).findFromUserName? a;
  let b := (← getLCtx).findFromUserName? info.fst;
--   neqexpr ← tactic.to_expr ``(%%aexpr < %%b),
--   neqproof ← tactic.to_expr ``(%%altt %%b %%info.snd),
--   ineqprooft ← tactic.infer_type neqproof,
  let neqname ← getUnusedUserName (a ++ "lt" ++ info.fst);
--   tactic.assertv neqname neqexpr neqproof,
  return()
}

private def wrapup (s : Expr) (info : Name × Expr) : TacticM Unit :=
withMainContext do {
  let n ← getUnusedUserName (info.fst);
  -- TODO Maybe infer also the element type from the set type
  let sType ← inferType s;
  let some aDecl := (← getLCtx).findFromUserName? info.fst | throwError ("Could not find " ++ info.fst ++ " in the current context!");
  let inExpr ← instantiateMVars (mkApp5 (.const `Membership.mem [← mkFreshLevelMVar, ← mkFreshLevelMVar]) (← mkFreshTypeMVar) sType (← mkFreshExprMVar none) aDecl.toExpr s);
  let inVal ← instantiateMVars info.snd;
  -- DO NOT REMOVE
  check inExpr;
  check inVal;
  let ngs ← (← getMainGoal).assertHypotheses #[{ userName := n, type := inExpr, value := inVal }];
  replaceMainGoal [ngs.snd];
}

-- TODO Move this inside doPick
private def detectMode (α : Expr) : TacticM (PickMode × Expr) :=
  do {
    let u ← mkFreshLevelMVar;
    let loClass := (Expr.app (.const `LinearOrder [u]) α);
    let e ← synthInstance loClass;
    return (PickMode.lo, e)
  } <|>
  do {
    let u ← mkFreshLevelMVar;
    let eqClass := (Expr.app (.const `DecidableEq [u]) α);
    let e ← synthInstance eqClass;
    return (PickMode.eq, e)
  } <|> throwError ("No LinearOrder or DecidableEq in type " ++ α)

private def upgradeProof (decEqExpr : Expr) (aInst : Expr) (info : Name × Expr) : TacticM (Name × Expr) :=
withMainContext do {
  let .app (.app (.app (.const `Eq _) sType) insExpr) sExpr ← inferType aInst | throwError ("Could not parse type of expression " ++ aInst);
  let some bDecl := (← getLCtx).findFromUserName? info.fst | throwError ("Could not find " ++ info.fst ++ " in the curent context!");
  let eType ← inferType bDecl.toExpr;
-- TODO THE DECEQ THING IS BROKEN
  let subsetEqExpr := mkApp6 (.const `Eq.subst [(← mkFreshLevelMVar)]) sType (.lam `x sType (mkApp5 (.const `Membership.mem [← mkFreshLevelMVar, ← mkFreshLevelMVar]) (← mkFreshExprMVar none) sType (← mkFreshExprMVar none) bDecl.toExpr (.bvar 0)) .default) insExpr sExpr aInst (mkApp6 (.const `Finset.mem_insert_of_mem [← mkFreshLevelMVar]) eType (← mkFreshExprMVar none) (← mkFreshExprMVar none) bDecl.toExpr (← mkFreshExprMVar none) info.snd);
  check subsetEqExpr;
-- match mode with
  --                | pick_mode.eq := tactic.to_expr ``(((finset.ext_iff.mp %%ainst) %%b).mp (finset.subset_iff.mp (finset.subset_insert %%a %%t) %%info.snd))
  --                | pick_mode.lo := do {
  --                                    α ← tactic.infer_type b,
  --                                    loclass ← tactic.to_expr  ``(linear_order %%α),
  --                                    loinst ← tactic.mk_instance loclass,
  --                                    tactic.to_expr ``(((finset.ext_iff.mp %%ainst) %%b).mp (finset.subset_iff.mp (@finset.subset_insert _ (%%loinst).decidable_eq %%a %%t) %%info.snd))
  --                                 }
  --                end,
  return (info.fst, subsetEqExpr)
}

private partial def parseLBound (e : Expr) : TacticM (Option (Expr × Expr × Expr × List Level)) :=
match e.getAppFn with
  | .const `LT.lt _ => (match e.getAppArgs with
    | #[_, _, b, s] =>  (match s.getAppFn with
      | .const `Finset.card u => (match s.getAppArgs with
        | #[t, s'] => return some (b, t, s', u)
        | _ => do return none)
      | _ => do return none)
    | _  => do return none)
  | _ => return none

-- Invariant: every level returns a list of pairs where each pair is:
-- fst: the name of a member obtained in a recursive call
-- snd: the name of the fact that that member belongs to the rest of the set of this level
-- It is the responsibility of each level to upgrade the recursive list at the calling level
private def doPick (mode : PickMode) : List Name → Name → TacticM (List (Name × Expr))
| [], _ => return []
| (name :: names), bineq => withMainContext do
    let some (.cdecl _ bineqVar _ e _ _) := (← getLCtx).findFromUserName? bineq | throwError ("Could not get expression in " ++ bineq);
    let subsetName ← getUnusedUserName ("t");
    let atCardName ← getUnusedUserName ("atCard");
    let aNotIntName ← getUnusedUserName ("aNotInt");
    let aInstName ← getUnusedUserName ("aInst");
    match mode with
      | .eq => do {
                  let some (b, t, s, levels) ← parseLBound e | throwError bineq ++ " is not a lower-bound expression!";
                  let mg ← getMainGoal;
                  let u ← mkFreshLevelMVar;
                  let eqClass := (Expr.app (.const `DecidableEq [u]) t);
                  let eqInst ← synthInstance eqClass;
                  let sType ← inferType s;
                  let u ← mkFreshLevelMVar;
                  let pickLemma ← instantiateMVars (mkApp4 (.const `Pick.pick_one_eq []) t s eqInst (mkApp7 (.const `lt_of_le_of_lt [u]) (← mkFreshExprMVar none) (← mkFreshExprMVar none) (.const `Nat.zero []) b (mkApp2 (.const `Finset.card levels) t s) (.app (.const `Nat.zero_le []) b) (.fvar bineqVar)));
                  -- DO NOT REMOVE
                  check pickLemma;
                  let pls ← pickLemma.toSyntax;
                  let ngs ← Std.Tactic.RCases.rcases #[(none, pls)] (.tuple' (List.map (.one (mkNullNode)) [name, subsetName, atCardName, aNotIntName, aInstName])) mg;
                  replaceMainGoal ngs;
                  -- let mg ← getMainGoal;
                  let u ← mkFreshLevelMVar;
                  let v ← mkFreshLevelMVar;
                  let some b' := b.numeral? | throwError b ++ " is not a number!";
                  let newBoundName ← getUnusedUserName ("newBound");
                  -- TODO Figure out if there is an elegant way to reload the context
                  withMainContext do {
                  let some a := (← getLCtx).findFromUserName? name | throwError ("Could not find declaration " ++ atCardName ++ "in current context!");
                  let some atCard := (← getLCtx).findFromUserName? atCardName | throwError ("Could not find declaration " ++ atCardName ++ " in current context!");
                  let some tset := (← getLCtx).findFromUserName? subsetName | throwError ("Could not find declaration " ++ subsetName ++ " in current context!");
                  let some aInst := (← getLCtx).findFromUserName? aInstName | throwError ("Could not find declaration " ++ aInstName ++ " in current context!");
                  let (_, cl) ← detectMode t;
                  let aInParent ← (match mode with
-- TODO THIS IS BROKEN AS WELL!! SWAP THE DECEQ INSTANCES
                                     | .eq => do return mkApp6 (.const `Eq.subst [(← mkFreshLevelMVar)]) sType (.lam  `x sType (mkApp5 (.const `Membership.mem [← mkFreshLevelMVar, ← mkFreshLevelMVar]) t sType (← mkFreshExprMVar none) a.toExpr (.bvar 0)) .default) (← mkFreshExprMVar none) s aInst.toExpr (mkApp4 (.const `Finset.mem_insert_self [(← mkFreshLevelMVar)]) t (← mkFreshExprMVar none) a.toExpr tset.toExpr)
-- TODO THIS IS BROKEN!!!
                                     | .lo => do return (mkApp6 (.const `Eq.subst [(← mkFreshLevelMVar)]) t (.lam  `x t (mkApp4 (.const `Membership.mem [← mkFreshLevelMVar, ← mkFreshLevelMVar]) t (← mkFreshExprMVar none) (.bvar 0) s) .default) (← mkFreshExprMVar none) (← mkFreshExprMVar none) aInst.toExpr (mkApp4 (.const `Finset.mem_insert_self [(← mkFreshLevelMVar)]) t cl a.toExpr s)));
                  check aInParent;
                  if b' == 0 then return [(name, aInParent)] else
                  let newBoundType := mkApp4 (.const `LT.lt [u]) (.const `Nat []) (← mkFreshExprMVar none) (mkNatLit b'.pred) (mkApp2 (.const `Finset.card levels) t tset.toExpr);
                  let newBoundProof := mkApp6 (.const `Eq.subst [v]) (.const `Nat []) (.lam `x (.const `Nat []) (mkApp4 (.const `LT.lt [u]) (.const `Nat []) (← mkFreshExprMVar none) (mkNatLit b'.pred) (.bvar 0)) .default) (← mkFreshExprMVar none) (← mkFreshExprMVar none) (mkApp4 (.const `Eq.symm [v]) (.const `Nat []) (mkApp2 (.const `Finset.card levels) t tset.toExpr) (← mkFreshExprMVar none) atCard.toExpr) (mkApp4 (.const `Nat.pred_lt_pred []) (mkNatLit b') (mkApp2 (.const `Finset.card levels) t s) (.app (.const `Nat.succ_ne_zero []) (mkNatLit b'.pred)) (.fvar bineqVar));
                  let newBoundType ← instantiateMVars newBoundType;
                  let newBoundProof ← instantiateMVars newBoundProof;
                  check newBoundType;
                  check newBoundProof;
                  let ngs ← (← getMainGoal).assertHypotheses #[{ userName := newBoundName, type := newBoundType, value := newBoundProof }];
                  replaceMainGoal [ngs.snd];
                  let recCall ← doPick mode names newBoundName;
                  let some aNotInt := (← getLCtx).findFromUserName? aNotIntName | throwError ("Could not find declaration " ++ aNotIntName ++ " in current context!");
                  (match mode with
                    | .eq => recCall.forA (λ i => diffHyp name aNotInt.toExpr i)
                    | .lo => do
                             let (recHead :: _) := recCall | throwError "Nothing picked in the previous level!";
                             ltHyp name aNotInt.toExpr recHead);
                  let recCall ← recCall.mapM (upgradeProof cl aInst.toExpr);
                  return (name, aInParent) :: recCall;
        }}
      | .lo => do log "mode .lo"; return []
-- tactic.rcases none ``(pick_one_lo (lt_of_le_of_lt (nat.zero_le %%b) %%bineq)) (tactic.rcases_patt.tuple (list.map tactic.rcases_patt.one [elemname, subsetname, atcardname, anotintname, ainstname]))
--     subset ← tactic.resolve_name subsetname,
--     atcard ← tactic.resolve_name atcardname,
--     match b.to_nat with
--     | some b' := do {
--         -- We have to trust bpred is b-1 here
--         newineqexpr ← tactic.to_expr ``(%%(reflect b'.pred) < (finset.card %%subset)),
--         newineqproof ← tactic.to_expr ``(@eq.subst nat (λ x, %%(reflect b'.pred) < x) _ _ (eq.symm %%atcard) (nat.pred_lt_pred (nat.succ_ne_zero %%(reflect b'.pred)) %%bineq)),
--         newboundname ← tactic.get_unused_name "newb",
--         tactic.assertv newboundname newineqexpr newineqproof,
--         simpdefault ← simp_lemmas.mk_default,
--         localbound ← tactic.get_local newboundname,
--         tactic.simp_hyp simpdefault [] localbound,
--         localbound ← tactic.get_local newboundname,
--         rec ← pick n names.tail localbound,
--         elem ← tactic.get_local elemname,
--         atnotint ← tactic.get_local anotintname,
--         match mode with
--         | pick_mode.eq := list.mmap' (λ i, pick_diff elemname atnotint i) rec
--         | pick_mode.lo := pick_lt elemname atnotint rec.head
--         end,
--         ainst ← tactic.get_local ainstname,
--         rec ← list.mmap (λ i, pick_upgrade mode ainst i) rec,
--         elem ← tactic.get_local elemname,
--         subset ← tactic.get_local subsetname,
--         ainst ← tactic.get_local ainstname,
--         -- tactic.trace ainst,
--         ainparent ← match mode with
--                     | pick_mode.eq := tactic.to_expr ``(@eq.subst _ (λ x, %%elem ∈ x) _ _ %%ainst (finset.mem_insert_self %%elem %%subset))
--                     | pick_mode.lo := do {
--                                         loclass ← tactic.to_expr ``(linear_order %%α),
--                                         loinst ← tactic.mk_instance loclass,
--                                         tactic.to_expr ``(@eq.subst _ (λ x, %%elem ∈ x) _ _ %%ainst (@finset.mem_insert_self _ (%%loinst).decidable_eq %%elem %%subset))
--                                       }
--                     end,
--         tactic.clear_lst [ainstname, anotintname, atcardname, newboundname, subsetname],
--         return ((elemname, ainparent) :: rec)
--       }
--     | none := tactic.fail "Somehow the bound was not a nat"
--     end

-- def pick [Monad m] [MonadLCtx m] [MonadError m] {α : Type} (k : ℕ) (s : Finset α) (names : List Name) : tactic --:=
-- --(stexp : parse (tk "from" *> texpr)) (names : parse (with_ident_list)) : tactic :=
-- -- do
-- | `(tactic| fail "wines suck")
--   -- if k ≠ names.length then `(tactic| fail "Not enough names.") else `(tactic| fail "wines suck")
-- --   sexp ← tactic.i_to_expr stexp,
-- --   ineqexp ← tactic.to_expr ``(_ < (finset.card %%sexp)),
-- --   exp ← tactic.find_assumption ineqexp,
-- --   etype ← tactic.infer_type exp,
-- --   `(%%b < (finset.card %%l)) ← tactic.infer_type exp,
-- --   `(finset %%α) ← tactic.infer_type l,
-- --   -- tactic.trace α,
-- --   mode ← pick_detect_mode α,
-- --   match b.to_nat with
-- --   | some c := if c.succ < k then tactic.fail "Picking too many elements!" else
-- --               match k with
-- --               | nat.zero := tactic.fail "Pick at least one element!"
-- --               | (nat.succ k') := do {
-- --                   newobjs ← pick mode k' names exp,
-- --                   -- list.mmap' tactic.trace newobjs,
-- --                   list.mmap' (λ i, pick_wrapup l i) newobjs
-- --                 }
-- --               end
-- --   | none := tactic.fail ("Assumption " ++ (to_string exp) ++ " is not a good bound.")
-- --   end

-- TODO Define this one in terms of parseLBound
private partial def isLBound (s : Expr) : (l : LocalDecl) → TacticM (Option (Name × Expr))
  | .cdecl _ _ name e _ _ => (match e.getAppFn with
    | .const `LT.lt _ => (match e.getAppArgs with
      | #[_, _, b, s'] =>  (match s'.getAppFn with
        | .const `Finset.card _ => (match s'.getAppArgs with
          | #[_, s''] => do if (← isDefEq s'' s) then return (some (name, e)) else return none
          | _ => do return none)
        | _ => do return none)
      | _  => do return none)
    | _ => return none)
  | .ldecl .. => return none

def pickFn (is :  List Name) (s : TSyntax `term) : TacticM Unit :=
withMainContext do
  let sexp ← Lean.Elab.Term.elabTerm s none;
  let ctx ← getLCtx;
  let w ← ctx.findDeclM? (isLBound sexp);
  (match w with
    | none => throwError "No lower-bound found in context!"
    | some (sBoundName, sBoundExp) => do (match (← parseLBound sBoundExp) with
      | none => throwError ("Could not parse lower-bound expression " ++ sBoundExp)
      | some (b, _, sexp, _) => (match b.numeral? with
        | none => throwError ("For some reason lower-bound " ++ b ++ " is not ℕ!")
        | some n => if n.succ < is.length then throwError "Picking too many elements!" else
                  do
                    match (← inferType sexp) with
                      | .app (.const `Finset _) α => do
                                                     (match (← detectMode α) with
                                                       | (.eq, _) => return ()
                                                       | (.lo, _) => do
                                                                  let insList ← doPick .eq is sBoundName;
                                                                  insList.forA (wrapup sexp);)
                      | _ => throwError ("Could not find the element type of " ++ s))))

syntax (name := pick) "pick " (ppSpace ident)+ fromTerm : tactic

@[tactic pick] elab_rules : tactic
  | `(tactic| pick $name from $s) => pickFn [getNameOfIdent' name.raw] s
  | `(tactic| pick $name $names:ident* from $s) =>  pickFn ((name :: names.data).map (fun i => getNameOfIdent' i.raw)) s
