import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice

open Lean Lean.Meta Lean.Parser.Tactic Lean.Parser.Term Lean.Elab.Tactic Lean.Elab.Term

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

syntax "throwNameError " term : term

macro_rules
  | `(throwNameError $msg:term) => `(throwError ("Could not find " ++ $msg ++ " in the current context!"))

private def diffHyp (a : Name) (aNotInt : Expr) (info : Name × Expr) : TacticM PUnit :=
withMainContext do {
  let some aDecl := (← getLCtx).findFromUserName? a | throwNameError a;
  let some bDecl := (← getLCtx).findFromUserName? info.fst | throwNameError info.fst;
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

private def ltHyp (a : Name) (aLtt : Expr) (info : Name × Expr) : TacticM Unit :=
withMainContext do {
  let .str _ aStr := a | throwError ("Name " ++ a ++ " is not a string?");
  let .str _ bStr := info.fst | throwError ("Name " ++ info.fst ++ " is not a string?");
  let some aDecl := (← getLCtx).findFromUserName? a | throwNameError a;
  let some bDecl := (← getLCtx).findFromUserName? info.fst | throwNameError info.fst;
  let ltExpr ← instantiateMVars (mkApp4 (.const `LT.lt [← mkFreshLevelMVar]) aDecl.type (← mkFreshExprMVar none) aDecl.toExpr bDecl.toExpr);
  let ltProof ← instantiateMVars (mkApp2 aLtt bDecl.toExpr info.snd);
  let uname := aStr ++ "Lt" ++ bStr;
  let ltName ← getUnusedUserName uname;
  check ltExpr;
  check ltProof;
  let ngs ← (← getMainGoal).assertHypotheses #[{ userName := ltName, type := ltExpr, value := ltProof }];
  replaceMainGoal [ngs.snd];
  return()
}

private def wrapup (s : Expr) (info : Name × Expr) : TacticM Unit :=
withMainContext do {
  let .str _ aStr := info.fst | throwError ("Name " ++ info.fst ++ " is not a string?");
  let uname := aStr ++ "Ins";
  let n ← getUnusedUserName uname;
  -- TODO Maybe infer also the element type from the set type
  let sType ← inferType s;
  let some aDecl := (← getLCtx).findFromUserName? info.fst | throwNameError info.fst;
  let inExpr ← instantiateMVars (mkApp5 (.const `Membership.mem [← mkFreshLevelMVar, ← mkFreshLevelMVar]) (← mkFreshTypeMVar) sType (← mkFreshExprMVar none) aDecl.toExpr s);
  let inVal ← instantiateMVars info.snd;
  -- DO NOT REMOVE
  check inExpr;
  check inVal;
  let ngs ← (← getMainGoal).assertHypotheses #[{ userName := n, type := inExpr, value := inVal }];
  replaceMainGoal [ngs.snd];
}

private def detectMode (α : Expr) : TacticM (Expr × Option Expr) :=
  do {
    let loClass := (Expr.app (.const `LinearOrder [← mkFreshLevelMVar]) α);
    let e ← synthInstance loClass;
    return (mkApp2 (.const `LinearOrder.decidableEq [← mkFreshLevelMVar]) α e, e)
  } <|>
  do {
    let u ← mkFreshLevelMVar;
    let eqClass := (Expr.app (.const `DecidableEq [u]) α);
    let e ← synthInstance eqClass;
    return (e, none)
  } <|> throwError ("No LinearOrder or DecidableEq in type " ++ α)

private def upgradeProof (decEqExpr : Expr) (aInst : Expr) (info : Name × Expr) : TacticM (Name × Expr) :=
withMainContext do {
  let .app (.app (.app (.const `Eq _) sType) insExpr) sExpr ← inferType aInst | throwError ("Could not parse type of expression " ++ aInst);
  let some bDecl := (← getLCtx).findFromUserName? info.fst | throwNameError info.fst;
  let eType ← inferType bDecl.toExpr;
  let subsetEqExpr := mkApp6 (.const `Eq.subst [(← mkFreshLevelMVar)]) sType (.lam `x sType (mkApp5 (.const `Membership.mem [← mkFreshLevelMVar, ← mkFreshLevelMVar]) (← mkFreshExprMVar none) sType (← mkFreshExprMVar none) bDecl.toExpr (.bvar 0)) .default) insExpr sExpr aInst (mkApp6 (.const `Finset.mem_insert_of_mem [← mkFreshLevelMVar]) eType decEqExpr (← mkFreshExprMVar none) bDecl.toExpr (← mkFreshExprMVar none) info.snd);
  check subsetEqExpr;
  return (info.fst, subsetEqExpr)
}

private def parseLBound : Expr → TacticM (Option (Expr × Expr × Expr × List Level))
| .app (.app (.app (.app (.const `LT.lt _) _) _) b) (.app (.app (.const `Finset.card u) t) s) => return some (b, t, s, u)
| _ => return none

-- Invariant: every level returns a list of pairs where each pair is:
-- fst: the name of a member obtained in a recursive call
-- snd: the name of the fact that that member belongs to the rest of the set of this level
-- It is the responsibility of each level to upgrade the recursive list at the calling level
private def doPick : List Name → Expr → TacticM (List (Name × Expr))
| [], _ => return []
| (name :: names), bineq => withMainContext do
    let subsetName ← getUnusedUserName "t";
    let atCardName ← getUnusedUserName "atCard";
    let aNotIntName ← getUnusedUserName "aNotInt";
    let aInstName ← getUnusedUserName "aInst";
    let bineqType ← match bineq with | .fvar id => id.getType | _ => inferType bineq;
    let bineqType ← instantiateMVars bineqType;
    let some (lowerBound, ty, s, levels) ← parseLBound bineqType | throwError bineq ++ " is not a lower-bound expression!";
    let (eqCls, loCls) ← detectMode ty;
    let mg ← getMainGoal;
    let sType ← inferType s;
    let u ← mkFreshLevelMVar;
    let pickLemma ← (match loCls with
      | none => return (mkApp4 (.const `Pick.pick_one_eq []) ty s eqCls (mkApp7 (.const `lt_of_le_of_lt [u]) (.const `Nat []) (← mkFreshExprMVar none) (.const `Nat.zero []) lowerBound (mkApp2 (.const `Finset.card levels) ty s) (.app (.const `Nat.zero_le []) lowerBound) bineq))
      | some cls => return (mkApp4 (.const `Pick.pick_one_lo []) ty s cls (mkApp7 (.const `lt_of_le_of_lt [u]) (.const `Nat []) (← mkFreshExprMVar none) (.const `Nat.zero []) lowerBound (mkApp2 (.const `Finset.card levels) ty s) (.app (.const `Nat.zero_le []) lowerBound) bineq)));
    -- DO NOT REMOVE
    let pickLemma ← instantiateMVars pickLemma;
    check pickLemma;
    let pls ← pickLemma.toSyntax;
    let ngs ← Std.Tactic.RCases.rcases #[(none, pls)] (.tuple' (List.map (.one (mkNullNode)) [name, subsetName, atCardName, aNotIntName, aInstName])) mg;
    replaceMainGoal ngs;
    let u ← mkFreshLevelMVar;
    let v ← mkFreshLevelMVar;
    let some b' := lowerBound.numeral? | throwError lowerBound ++ " is not a number!";
    -- TODO Figure out if there is an elegant way to reload the context
    withMainContext do {
      let some a := (← getLCtx).findFromUserName? name | throwNameError name;
      let some atCard := (← getLCtx).findFromUserName? atCardName | throwNameError atCardName;
      let some tset := (← getLCtx).findFromUserName? subsetName | throwNameError subsetName;
      let some aInst := (← getLCtx).findFromUserName? aInstName | throwNameError aInstName;
      -- let clearArray := #[a.fvarId, atCard.fvarId, tset.fvarId, aInst.fvarId];
      let aInParent ← instantiateMVars (mkApp6 (.const `Eq.subst [(← mkFreshLevelMVar)]) sType (.lam  `x sType (mkApp5 (.const `Membership.mem [← mkFreshLevelMVar, ← mkFreshLevelMVar]) ty sType (← mkFreshExprMVar none) a.toExpr (.bvar 0)) .default) (← mkFreshExprMVar none) s aInst.toExpr (mkApp4 (.const `Finset.mem_insert_self [(← mkFreshLevelMVar)]) ty eqCls a.toExpr tset.toExpr));
      check aInParent;
      if b' == 0 then return [(name, aInParent)] else
      let newBoundProof := mkApp6 (.const `Eq.subst [v]) (.const `Nat []) (.lam `x (.const `Nat []) (mkApp4 (.const `LT.lt [u]) (.const `Nat []) (← mkFreshExprMVar none) (mkNatLit b'.pred) (.bvar 0)) .default) (← mkFreshExprMVar none) (← mkFreshExprMVar none) (mkApp4 (.const `Eq.symm [v]) (.const `Nat []) (mkApp2 (.const `Finset.card levels) ty tset.toExpr) (← mkFreshExprMVar none) atCard.toExpr) (mkApp4 (.const `Nat.pred_lt_pred []) (mkNatLit b') (mkApp2 (.const `Finset.card levels) ty s) (.app (.const `Nat.succ_ne_zero []) (mkNatLit b'.pred)) bineq);
      let newBoundProof ← instantiateMVars newBoundProof;
      check newBoundProof;
      let recCall ← doPick names newBoundProof;
      let some aNotInt := (← getLCtx).findFromUserName? aNotIntName | throwError ("Could not find declaration " ++ aNotIntName ++ " in current context!");
      (match loCls with
        | none => recCall.forA (λ i => diffHyp name aNotInt.toExpr i)
        | some _ => do
                 let (recHead :: _) := recCall | throwError "Nothing picked in the previous level!";
                 ltHyp name aNotInt.toExpr recHead);
      let recCall ← recCall.mapM (upgradeProof eqCls aInst.toExpr);
      return (name, aInParent) :: recCall;
    }

private partial def isLBound (s : Expr) : (l : LocalDecl) → TacticM (Option (Name × FVarId))
  | .cdecl _ id name t _ _ => do
                          let some (_, _, s', _) ← parseLBound t | return none;
                          if (← isDefEq s' s) then return (some (name, id)) else return none
  | .ldecl .. => return none

def pickFn (is :  List Name) (s : TSyntax `term) : TacticM Unit :=
withMainContext do
  let sexp ← Lean.Elab.Term.elabTerm s none;
  let ctx ← getLCtx;
  let w ← ctx.findDeclM? (isLBound sexp);
  match w with
    | none => throwError "No lower-bound found in context!"
    | some (sBoundName, sBoundID) => do
      let sbt ← sBoundID.getType;
      match (← parseLBound sbt) with
      | none => throwError ("Could not parse lower-bound expression " ++ sBoundName)
      | some (b, _, sexp, _) => (match b.numeral? with
        | none => throwError ("For some reason lower-bound " ++ b ++ " is not ℕ!")
        | some n => if n.succ < is.length then throwError "Picking too many elements!" else
          do
          match (← inferType sexp) with
            | .app (.const `Finset _) _ => do
              let insList ← doPick is (.fvar sBoundID)
              insList.forA (wrapup sexp);
            | _ => throwError ("Could not find the element type of " ++ s))

syntax (name := pick) "pick " (ppSpace ident)+ fromTerm : tactic

@[tactic pick] elab_rules : tactic
  | `(tactic| pick $names:ident* from $s) => pickFn (names.data.map (λ i ↦ getNameOfIdent' i.raw)) s
