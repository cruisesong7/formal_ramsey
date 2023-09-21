import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Finset.Powerset

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

lemma pick_one_lo {α : Type} {s : Finset α} [LinearOrder α] : 0 < s.card → ∃! (a : α), a ∈ s ∧ ∃! (t : Finset α), t ∈ s.powerset ∧ (t.card = s.card.pred) ∧ (∀ a' ∈ t, a < a') ∧ (insert a t = s) := by
  intro sPos
  rw [Finset.card_pos] at sPos
  let a := s.min' sPos
  let t := s.erase a
  use a
  apply And.intro <;> simp (config := { zeta := false })
  · apply And.intro
    · exact Finset.min'_mem s sPos
    · use t
      simp (config := { zeta := false })
      apply And.intro
      · apply And.intro
        · exact Finset.erase_subset (s.min' sPos) s
        · apply And.intro
          · exact Finset.card_erase_of_mem (Finset.min'_mem s sPos)
          · apply And.intro
            · intro b bNotMin bIns
              rw [← ne_eq] at bNotMin
              exact lt_of_le_of_ne (Finset.min'_le s b bIns) bNotMin.symm
            · exact Finset.insert_erase (Finset.min'_mem s sPos)
      · intro t' _ _ t'Min t'Insert
        have aNotInt' : a ∉ t' := λ aInt' ↦ lt_irrefl a (t'Min a aInt')
        have repl := Finset.erase_insert aNotInt'
        rw [t'Insert] at repl
        simp [repl]
  · intro b bIns tUniqueProp
    have tProp := ExistsUnique.exists tUniqueProp
    rcases tProp with ⟨t', _, _, bMin, bInsert⟩
    apply le_antisymm
    · have minIns := Finset.min'_mem s sPos
      simp [← bInsert] at minIns
      cases minIns
      next bVal =>
        rw [← bVal]
        simp [bInsert]
      next minInt' =>
        simp [bInsert] at minInt'
        exact le_of_lt (bMin (s.min' sPos) minInt')
    · exact Finset.min'_le s b bIns

instance decPickatProp {α : Type} [LinearOrder α] : ∀ (s : Finset α) (a : α), DecidablePred (λ (t : Finset α) ↦ (t.card = s.card.pred) ∧ (∀ a' ∈ t, a < a') ∧ (insert a t = s)) := by
  intros s a
  unfold DecidablePred
  intros t
  cases s.decidableNonempty with
  | isFalse sEmpty =>
    apply isFalse
    intro tProp
    rcases tProp with ⟨_, _, tInsert⟩
    rw [← tInsert] at sEmpty
    exact sEmpty (Finset.insert_nonempty a t)
  | isTrue sNonempty =>
    cases s.decidableMem a with
    | isFalse aNonMem =>
      apply isFalse
      intro tProp
      rcases tProp with ⟨_, _, tInsert⟩
      simp [← tInsert] at aNonMem
    | isTrue aMem =>
      by_cases a = (s.min' sNonempty)
      · by_cases t = s.erase a
        · apply isTrue
          simp
          apply And.intro <;> rw [h]
          · exact Finset.card_erase_of_mem aMem
          · apply And.intro
            · intros b bInt
              simp at bInt
              rw [← ne_eq] at bInt
              subst a
              exact lt_of_le_of_ne (Finset.min'_le s b bInt.right) bInt.left.symm
            · exact Finset.insert_erase aMem
        · apply isFalse
          intro tProp
          rcases tProp with ⟨_, aMin, tInsert⟩
          have aNotInt : a ∉ t := λ aInt ↦ lt_irrefl a (aMin a aInt)
          have absd := Finset.erase_insert aNotInt
          rw [tInsert] at absd
          simp [absd] at h
      · apply isFalse
        simp
        intros _ aMin tInsert
        have minIns := Finset.min'_mem s sNonempty
        simp [← tInsert] at minIns
        cases minIns with
        | inl aMin =>
          simp [tInsert] at aMin
          simp [aMin] at h
        | inr minInt =>
          simp [tInsert] at minInt
          exact (not_lt_of_le (Finset.min'_le s a aMem)) (aMin (s.min' sNonempty) minInt)
  done

instance decPickaProp {α : Type} [LinearOrder α] : ∀ (s : Finset α), DecidablePred (λ (a : α) ↦ ∃! (t : Finset α), t ∈ s.powerset ∧ ((t.card = s.card.pred) ∧ (∀ a' ∈ t, a < a') ∧ (insert a t = s))) := by
  intros s
  unfold DecidablePred
  intro a
  cases Nat.zero.decLt s.card with
  | isFalse sCard =>
    apply isFalse
    intro atProp
    rcases (ExistsUnique.exists atProp) with ⟨t, _, _, _, tInsert⟩
    simp [← tInsert] at sCard
  | isTrue sCardPos =>
    rw [Finset.card_pos] at sCardPos
    cases s.decidableMem a with
    | isFalse aNonMem =>
      apply isFalse
      intro tProp
      rcases (ExistsUnique.exists tProp) with ⟨t, _, ⟨_, _, tInsert⟩⟩
      simp [← tInsert] at aNonMem
    | isTrue aMem =>
      by_cases a = (s.min' sCardPos)
      · apply isTrue
        simp
        use s.erase a
        apply And.intro <;> simp
        · apply And.intro
          · exact Finset.erase_subset a s
          · apply And.intro
            · exact Finset.card_erase_of_mem aMem
            · apply And.intro
              · intros b bNea bIns
                rw [h] at bNea ⊢
                rw [← ne_eq] at bNea
                exact lt_of_le_of_ne (Finset.min'_le s b bIns) bNea.symm
              · exact Finset.insert_erase aMem
        · intros t' _ _ aMin t'Ins
          have aNotInt : a ∉ t' := λ aInt ↦ lt_irrefl a (aMin a aInt)
          have t'Val := Finset.erase_insert aNotInt
          rw [t'Ins] at t'Val
          rw [← t'Val]
      · apply isFalse
        simp
        intro tUniqueProp
        rcases (ExistsUnique.exists tUniqueProp) with ⟨t, _, ⟨_, aMin, tInsert⟩⟩
        have minIns := Finset.min'_mem s sCardPos
        simp [← tInsert] at minIns
        cases minIns with
        | inl aMin =>
          simp [tInsert] at aMin
          simp [aMin] at h
        | inr minInt =>
          simp [tInsert] at minInt
          exact (not_lt_of_le (Finset.min'_le s a aMem)) (aMin (s.min' sCardPos) minInt)
  done

end Pick

syntax "throwNameError " term : term

macro_rules
  | `(throwNameError $msg:term) => `(throwError ("Could not find " ++ $msg ++ " in the current context!"))

private def diffHyp (a : Name) (aNotInt : Expr) (info : Name × Expr × FVarSubst) : TacticM PUnit :=
withMainContext do {
  let some aDecl := (← getLCtx).findFromUserName? a | throwNameError a;
  let some bDecl := (← getLCtx).findFromUserName? info.fst | throwNameError info.fst;
  let .app (.const `Not _) setEqExpr ← inferType aNotInt | throwError ("Could not parse expression " ++ aNotInt);
  let .app (.app (.app (.app (.app (.const `Membership.mem levels) eType) sType) memInst) _) s := setEqExpr | throwError ("Could not parse expression " ++ aNotInt);
  let neqExpr ← instantiateMVars (mkApp3 (.const `Ne [(← mkFreshLevelMVar)]) eType aDecl.toExpr bDecl.toExpr);
  let neqProof ← instantiateMVars (info.snd.snd.apply (.lam `x (mkApp3 (.const `Eq [← mkFreshLevelMVar]) eType aDecl.toExpr bDecl.toExpr) (.app aNotInt (mkApp6 (.const `Eq.subst [(← mkFreshLevelMVar)]) eType (.lam `y eType (mkApp5 (.const `Membership.mem levels) eType sType memInst (.bvar 0) s) .default) bDecl.toExpr aDecl.toExpr (mkApp4 (.const `Eq.symm [(← mkFreshLevelMVar)]) (← mkFreshTypeMVar) aDecl.toExpr bDecl.toExpr (.bvar 0)) info.snd.fst)) .default));
  let neqName ← getUnusedUserName (a ++ "Neq" ++ info.fst);
  -- DO NOT REMOVE
  check neqExpr;
  check neqProof;
  let ngs ← (← getMainGoal).assertHypotheses #[{ userName := neqName, type := neqExpr, value := neqProof }];
  replaceMainGoal [ngs.snd];
}

private def ltHyp (a : Name) (aLtt : Expr) (info : Name × Expr × FVarSubst) : TacticM Unit :=
withMainContext do {
  let .str _ aStr := a | throwError ("Name " ++ a ++ " is not a string?");
  let .str _ bStr := info.fst | throwError ("Name " ++ info.fst ++ " is not a string?");
  let some aDecl := (← getLCtx).findFromUserName? a | throwNameError a;
  let some bDecl := (← getLCtx).findFromUserName? info.fst | throwNameError info.fst;
  let ltExpr ← instantiateMVars (mkApp4 (.const `LT.lt [← mkFreshLevelMVar]) aDecl.type (← mkFreshExprMVar none) aDecl.toExpr bDecl.toExpr);
  let ltProof ← instantiateMVars (info.snd.snd.apply (mkApp2 aLtt bDecl.toExpr info.snd.fst));
  let uname := aStr ++ "Lt" ++ bStr;
  let ltName ← getUnusedUserName uname;
  check ltExpr;
  check ltProof;
  let ngs ← (← getMainGoal).assertHypotheses #[{ userName := ltName, type := ltExpr, value := ltProof }];
  replaceMainGoal [ngs.snd];
  return()
}

private def wrapup (s : Expr) (info : Name × Expr × FVarSubst) : TacticM Unit :=
withMainContext do {
  let .str _ aStr := info.fst | throwError ("Name " ++ info.fst ++ " is not a string?");
  let uname := aStr ++ "Ins";
  let n ← getUnusedUserName uname;
  -- TODO Maybe infer also the element type from the set type
  let sType ← inferType s;
  let some aDecl := (← getLCtx).findFromUserName? info.fst | throwNameError info.fst;
  let inExpr ← instantiateMVars (mkApp5 (.const `Membership.mem [← mkFreshLevelMVar, ← mkFreshLevelMVar]) (← mkFreshTypeMVar) sType (← mkFreshExprMVar none) aDecl.toExpr s);
  let inVal ← instantiateMVars (info.snd.snd.apply info.snd.fst);
  -- DO NOT REMOVE
  check inExpr;
  check inVal;
  let ngs ← (← getMainGoal).assertHypotheses #[{ userName := n, type := inExpr, value := inVal }];
  replaceMainGoal [ngs.snd];
}

private def upgradeProof (decEqExpr : Expr) (aInst : Expr) (info : Name × Expr × FVarSubst) : TacticM (Name × Expr × FVarSubst) :=
withMainContext do {
  let .app (.app (.app (.const `Eq _) sType) insExpr) sExpr ← inferType aInst | throwError ("Could not parse type of expression " ++ aInst);
  let some bDecl := (← getLCtx).findFromUserName? info.fst | throwNameError info.fst;
  let eType ← inferType bDecl.toExpr;
  let subsetEqExpr := info.snd.snd.apply (mkApp6 (.const `Eq.subst [(← mkFreshLevelMVar)]) sType (.lam `x sType (mkApp5 (.const `Membership.mem [← mkFreshLevelMVar, ← mkFreshLevelMVar]) (← mkFreshExprMVar none) sType (← mkFreshExprMVar none) bDecl.toExpr (.bvar 0)) .default) insExpr sExpr aInst (mkApp6 (.const `Finset.mem_insert_of_mem [← mkFreshLevelMVar]) eType decEqExpr (← mkFreshExprMVar none) bDecl.toExpr (← mkFreshExprMVar none) info.snd.fst));
  check subsetEqExpr;
  return (info.fst, subsetEqExpr, info.snd.snd)
}

private def parseLBound : Expr → TacticM (Option (Expr × Expr × Expr × List Level))
| .app (.app (.app (.app (.const `LT.lt _) _) _) b) (.app (.app (.const `Finset.card u) t) s) => return some (b, t, s, u)
| _ => return none

-- Invariant: every level returns a list of pairs where each pair is:
-- fst: the name of a member obtained in a recursive call
-- snd: the name of the fact that that member belongs to the rest of the set of this level
-- It is the responsibility of each level to upgrade the recursive list at the calling level
private def doPick : List Name → Expr → TacticM (List (Name × Expr × FVarSubst))
| [], _ => return []
| (name :: names), bineq => withMainContext do
    let bineqType ← match bineq with | .fvar id => id.getType | _ => inferType bineq;
    let bineqType ← instantiateMVars bineqType;
    let some (lowerBound, ty, s, levels) ← parseLBound bineqType | throwError bineq ++ " is not a lower-bound expression!";
    let loClassExpr := (Expr.app (.const `LinearOrder [← mkFreshLevelMVar]) ty);
    let loClass ← synthInstance loClassExpr;
    let eqCls ← instantiateMVars (mkApp2 (.const `LinearOrder.decidableEq [← mkFreshLevelMVar]) ty loClass)
    let mg ← getMainGoal;
    let sType ← inferType s;
    let pickLemma ← instantiateMVars (mkApp4 (.const `Pick.pick_one_lo []) ty s loClass (mkApp7 (.const `lt_of_le_of_lt [← mkFreshLevelMVar]) (.const `Nat []) (← mkFreshExprMVar none) (.const `Nat.zero []) lowerBound (mkApp2 (.const `Finset.card levels) ty s) (.app (.const `Nat.zero_le []) lowerBound) bineq));
    check pickLemma;
    let a ← instantiateMVars (mkApp5 (.const `Finset.choose [← mkFreshLevelMVar]) ty (← mkFreshExprMVar none) (mkApp3 (.const `Pick.decPickaProp []) ty loClass s) s pickLemma);
    let tProp ← instantiateMVars (mkApp5 (.const `Finset.choose_property [← mkFreshLevelMVar]) ty (← mkFreshExprMVar none) (mkApp3 (.const `Pick.decPickaProp []) ty loClass s) s pickLemma);
    let t ← instantiateMVars (mkApp5 (.const `Finset.choose [← mkFreshLevelMVar]) (mkApp (.const `Finset [← mkFreshLevelMVar]) ty) (← mkFreshExprMVar none) (mkApp4 (.const `Pick.decPickatProp []) ty loClass s a) (mkApp2 (.const `Finset.powerset [← mkFreshLevelMVar]) ty s) tProp);
    check a;
    check t;
    let atSpec ← instantiateMVars (mkApp5 (.const `Finset.choose_property [← mkFreshLevelMVar]) (mkApp (.const `Finset [← mkFreshLevelMVar]) ty) (← mkFreshExprMVar none) (mkApp4 (.const `Pick.decPickatProp []) ty loClass s a) (mkApp2 (.const `Finset.powerset [← mkFreshLevelMVar]) ty s) tProp);
    let atCard := Expr.proj `And 0 atSpec;
    let aNotInt := Expr.proj `And 0 (.proj `And 1 atSpec);
    -- TODO Maybe use Finset.choose_spec instead?
    let aInst := Expr.proj `And 1 (.proj `And 1 atSpec);
    let u ← mkFreshLevelMVar;
    let v ← mkFreshLevelMVar;
    let some b' := lowerBound.numeral? | throwError lowerBound ++ " is not a number!";
    let aInParent ← instantiateMVars (mkApp6 (.const `Eq.subst [(← mkFreshLevelMVar)]) sType (.lam  `x sType (mkApp5 (.const `Membership.mem [← mkFreshLevelMVar, ← mkFreshLevelMVar]) ty sType (← mkFreshExprMVar none) a (.bvar 0)) .default) (← mkFreshExprMVar none) s aInst (mkApp4 (.const `Finset.mem_insert_self [(← mkFreshLevelMVar)]) ty eqCls a t));
    check aInParent;
    let some last := (← getLCtx).lastDecl | unreachable!;
    let aType ← inferType a;
    let aDecl ← mg.assertAfter last.fvarId name aType a;
    let aSubst := FVarSubst.insert FVarSubst.empty aDecl.fvarId a;
    replaceMainGoal [aDecl.mvarId];
    -- TODO Figure out if there is an elegant way to reload the context
    withMainContext do {
      if (b' == 0 || names.length == 0) then return [(name, aInParent, aSubst)] else
      let newBoundProof := mkApp6 (.const `Eq.subst [v]) (.const `Nat []) (.lam `x (.const `Nat []) (mkApp4 (.const `LT.lt [u]) (.const `Nat []) (← mkFreshExprMVar none) (mkNatLit b'.pred) (.bvar 0)) .default) (← mkFreshExprMVar none) (← mkFreshExprMVar none) (mkApp4 (.const `Eq.symm [v]) (.const `Nat []) (mkApp2 (.const `Finset.card levels) ty t) (← mkFreshExprMVar none) atCard) (mkApp4 (.const `Nat.pred_lt_pred []) (mkNatLit b') (mkApp2 (.const `Finset.card levels) ty s) (.app (.const `Nat.succ_ne_zero []) (mkNatLit b'.pred)) bineq);
      let newBoundProof ← instantiateMVars newBoundProof;
      check newBoundProof;
      let recCall ← doPick names newBoundProof;
      -- TODO Figure out if there is an elegant way to reload the context
      withMainContext do {
        let (recHead :: _) := recCall | throwError "Nothing picked in the previous level!";
        ltHyp name aNotInt recHead;
        let recCall ← recCall.mapM (upgradeProof eqCls aInst);
        return (name, aInParent, aSubst) :: recCall;
      }
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
