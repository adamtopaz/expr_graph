import ExprGraph.Expr
import LeanExtras.Frontend

open Lean Elab Tactic ExprGraph

namespace Lean.Elab.TacticInfo

def isOriginal (i : TacticInfo) : Bool := 
  match i.stx.getHeadInfo with
  | .original .. => true
  | _ => false

def name? (i : TacticInfo) : Option Name := 
  match i.stx with
  | .node _ n _ => some n
  | _ => none

def isSubstantive (i : TacticInfo) : Bool := 
  match i.name? with
  | none => false
  | some `null => false
  | some ``cdot => false
  | some ``cdotTk => false
  | some ``Lean.Parser.Term.byTactic => false
  | some ``Lean.Parser.Tactic.tacticSeq => false
  | some ``Lean.Parser.Tactic.tacticSeq1Indented => false
  | some ``Lean.Parser.Tactic.«tactic_<;>_» => false
  | some ``Lean.Parser.Tactic.paren => false
  | _ => true

def getUsedConstantsAsSet (t : TacticInfo) : NameSet :=
  t.goalsBefore
    |>.filterMap t.mctxAfter.getExprAssignmentCore?
    |>.map Expr.getUsedConstantsAsSet
    |>.foldl .union .empty

end Lean.Elab.TacticInfo


