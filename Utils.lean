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

namespace Lean.Elab.ContextInfo

def runCoreM' (info : ContextInfo) (x : CoreM α) : IO α := do
  --let initHeartbeats ← IO.getNumHeartbeats
  Prod.fst <$> x.toIO
    { currNamespace := info.currNamespace, 
      openDecls := info.openDecls,
      fileName := "<InfoTree>", 
      fileMap := default,
      initHeartbeats := 0, --initHeartbeats,
      maxHeartbeats := maxHeartbeats.get info.options,
      options := info.options }
    { env := info.env, ngen := info.ngen }

def runMetaM' (info : ContextInfo) (lctx : LocalContext) (x : MetaM α) : IO α := do
  Prod.fst <$> info.runCoreM' (x.run { lctx := lctx } { mctx := info.mctx })

def ppGoals' (ctx : ContextInfo) (goals : List MVarId) : IO Format :=
  if goals.isEmpty then
    return "no goals"
  else
    ctx.runMetaM' {} (return Std.Format.prefixJoin "\n" (← goals.mapM (Meta.ppGoal ·)))

end Lean.Elab.ContextInfo
