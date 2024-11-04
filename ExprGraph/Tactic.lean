import ExprGraph.Expr
import LeanExtras.Frontend

open Lean Elab Tactic ExprGraph

def Lean.Expr.addId (e : Expr) : MetaM (WithId Expr) := do
  let mut id : UInt64 := hash e
  let decls := (← getLCtx).fvarIdToDecl
  for (fvarId, localDecl) in decls do
    id := mixHash id (hash fvarId)
    id := mixHash id (hash localDecl)
  return ⟨e, id⟩

def Lean.Expr.mkExprGraphWithLCtxCaching (expr : Expr) (compressUniverses? compressProofs? : Bool) : 
      MonadCacheT (WithId Expr) (WithId Node × ExprGraph) MetaM (WithId Node × ExprGraph) := do
  let expr ← expr.addId
  checkCache expr fun _ => do
  let lctx ← getLCtx
  let (node, graph) ← expr.val.mkExprGraph compressUniverses? compressProofs?
  let mut outGraph := graph
  for (fvarId, decl) in lctx.fvarIdToDecl do
    if decl.isAuxDecl || decl.isImplementationDetail then continue
    let (fvNode, fvGraph) ← (Expr.fvar fvarId).mkExprGraph compressUniverses? compressProofs?
    outGraph := outGraph ∪ fvGraph |>.insertEdge ⟨.localDecl, node.id⟩ fvNode node
  return (node, outGraph)

def Lean.Expr.mkExprGraphWithLCtx (expr : Expr) (compressUniverses? compressProofs? : Bool) : 
    MetaM (WithId Node × ExprGraph) := do
  expr.mkExprGraphWithLCtxCaching compressUniverses? compressProofs? |>.run

def Lean.MVarId.mkExprGraphCaching (id : MVarId) (compressUniverses? compressProofs? : Bool) : 
    MonadCacheT (WithId Expr) (WithId Node × ExprGraph) MetaM (WithId Node × ExprGraph) := 
    id.withContext do
  instantiateMVarDeclMVars id
  let tp ← id.getType
  tp.mkExprGraphWithLCtxCaching compressUniverses? compressProofs?

def Lean.MVarId.mkExprGraph (id : MVarId) (compressUniverses? compressProofs? : Bool) : 
    MetaM (WithId Node × ExprGraph) := 
  id.mkExprGraphCaching compressUniverses? compressProofs? |>.run

def mkGoalStateExprGraphCaching (goals : List MVarId) (compressUniverses? compressProofs? : Bool) :
    MonadCacheT (WithId Expr) (WithId Node × ExprGraph) MetaM (WithId Node × ExprGraph) := do
  let mut id : UInt64 := hash "goalState"
  for goal in goals do
    let tp ← goal.getType
    id := mixHash id (hash tp)
  let outNode : WithId Node := ⟨.goalState, id⟩
  let mut outGraph := {}
  for (goal, idx) in goals.toArray.zipWithIndex do
    let (goalNode, goalGraph) ← goal.mkExprGraphCaching compressUniverses? compressProofs?
    outGraph := outGraph ∪ goalGraph |>.insertEdge ⟨.goal idx, id⟩ goalNode outNode
  return (outNode, outGraph)

def mkGoalStateExprGraph (goals : List MVarId) (compressUniverses? compressProofs? : Bool) :
    MetaM (WithId Node × ExprGraph) := 
  mkGoalStateExprGraphCaching goals compressUniverses? compressProofs? |>.run
