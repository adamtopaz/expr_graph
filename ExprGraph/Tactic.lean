import ExprGraph.Expr
import LeanExtras.Frontend

open Lean Elab Tactic ExprGraph

def Lean.Expr.mkExprGraphWithLCtx (expr : Expr) (compressUniverses? compressProofs? : Bool) : 
    MetaM (WithId Node × ExprGraph) := do
  let lctx ← getLCtx
  let (node, graph) ← expr.mkExprGraph compressUniverses? compressProofs?
  let mut outGraph := graph
  for (fvarId, decl) in lctx.fvarIdToDecl do
    if decl.isAuxDecl || decl.isImplementationDetail then continue
    let (fvNode, fvGraph) ← (Expr.fvar fvarId).mkExprGraph compressUniverses? compressProofs?
    outGraph := outGraph ∪ fvGraph |>.insertEdge ⟨.localDecl, node.id⟩ fvNode node
  return (node, outGraph)

def Lean.MVarId.mkExprGraph (id : MVarId) (compressUniverses? compressProofs? : Bool) : 
    MetaM (WithId Node × ExprGraph) := id.withContext do
  instantiateMVarDeclMVars id
  let tp ← id.getType
  tp.mkExprGraphWithLCtx compressUniverses? compressProofs?

def mkGoalStateExprGraph (goals : List MVarId) (compressUniverses? compressProofs? : Bool) :
    MetaM (WithId Node × ExprGraph) := do
  let mut id : UInt64 := hash "goalState"
  for goal in goals do
    let tp ← goal.getType
    id := mixHash id (hash tp)
  let outNode : WithId Node := ⟨.goalState, id⟩
  let mut outGraph := {}
  for (goal, idx) in goals.toArray.zipWithIndex do
    let (goalNode, goalGraph) ← goal.mkExprGraph compressUniverses? compressProofs?
    outGraph := outGraph ∪ goalGraph |>.insertEdge ⟨.goal idx, id⟩ goalNode outNode
  return (outNode, outGraph)
