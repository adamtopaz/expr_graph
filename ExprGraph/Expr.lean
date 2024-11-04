import LeanExtras

open Lean

namespace ExprGraph

deriving instance ToJson, DecidableEq for BinderInfo

inductive Node where
  | str (s : String) 
  | nat (n : Nat)
  | name (n : Name)
  | level
  | levelZero
  | levelSucc
  | levelMax
  | levelIMax
  | levelParam
  | levelMVar
  | proof
  | bvar
  | mvar
  | fvar
  | sort
  | const (nm : Name)
  | app
  | lam (bi : BinderInfo)
  | forallE (bi : BinderInfo)
  | proj (nm : Name) (idx : Nat)
  | letE
  | goalState
deriving Hashable, BEq, ToJson, DecidableEq, Inhabited

inductive Edge where
  | levelSuccArg
  | levelMaxArgL
  | levelMaxArgR
  | levelIMaxArgL
  | levelIMaxArgR
  | fvarType
  | fvarVal
  | mvarType
  | mvarVal
  | proofType
  | sortLevel
  | constLevelArg (n : Nat)
  | appFn
  | appArg (n : Nat)
  | lamVar
  | lamBody
  --| lamType
  | forallEVar
  | forallEBody
  --| forallEType
  | letEVar
  | letEBody
  --| letEType
  --| letEVal
  | projStruct
  | localDecl
  | goal (idx : Nat)
deriving Hashable, BEq, ToJson, DecidableEq

def Node.toString : Node → String := fun
  | .str s => s!"str {s}"
  | .nat n => s!"nat {n}"
  | .name n => s!"name {n}"
  | .level => "level"
  | .levelZero => "levelZero"
  | .levelSucc => "levelSucc"
  | .levelMax => "levelMax"
  | .levelIMax => "levelIMax"
  | .levelParam => "levelParam"
  | .levelMVar => "levelMVar"
  | .proof => "proof"
  | .bvar => "bvar"
  | .mvar => "mvar"
  | .fvar => "fvar"
  | .sort => "sort"
  | .const nm => s!"const {nm}"
  | .app => "app"
  | .lam _bi => s!"lam"
  | .forallE _bi => s!"forallE"
  | .letE => s!"letE"
  | .proj nm idx => s!"proj {nm} {idx}"
  | .goalState => "goalState"

def Edge.toString : Edge → String := fun
  | .levelSuccArg => "levelSuccArg"
  | .levelMaxArgL => "levelMaxArgL"
  | .levelMaxArgR => "levelMaxArgR"
  | .levelIMaxArgL => "levelIMaxArgL"
  | .levelIMaxArgR => "levelIMaxArgR"
  | .fvarType => "fvarType"
  | .fvarVal => "fvarVal"
  | .mvarType => "mvarType"
  | .mvarVal => "mvarVal"
  | .proofType => "proofType"
  | .sortLevel => "sortLevel"
  | .constLevelArg n => s!"sortLevelArg {n}"
  | .appFn => "appFn"
  | .appArg n => s!"appArg {n}"
  | .lamVar => "lamVar"
  | .lamBody => "lamBody"
  --| .lamType => "lamType"
  | .forallEVar => "forallEVar"
  | .forallEBody => "forallEBody"
  --| .forallEType => "forallEType"
  | .letEVar => "letEVar"
  | .letEBody => "letEBody"
  --| .letEType => "letEType"
  --| .letEVal => "letEVal"
  | .projStruct => "projStruct"
  | .localDecl => "localDecl"
  | .goal idx => s!"goal {idx}"

end ExprGraph

abbrev ExprGraph := HashGraph (WithId ExprGraph.Node) (WithId ExprGraph.Edge)

open ExprGraph

local notation a ":::" b => mixHash (Hashable.hash a) (Hashable.hash b)

def String.mkExprGraph (s : String) : WithId Node × ExprGraph := 
  let outId : UInt64 := s ::: "String"
  let outNode : WithId Node := ⟨.str s, outId⟩
  (outNode, {outNode})

def Nat.mkExprGraph (n : Nat) : WithId Node × ExprGraph := 
  let outId : UInt64 := n ::: "Nat"
  let outNode : WithId Node := ⟨.nat n, outId⟩
  (outNode, {outNode})

def Lean.Name.mkExprGraph (n : Name) : WithId Node × ExprGraph := 
  let outId : UInt64 := n ::: "Name"
  let outNode : WithId Node := ⟨.name n, outId⟩
  (outNode, {outNode})

def Lean.Level.mkCompressedExprGraph (l : Level) : WithId Node × ExprGraph := 
  let outId : UInt64 := l ::: "Lean.Level"
  let outNode : WithId Node := ⟨.level, outId⟩
  (outNode, {outNode})

def Lean.Level.mkExprGraph (l : Level) : WithId Node × ExprGraph := 
  let outId : UInt64 := l ::: "Lean.Level"
  match l with
  | .zero => 
    let outNode : WithId Node := ⟨.levelZero, outId⟩ 
    (outNode, {outNode})
  | .succ a => 
    let outNode : WithId Node := ⟨.levelSucc, outId⟩ 
    let (prevNode, prevGraph) := a.mkExprGraph
    (outNode, prevGraph.insertEdge ⟨.levelSuccArg, outId⟩ prevNode outNode)
  | .max a b => 
    let outNode : WithId Node := ⟨.levelMax, outId⟩ 
    let (lNode, lGraph) := a.mkExprGraph
    let (rNode, rGraph) := b.mkExprGraph
    let outGraph := lGraph ∪ rGraph
      |>.insertEdge ⟨.levelMaxArgL, outId⟩ lNode outNode
      |>.insertEdge ⟨.levelMaxArgR, outId⟩ rNode outNode
    (outNode, outGraph)
  | .imax a b => 
    let outNode : WithId Node := ⟨.levelIMax, outId⟩ 
    let (lNode, lGraph) := a.mkExprGraph
    let (rNode, rGraph) := b.mkExprGraph
    let outGraph := lGraph ∪ rGraph
      |>.insertEdge ⟨.levelIMaxArgL, outId⟩ lNode outNode 
      |>.insertEdge ⟨.levelIMaxArgR, outId⟩ rNode outNode
    (outNode, outGraph)
  | .param _ => 
    let outNode : WithId Node := ⟨.levelParam, outId⟩ 
    (outNode, {outNode})
  | .mvar _ => 
    let outNode : WithId Node := ⟨.levelMVar, outId⟩ 
    (outNode, {outNode})

-- TODO: Add inhabited instance on `WithId`
instance : Inhabited (MonadCacheT Expr (WithIdNode × ExprGraph) MetaM (WithId Node × ExprGraph)) where
  default := pure (⟨default, default⟩, default)

partial
def Lean.Expr.mkExprGraphCaching
    (e : Expr) 
    (compressUniverses? : Bool)
    (compressProofs? : Bool) : 
    MonadCacheT Expr (WithId Node × ExprGraph) MetaM (WithId Node × ExprGraph) := do
  let e ← instantiateMVars e
  checkCache e fun _ => do
    let outId : UInt64 := e ::: "Lean.Expr" 
    let universeFn : Level → WithId Node × ExprGraph := 
      if compressUniverses? then Level.mkCompressedExprGraph else Level.mkExprGraph
    if compressProofs? && (← Meta.isProof e) then 
      let outNode : WithId Node := ⟨.proof, outId⟩
      let tp ← Meta.inferType e
      let (tpNode, tpGraph) ← tp.mkExprGraphCaching compressUniverses? compressProofs?
      return (outNode, tpGraph |>.insertEdge ⟨.proofType, outId⟩ tpNode outNode)
    else
    match e with 
    | .bvar _ => 
      let outNode : WithId Node := ⟨.bvar, outId⟩
      return (outNode, {outNode})
    | .fvar id =>
      let (tpNode, tpGraph) ← (← id.getType).mkExprGraphCaching compressUniverses? compressProofs?
      let outNode : WithId Node := ⟨.fvar, outId⟩
      let mut outGraph := tpGraph |>.insertEdge ⟨.fvarType, outId⟩ tpNode outNode
      let some val ← id.getValue? | return (outNode, outGraph)
      let (valNode, valGraph) ← val.mkExprGraphCaching compressUniverses? compressProofs?
      outGraph := outGraph ∪ valGraph |>.insertEdge ⟨.fvarVal, outId⟩ valNode outNode
      return (outNode, outGraph)
    | .mvar mvarId =>
      let (tpNode, tpGraph) ← (← mvarId.getType).mkExprGraphCaching compressUniverses? compressProofs?
      let outNode : WithId Node := ⟨.mvar, outId⟩
      let outGraph := tpGraph |>.insertEdge ⟨.mvarType, outId⟩ tpNode outNode
      return (outNode, outGraph)
    | .sort u => 
      let outNode : WithId Node := ⟨.sort, outId⟩
      let (uNode, uGraph) := universeFn u
      let outGraph := uGraph |>.insertEdge ⟨.sortLevel, outId⟩ uNode outNode
      return (outNode, outGraph)
    | .const declName us => 
      let outNode : WithId Node := ⟨.const declName, outId⟩
      let mut outGraph : ExprGraph := {outNode}
      for (u,i) in us.toArray.zipWithIndex do
        let (uNode, uGraph) := universeFn u
        outGraph := (outGraph ∪ uGraph) |>.insertEdge ⟨.constLevelArg i, outId⟩ uNode outNode
      return (outNode, outGraph)
    | .app .. => 
      let outNode : WithId Node := ⟨.app, outId⟩
      let fn := e.getAppFn
      let (fnNode, fnGraph) ← fn.mkExprGraphCaching compressUniverses? compressProofs?
      let mut outGraph := fnGraph |>.insertEdge ⟨.appFn, outId⟩ fnNode outNode
      let args := e.getAppArgs
      for (arg, i) in args.zipWithIndex do
        let (argNode, argGraph) ← arg.mkExprGraphCaching compressUniverses? compressProofs?
        outGraph := outGraph ∪ argGraph |>.insertEdge ⟨.appArg i, outId⟩ argNode outNode
      return (outNode, outGraph)
    | .lam nm tp body binfo => Meta.withLocalDecl nm binfo tp fun fvar => do
      let body := body.instantiateRev #[fvar]
      let fvarId := fvar.fvarId!
      let binderInfo ← fvarId.getBinderInfo
      let outNode : WithId Node := ⟨.lam binderInfo, outId⟩
      let (bodyNode, bodyGraph) ← body.mkExprGraphCaching compressUniverses? compressProofs?
      let (fvarNode, fvarGraph) ← fvar.mkExprGraphCaching compressUniverses? compressProofs?
      let outGraph := bodyGraph ∪ fvarGraph 
        |>.insertEdge ⟨.lamBody, outId⟩ bodyNode outNode
        |>.insertEdge ⟨.lamVar, outId⟩ fvarNode outNode
      return (outNode, outGraph)
    | .forallE nm tp body binfo => Meta.withLocalDecl nm binfo tp fun fvar => do
      let body := body.instantiateRev #[fvar]
      let fvarId := fvar.fvarId!
      let binderInfo ← fvarId.getBinderInfo
      let outNode : WithId Node := ⟨.forallE binderInfo, outId⟩
      let (bodyNode, bodyGraph) ← body.mkExprGraphCaching compressUniverses? compressProofs?
      let (fvarNode, fvarGraph) ← fvar.mkExprGraphCaching compressUniverses? compressProofs?
      let outGraph := bodyGraph ∪ fvarGraph 
        |>.insertEdge ⟨.forallEBody, outId⟩ bodyNode outNode
        |>.insertEdge ⟨.forallEVar, outId⟩ fvarNode outNode
      return(outNode, outGraph)
    | .letE nm tp val body _ => Meta.withLetDecl nm tp val fun fvar => do
      let body := body.instantiateRev #[fvar]
      let outNode : WithId Node := ⟨.letE, outId⟩
      let (bodyNode, bodyGraph) ← body.mkExprGraphCaching compressUniverses? compressProofs?
      let (fvarNode, fvarGraph) ← fvar.mkExprGraphCaching compressUniverses? compressProofs?
      let mut outGraph := bodyGraph ∪ fvarGraph 
        |>.insertEdge ⟨.letEBody, outId⟩ bodyNode outNode
        |>.insertEdge ⟨.letEVar, outId⟩ fvarNode outNode
      return (outNode, outGraph)
    | .lit (.natVal a) => 
      let outNode : WithId Node := ⟨.nat a, outId⟩
      return (outNode, {outNode})
    | .lit (.strVal a) => 
      let outNode : WithId Node := ⟨.str a, outId⟩
      return (outNode, {outNode})
    | .mdata _data expr => expr.mkExprGraphCaching compressUniverses? compressProofs?
    | .proj typeName idx struct => 
      let outNode : WithId Node := ⟨.proj typeName idx, outId⟩
      let (strNode, strGraph) ← struct.mkExprGraphCaching compressUniverses? compressProofs?
      let outGraph := strGraph |>.insertEdge ⟨.projStruct, outId⟩ strNode outNode
      return (outNode, outGraph)

def Lean.Expr.mkExprGraph
    (e : Expr) 
    (compressUniverses? : Bool)
    (compressProofs? : Bool) : 
    MetaM (WithId Node × ExprGraph) := 
  e.mkExprGraphCaching compressUniverses? compressProofs? |>.run  
