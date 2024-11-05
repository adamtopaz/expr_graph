import ExprGraph
import Cli
import ImportGraph.RequiredModules
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.CoreM
import LeanExtras
import Utils

open Cli Lean

def withMathlibConsts (e : Array (Name × ConstantInfo) → CoreM α) (opts : Options := {}) : IO α := do
  searchPathRef.set compile_time_search_path%
  CoreM.withImportModules (options := opts) #[`Mathlib] do
    let env ← getEnv
    let mut cs := #[]
    for (n,c) in env.constants do
      if ← n.isBlackListed then continue
      cs := cs.push (n,c)
    e cs

def runOnMathlibConsts 
    (e : Nat → Name → ConstantInfo → CoreM (Except IO.Error Unit)) 
    (numThread : Nat := 1) 
    (opts : Options := {}) 
    (timeout : Option UInt32 := none) :
    IO (Except IO.Error Unit) := do
  withMathlibConsts (opts := opts) fun cs => do
    let ctx ← read
    let state ← get
    cs.runInParallel numThread fun idx (nm, cinfo) =>
      let go := Prod.fst <$> Core.CoreM.toIO (e idx nm cinfo) ctx state
      match timeout with
      | none => go
      | some t => do
        try withTimeout t go
        catch _e => return .ok ()

def mkExprGraphJson
    (pp : Format) 
    (node : WithId ExprGraph.Node) 
    (graph : ExprGraph) 
    (mdata : Json) : Json := 
  .mkObj [
    ("mdata", mdata),
    ("pp", toString pp),
    ("graph", graph.mkJsonWithIdx node (fun a => a.val.tokenize) (fun a => a.val.tokenize)),
    ("dot", graph.mkDotWithIdx node (fun a => a.val.toString) (fun a => a.val.toString) hash)
  ]

def writeExprGraph 
    (handle : IO.FS.Handle) 
    (pp : Format) 
    (node : WithId ExprGraph.Node) 
    (graph : ExprGraph) 
    (mdata : Json) : MetaM Unit := do
  handle.putStrLn <| Json.compress <| mkExprGraphJson pp node graph mdata

def printExprGraph 
    (pp : Format) 
    (node : WithId ExprGraph.Node) 
    (graph : ExprGraph) 
    (mdata : Json) : IO Unit := do
  println! Json.compress <| mkExprGraphJson pp node graph mdata

def runTypeGraphCmd (p : Parsed) : IO UInt32 := do
  let output : String := p.positionalArg! "output" |>.as! String
  let threads : Nat := p.positionalArg! "threads" |>.as! Nat
  let output : System.FilePath := output
  let handle ← IO.FS.Handle.mk output .write
  let options : Options := maxHeartbeats.set {} 0
  let res ← runOnMathlibConsts 
      (numThread := threads) (opts := options) (timeout := none)
      fun idx nm cinfo => Meta.MetaM.run' do
    let tp := cinfo.type
    let mod := (← getEnv).getModuleFor? nm
    if p.hasFlag "verbose" then println! s!"{idx} : {nm} : {mod.getD .anonymous}" 
    let (node, graph) ← tp.mkExprGraph true true
    let pp ← Meta.ppExpr tp
    writeExprGraph handle pp node graph <| .mkObj [
      ("name", toJson nm),
      ("module", toJson mod)
    ]
    return .ok ()
  match res with 
  | .ok _ => return 0
  | .error e => throw e

def typeGraphCmd := `[Cli|
  type_graph VIA runTypeGraphCmd;
  "Generate graphs for types of constants appearing in mathlib."
  FLAGS:
    v, verbose; "Print the name of the constant being processed"
  ARGS:
    "output" : String; "Output file"
    "threads" : Nat; "Number of threads to use"
]

def runTypeValGraphCmd (p : Parsed) : IO UInt32 := do
  let output : String := p.positionalArg! "output" |>.as! String
  let threads : Nat := p.positionalArg! "threads" |>.as! Nat
  let output : System.FilePath := output
  let handle ← IO.FS.Handle.mk output .write
  let options : Options := maxHeartbeats.set {} 0
  let res ← runOnMathlibConsts 
      (numThread := threads) (opts := options) (timeout := none)
      fun idx nm cinfo => Meta.MetaM.run' do
    let tp := cinfo.type
    let mod := (← getEnv).getModuleFor? nm
    if p.hasFlag "verbose" then println! s!"{idx} : {nm} : {mod.getD .anonymous}" 
    let (node, graph) ← tp.mkExprGraph true true
    let pp ← Meta.ppExpr tp
    writeExprGraph handle pp node graph <| .mkObj [
      ("fromType", true),
      ("name", toJson nm),
      ("module", toJson mod)
    ]
    let some val := cinfo.value? | return .ok ()
    let (node, graph) ← val.mkExprGraph true true
    let pp ← Meta.ppExpr val
    writeExprGraph handle pp node graph <| .mkObj [
      ("fromType", false),
      ("name", toJson nm),
      ("module", toJson mod)
    ]
    return .ok ()
  match res with 
  | .ok _ => return 0
  | .error e => throw e

def typeValGraphCmd := `[Cli|
  type_val_graph VIA runTypeValGraphCmd;
  "Generate graphs for types and values of constants appearing in mathlib."
  FLAGS:
    v, verbose; "Print the name of the constant being processed"
  ARGS:
    "output" : String; "Output file"
    "threads" : Nat; "Number of threads to use"
]

def Lean.ConstantInfo.forEachSubexpr
    (info : ConstantInfo) 
    (f : Bool → Expr → MetaM Unit) : 
    MetaM Unit := do
  let tp := info.type
  Meta.forEachExpr tp <| f true
  let some val := info.value? | return ()
  Meta.forEachExpr val <| f false

def runSubexprGraphCmd (p : Parsed) : IO UInt32 := do
  let output : String := p.positionalArg! "output" |>.as! String
  let threads : Nat := p.positionalArg! "threads" |>.as! Nat
  let output : System.FilePath := output
  let handle ← IO.FS.Handle.mk output .write
  let options : Options := maxHeartbeats.set {} 0
  let res ← runOnMathlibConsts 
      (numThread := threads) (opts := options) (timeout := none)
      fun idx nm cinfo => Meta.MetaM.run' do
    let mod := (← getEnv).getModuleFor? nm
    if p.hasFlag "verbose" then println! s!"{idx} : {nm} : {mod.getD .anonymous}" 
    cinfo.forEachSubexpr fun isTp? e => do 
      let (node, graph) ← e.mkExprGraph true true
      let pp ← Meta.ppExpr e
      writeExprGraph handle pp node graph <| .mkObj [
        ("fromType", isTp?),
        ("name", toJson nm),
        ("module", toJson mod)
      ]
    return .ok ()
  match res with 
  | .ok _ => return 0
  | .error e => throw e

def subexprGraphCmd := `[Cli|
  subexpr_graph VIA runSubexprGraphCmd;
  "Generate graphs for all (sub)expressions appearing in mathlib."
  FLAGS:
    v, verbose; "Print the name of the constant being processed"
  ARGS:
    "output" : String; "Output file"
    "threads" : Nat; "Number of threads to use"
]

def runSubexprLCtxGraphCmd (p : Parsed) : IO UInt32 := do
  let output : String := p.positionalArg! "output" |>.as! String
  let threads : Nat := p.positionalArg! "threads" |>.as! Nat
  let output : System.FilePath := output
  let handle ← IO.FS.Handle.mk output .write
  let options : Options := maxHeartbeats.set {} 0
  let res ← runOnMathlibConsts 
      (numThread := threads) (opts := options) (timeout := none)
      fun idx nm cinfo => Meta.MetaM.run' do
    let mod := (← getEnv).getModuleFor? nm
    if p.hasFlag "verbose" then println! s!"{idx} : {nm} : {mod.getD .anonymous}" 
    cinfo.forEachSubexpr fun isTp? e => do 
      let (node, graph) ← e.mkExprGraphWithLCtx true true
      let pp ← Meta.ppExpr e
      writeExprGraph handle pp node graph <| .mkObj [
        ("fromType", isTp?),
        ("name", toJson nm),
        ("module", toJson mod)
      ]
    return .ok ()
  match res with 
  | .ok _ => return 0
  | .error e => throw e

def subexprLCtxGraphCmd := `[Cli|
  subexpr_lctx_graph VIA runSubexprLCtxGraphCmd;
  "Generate graphs for all (sub)expressions appearing in mathlib. Graphs will include the whole local context."
  FLAGS:
    v, verbose; "Print the name of the constant being processed"
  ARGS:
    "output" : String; "Output file"
    "threads" : Nat; "Number of threads to use"
]

open Elab Term Tactic in
def runTacticGraphCmd (p : Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let module : Name := p.positionalArg! "module" |>.as! String |>.toName
  let options : Options := maxHeartbeats.set {} 0
  let leanFile : LeanFile := { ← LeanFile.findModule module with options := options }
  let compressUniverses? : Bool := ! p.hasFlag "universes"
  let compressProofs? : Bool := ! p.hasFlag "proofs"
  let debug? : Bool := p.hasFlag "debug"
  leanFile.withVisitInfoTrees' (post := fun _ _ _ => return) fun ctxInfo info _children => do
    let .ofTacticInfo info := info | return
    unless info.isOriginal do return
    unless info.isSubstantive do return
    let ctxInfo := { ctxInfo with options := maxHeartbeats.set ctxInfo.options 0 }
    try
      let ⟨node, graph⟩ ← ctxInfo.runMetaM' {} 
        <| Meta.withMCtx info.mctxBefore 
        <| mkGoalStateExprGraph info.goalsBefore compressUniverses? compressProofs?
      let pp ← ctxInfo.ppGoals' info.goalsBefore
      if !debug? then 
        printExprGraph pp node graph <| .mkObj [
          ("name", toJson info.name?),
          ("stx", toString info.stx.prettyPrint),
          ("usedConstants", toJson info.getUsedConstantsAsSet.toArray)
        ]
    catch err => 
      if debug? then println! Json.compress <| .mkObj [
        ("error", toString err),
        ("module", toJson module),
        ("name", toJson info.name?),
        ("stx", toString info.stx.prettyPrint),
      ]
  return 0

def tacticGraphCmd := `[Cli|
  tactic_graph VIA runTacticGraphCmd;
  "Generate graphs for all tactics in a given module."
  FLAGS:
    u, universes; "Include uncompressed universe levels in the graph"
    p, proofs; "Include uncompressed proofs in the graph"
    d, debug; "Only print error messages"
  ARGS:
    "module" : String; "Module to elaborate"
]

def entrypoint := `[Cli|
  entrypoint NOOP; "Entry point for this program"
  SUBCOMMANDS:
  typeGraphCmd;
  typeValGraphCmd;
  subexprGraphCmd;
  subexprLCtxGraphCmd;
  tacticGraphCmd
]

def main (args : List String) : IO UInt32 := entrypoint.validate args
