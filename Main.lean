import ExprGraph
import Cli
import ImportGraph.RequiredModules
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.CoreM
import LeanExtras

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

def writeExprGraph (handle : IO.FS.Handle) (expr : Expr) (mdata : Json) : MetaM Unit := do
  if ← IO.checkCanceled then return
  let (node, graph) ← expr.mkExprGraph true true
  if ← IO.checkCanceled then return
  handle.putStrLn <| Json.compress <| .mkObj [
    ("mdata", mdata),
    ("pp", toString <| ← Meta.ppExpr expr),
    ("graph", graph.mkJsonWithIdx node (fun a => toJson a.val) (fun a => toJson a.val)),
    ("dot", graph.mkDotWithIdx node (fun a => a.val.toString) (fun a => a.val.toString) hash)
  ]

def runTypeGraphCmd (p : Parsed) : IO UInt32 := do
  let output : String := p.positionalArg! "output" |>.as! String
  let threads : Nat := p.positionalArg! "threads" |>.as! Nat
  let timeout : Nat := p.positionalArg! "timeout" |>.as! Nat
  let output : System.FilePath := output
  let handle ← IO.FS.Handle.mk output .write
  let options : Options := maxHeartbeats.set {} 0
  let res ← runOnMathlibConsts 
      (numThread := threads) (opts := options) (timeout := timeout.toUInt32) 
      fun idx nm cinfo => Meta.MetaM.run' do
    let tp := cinfo.type
    let mod := (← getEnv).getModuleFor? nm
    println! s!"{idx} : {nm} : {mod.getD .anonymous}" 
    writeExprGraph handle tp <| .mkObj [
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
  ARGS:
    "output" : String; "Output file"
    "threads" : Nat; "Number of threads to use"
    "timeout" : Nat; "Timeout for each calculation in milliseconds"
]

def runTypeValGraphCmd (p : Parsed) : IO UInt32 := do
  let output : String := p.positionalArg! "output" |>.as! String
  let threads : Nat := p.positionalArg! "threads" |>.as! Nat
  let timeout : Nat := p.positionalArg! "timeout" |>.as! Nat
  let output : System.FilePath := output
  let handle ← IO.FS.Handle.mk output .write
  let options : Options := maxHeartbeats.set {} 0
  let res ← runOnMathlibConsts 
      (numThread := threads) (opts := options) (timeout := timeout.toUInt32) 
      fun idx nm cinfo => Meta.MetaM.run' do
    let tp := cinfo.type
    let mod := (← getEnv).getModuleFor? nm
    println! s!"{idx} : {nm} : {mod.getD .anonymous}" 
    writeExprGraph handle tp <| .mkObj [
      ("kind", "type"),
      ("name", toJson nm),
      ("module", toJson mod)
    ]
    let some val := cinfo.value? | return .ok ()
    writeExprGraph handle val <| .mkObj [
      ("kind", "value"),
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
  ARGS:
    "output" : String; "Output file"
    "threads" : Nat; "Number of threads to use"
    "timeout" : Nat; "Timeout for each calculation in milliseconds"
]

def runSubexprGraphCmd (p : Parsed) : IO UInt32 := do
  let output : String := p.positionalArg! "output" |>.as! String
  let threads : Nat := p.positionalArg! "threads" |>.as! Nat
  let timeout : Nat := p.positionalArg! "timeout" |>.as! Nat
  let output : System.FilePath := output
  let handle ← IO.FS.Handle.mk output .write
  let options : Options := maxHeartbeats.set {} 0
  let res ← runOnMathlibConsts 
      (numThread := threads) (opts := options) (timeout := timeout.toUInt32) 
      fun idx nm cinfo => Meta.MetaM.run' do
    let tp := cinfo.type
    let mod := (← getEnv).getModuleFor? nm
    println! s!"{idx} : {nm} : {mod.getD .anonymous}" 
    Meta.forEachExpr tp fun e => do
      writeExprGraph handle e <| .mkObj [
        ("kind", "type"),
        ("name", toJson nm),
        ("module", toJson mod)
      ]
    let some val := cinfo.value? | return .ok ()
    Meta.forEachExpr val fun e => do
      writeExprGraph handle e <| .mkObj [
        ("kind", "value"),
        ("name", toJson nm),
        ("module", toJson mod)
      ]
    return .ok ()
  match res with 
  | .ok _ => return 0
  | .error e => throw e

def subexprGraphCmd := `[Cli|
  subexpr_graph VIA runTypeValGraphCmd;
  "Generate graphs for all (sub)expressions appearing in mathlib."
  ARGS:
    "output" : String; "Output file"
    "threads" : Nat; "Number of threads to use"
    "timeout" : Nat; "Timeout for each calculation in milliseconds"
]

def entrypoint := `[Cli|
  entrypoint NOOP; "Entry point for this program"
  SUBCOMMANDS:
  typeGraphCmd;
  typeValGraphCmd;
  subexprGraphCmd
]



def main (args : List String) : IO UInt32 := entrypoint.validate args
