import ExprGraph
import Cli
import ImportGraph.RequiredModules
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.CoreM
import LeanExtras

open Cli Lean

def runTypeGraphCmd (p : Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let output : String := p.positionalArg! "output" |>.as! String
  let threads : Nat := p.positionalArg! "threads" |>.as! Nat
  let timeout : Nat := p.positionalArg! "timeout" |>.as! Nat
  let output : System.FilePath := output
  let handle ← IO.FS.Handle.mk output .write
  let options : Options := maxHeartbeats.set {} 0
  CoreM.withImportModules (options := options) #[`Mathlib] do
    let env ← getEnv
    let mut cs := #[]
    for (n,c) in env.constants do
      if ← n.isBlackListed then continue
      cs := cs.push (n,c) 
    -- Use 8 threads
    let ctx ← read
    let state ← get
    let res ← cs.runInParallel threads fun idx (n,c) => 
      withTimeout timeout <| Core.CoreM.toIO (go idx n c handle) ctx state <&> Prod.fst
    match res with 
    | .ok () => return 0
    | .error e => show IO _ from throw e
where go (idx : Nat) (nm : Name) (cinfo : ConstantInfo) (handle) := Meta.MetaM.run' do
  let tp := cinfo.type
  let (node, graph) ← tp.mkExprGraph true true
  let mod := (← getEnv).getModuleFor? nm
  println! s!"{idx} : {nm} : {mod.getD .anonymous}" 
  handle.putStrLn <| Json.compress <| .mkObj [
    ("name", toJson nm),
    ("module", toJson mod),
    ("pp", toString <| ← Meta.ppExpr tp),
    ("graph", graph.mkJsonWithIdx node (fun a => toJson a.val) (fun a => toJson a.val)),
    ("dot", graph.mkDotWithIdx node (fun a => a.val.toString) (fun a => a.val.toString) hash)
  ]
  return .ok ()

def typeGraphCmd := `[Cli|
  type_graph VIA runTypeGraphCmd;
  "Generate graphs for types of constants appearing in mathlib."
  ARGS:
    "output" : String; "Output file"
    "threads" : Nat; "Number of threads to use"
    "timeout" : Nat; "Timeout for each calculation in milliseconds"
]

def entrypoint := `[Cli|
  entrypoint NOOP; "Entry point for this program"
  SUBCOMMANDS:
  typeGraphCmd
]

def main (args : List String) : IO UInt32 := entrypoint.validate args
