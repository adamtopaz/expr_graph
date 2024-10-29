# Expression Graphs

This repository can be used to represent `Lean4` expressions as graphs.
For example, here is the graph representing the type of `Nat.add_comm`:

![Nat.add_comm](graph.png)

## Usage

To generate graphs associated to the types of all constants in `mathlib`, use the following command:
```lean
lake exe entrypoint type_graph output 8
```
This will dump the data to the file `output`, and the calculation will be done using 8 threads.

The function used to make the graphs can be found by importing `ExprGraph.Basic`, and it has the following type:
```lean
Lean.Expr.mkExprGraph (e : Expr) (compressUniverses? : Bool) (compressProofs? : Bool) : 
  MetaM (WithId Node × ExprGraph) 
```
The output is a pair of the root node and the graph itself.

## TODO

Right now, the data generation script truncates universe levels and proofs are `level` and `proof` nodes, respectively.
These options should be configurable as flags.
