# Expression Graphs

This repository can be used to represent `Lean4` expressions as graphs.
For example, here is the graph representing the type of `Nat.add_comm`:

![Nat.add_comm](graph.png)

## Comments

These graphs are computed in the `MetaM` monad, and thus `bvar`s should not appear.
Instead, new `fvar`s are introduced as part of the computation for all `forallE`, `lam` and `letE` expressions.
Variable names are also dropped.

The function used to make the graphs can be found by importing `ExprGraph.Basic`, and it has the following type:
```lean
Lean.Expr.mkExprGraph (e : Expr) (compressUniverses? : Bool) (compressProofs? : Bool) : 
  MetaM (WithId Node × ExprGraph) 
```
The output is a pair of the root node and the graph itself.

The option `compressUniverses? : Bool`, if true, will compress universes parameters as a plain `level`.
If false, this will construct an expression graph associated to the definition of the universe parameter. 

The option `compressProofs? : Bool`, if true, will compress proofs as a plain `proof`, while adding the graph associated to the *type* of the proof to the graph. 
If false, this will construct the expression graph associated to the proof itself.

The type `ExprGraph` is an abbreviation:
```lean
abbrev ExprGraph := HashGraph (WithId ExprGraph.Node) (WithId ExprGraph.Edge)
```

The definitions of `HashGraph` and `WithId` can be found at [this repository](https://github.com/adamtopaz/lean_extras). 

## Usage

To generate graphs associated to the types of all constants in `mathlib`, use the following command:
```lean
lake exe entrypoint type_graph output 8 5000
```
This will dump the data to the file `output`, and the calculation will be done using 8 threads.
Processing of each constant will have a timeout of 5000 milliseconds.

## TODO

- Right now, the data generation script truncates universe levels and proofs are `level` and `proof` nodes, respectively.
  These options should be configurable as flags.
- Better filtering of the constants to be considered in the data generation script.
