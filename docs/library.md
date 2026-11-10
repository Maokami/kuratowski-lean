# Using the library

The library proves Kuratowski's theorem for finite simple graphs with
**combinatorial planarity**: some rotation system has Euler characteristic
`|V| - |E| + |F| = 2 * |ConnectedComponent|`. Isolated vertices contribute one face.
The correspondence with embeddings in the plane or sphere is not formalized here.

## Imports and API layers

Import a focused module when possible. `import Kuratowski` imports the complete library.

| Module | Main interface | Dependencies of interest |
| --- | --- | --- |
| `Kuratowski.Perm` | `orbitCount`, splitting and joining cycles by transpositions | Permutations; no graphs |
| `Kuratowski.PermSum` | Sum-permutation powers, cycle membership, `orbitCount_sumCongr` | `Perm`; no graphs |
| `Kuratowski.Basic` | `RotationSystem`, `facePerm`, `eulerChar`, `IsPlanar` | Simple graphs and `Perm` |
| `Kuratowski.RotationOrder` | Inverse-rotation periods and neighbor enumeration | `Basic`; no face surgery |
| `Kuratowski.Contract` | `contractEdge`, `contractVertex`, adjacency formulas | Simple graphs; no rotation-system dependencies |
| `Kuratowski.Cyclic` | `CyclicSequence`, index shifts (`rotate`), reversal, monotonicity | Simple graphs and modular indices |
| `Kuratowski.Paths` | `walkInterior`, `SubdivisionPaths` | Paths and injective branch maps |
| `Kuratowski.Subdivision` | `IsSubdivision`, `ContainsSubdivision` | Edge subdivision, smoothing, and non-planarity bounds |
| `Kuratowski.SubdivisionOfPaths` | `containsSubdivision_iff_paths` | Equivalence with iterated subdivision |
| `Kuratowski.Hard` | `isPlanar_iff_kuratowskiFree` | The complete proof |

Public names remain in the `Kuratowski` namespace. The foundation extraction preserves the
existing public statement types and argument order; importing their old modules still works.
In particular, `Uncontract` uses `RotationOrder` and `Contract` instead of importing the
path-replacement and J2 face-construction modules. The later removal of unused arguments from
`Smooth` auxiliary lemmas is listed separately in [the changelog](../CHANGELOG.md).

```lean
import Kuratowski.Hard

open SimpleGraph Kuratowski

example {V : Type*} [Finite V] (G : SimpleGraph V) :
    IsPlanar G ↔ ¬ ContainsSubdivision G K5 ∧ ¬ ContainsSubdivision G K33 :=
  isPlanar_iff_kuratowskiFree
```

The examples in [`examples/`](../examples/) are checked by CI. Lake also resolves the
small `checkdecls` package, which is a regular dependency used for blueprint validation.

## Conventions

- Counts use `Nat.card` and `Set.ncard`; finiteness hypotheses are explicit in counting results.
- Vertex deletion and edge contraction keep the original vertex type. Deleted vertices remain
  isolated; contracting `xy` into `x` leaves `y` isolated.
- A subdivision path system embeds **all** source vertices, including isolated vertices.
  Different undirected edges have disjoint path interiors, and interiors avoid branch vertices.
- Classical reasoning is permitted. The audited axiom set is `propext`, `Classical.choice`,
  and `Quot.sound`. No theorem relies on `sorryAx` or native evaluation axioms.

## Potential Mathlib contributions

These are candidates for human review, not claims of upstream readiness or acceptance.
Before submission, search the current Mathlib revision again and discuss placement and API design.

1. Disjoint-sum permutation powers and cycle membership (`PermSum`). These have no graph
   dependencies and form a small, independently reviewable unit.
2. Orbit-count changes under transpositions and deletion (`Perm`, `PermutationDeletion`).
   First decide whether the quotient-based count fits existing permutation APIs.
3. General graph path and connectivity lemmas. Separate fixed-vertex-type deletion conventions
   from general facts before proposing an upstream interface.
4. Rotation systems and planarity. This is a larger design discussion, including the treatment
   of disconnected graphs, isolated vertices, and the topological interpretation.

Mathlib requires contributors to understand and justify AI-assisted code, disclose the assistance,
and participate personally in review. See the
[contribution policy](https://leanprover-community.github.io/contribute/index.html) and
[style guide](https://mathlib.org/contribute/style.html). Upstream discussion and submission are
not part of the repository's automatic improvement workflow.
