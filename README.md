# Kuratowski's theorem in Lean 4

A formal proof of **both directions** of Kuratowski's theorem for finite simple graphs,
using combinatorial planarity defined by rotation systems.

```lean
import Kuratowski.Hard

open SimpleGraph Kuratowski

example {V : Type*} [Finite V] (G : SimpleGraph V) :
    IsPlanar G ↔ ¬ ContainsSubdivision G K5 ∧ ¬ ContainsSubdivision G K33 :=
  isPlanar_iff_kuratowskiFree
```

The theorem includes disconnected graphs, isolated vertices, and an empty vertex type.
It requires no decidable equality or adjacency instance. **The correspondence between
rotation systems and topological embeddings in the plane is not formalized here.**

[한국어 설명과 전체 정리 목록](README.ko.md) · [Library guide](docs/library.md) ·
[Mathematical blueprint](blueprint/src/chapters/intro.tex) · [Contributing](CONTRIBUTING.md)

## Build and use

Lean **4.35.0** and Mathlib **v4.35.0** are pinned by `lean-toolchain` and
`lake-manifest.json`.

```sh
lake exe cache get
lake build
```

This builds the library and its axiom audit. All library declarations are checked against
`propext`, `Classical.choice`, and `Quot.sound`. No proof uses `sorry`, `admit`,
`native_decide`, or additional axioms.

For another Lake project using the same toolchain, add:

```toml
[[require]]
name = "kuratowski"
git = "https://github.com/Maokami/kuratowski-lean.git"
rev = "v1.0.0"
```

Import `Kuratowski.Hard` for the main theorem, a focused module for a smaller API,
or `Kuratowski` for the whole library. See [the library guide](docs/library.md).

The full repository check additionally builds the Korean blueprint as HTML and PDF,
checks its Lean declaration references, and runs finite regression checks:

```sh
scripts/blueprint.sh
```

It requires `leanblueprint`, Graphviz, and a TeX installation with XeLaTeX and Korean support.
Python enumeration checks are regression evidence; the Lean kernel checks the general proof.

## Proof and reusable components

The easy direction combines Euler's inequality, subgraph monotonicity, invariance under
undoing subdivision, and edge bounds excluding `K₅` and `K₃,₃`.
The hard direction uses induction on the number of edges: reduce to a
3-connected graph, contract a suitable edge, and reconstruct a planar rotation system or
exhibit a forbidden subdivision.

Reusable modules cover:

- permutation cycles, transpositions, and deletion;
- graph subdivisions and internally disjoint path systems;
- connectivity, edge contraction, and fixed-vertex-type deletion;
- cyclic orders, face boundaries, and rotation-system surgeries.

The [library guide](docs/library.md) identifies possible Mathlib contributions. Those APIs
still require upstream design review; this repository is not part of Mathlib.

## Development and provenance

Development used OpenAI Codex and Anthropic Claude Code, with independent source review,
Lean compilation, and axiom audits. Automated review does not certify that a theorem statement
matches its intended mathematics. See [AUTHORS.md](AUTHORS.md) and the
[Continuous AI notes](docs/continuous-ai.md) for scope and limitations.

The source is licensed under [Apache-2.0](LICENSE). Dependencies retain their own licenses.
Use [CITATION.cff](CITATION.cff) to cite a release, and include the commit when citing an
unreleased revision. See [CHANGELOG.md](CHANGELOG.md) for release changes.
