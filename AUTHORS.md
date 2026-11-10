# Authors and provenance

The project is maintained by [Maokami](https://github.com/Maokami), using that public handle.
The Git history records the contribution history; no legal name is inferred from the handle.

OpenAI Codex and Anthropic Claude Code assisted with formalization, code and documentation,
review, finite regression checks, and repository automation. AI systems are not listed as
human authors. The Lean kernel and the repository's axiom audit check the formal proof;
source review separately checks statements, assumptions, and correspondence with the blueprint.

The proof follows the sources cited in the [blueprint](blueprint/src/chapters/routes.tex),
including C. Thomassen, *Kuratowski's theorem* (1981), and Diestel's contractible-edge
lemma. The rotation-system perspective follows Mohar–Thomassen, *Graphs on Surfaces*.
Mathlib supplies
underlying graph, permutation, finite-set, and arithmetic APIs. Dependency attribution and
licenses remain with those projects.

This project uses combinatorial planarity. It does not formalize the topological correspondence
with planar or spherical embeddings, nor claim that its general APIs have been accepted upstream.
