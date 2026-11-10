# Contributing

Use the pinned Lean and Mathlib versions. Discuss changes to core definitions and public
statements before implementing them. Preserve the meaning of the mathematical blueprint.

- Write concise English Lean comments and docstrings. Keep lines at most 100 characters.
- State finiteness and decidability assumptions explicitly; avoid unused hypotheses.
- Reuse Mathlib or existing project results before adding another proof of the same fact.
- Keep general permutation and graph lemmas in focused modules; see [docs/library.md](docs/library.md).
- Record intentional public API changes in the changelog, including changes to implicit arguments.
- Do not introduce `sorry`, `admit`, extra axioms, or `native_decide`.

For a new library module, regenerate the root imports:

```sh
lake exe mk_all --lib Kuratowski
lake build
```

When mathematical content changes, update the corresponding blueprint statement, proof,
Lean names, and dependency references, then run `scripts/blueprint.sh`. New combinatorial
reformulations of surgery arguments also need the bounded finite checks required by `AGENTS.md`.
For comment-only edits, verify that non-comment code is unchanged; CI still builds the library.

Submit changes through a PR with the exact checks performed and any remaining limitations.
CI and the review of the current head must pass. Workflow, script, Lake configuration/lockfile,
toolchain, and audit changes
require maintainer review rather than automatic merging. Do not put credentials in source,
issues, logs, or artifacts.

Mathlib submission is a separate human review process. Search the current upstream API,
discuss placement, disclose AI assistance as required by upstream policy, and understand
and defend the submitted proof. The repository's automation does not submit upstream PRs.
