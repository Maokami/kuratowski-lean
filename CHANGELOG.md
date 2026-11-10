# Changelog

## 1.0.0

- Prove `isPlanar_iff_kuratowskiFree` for finite simple graphs, including disconnected
  graphs and isolated vertices, using combinatorial planarity.
- Supply subdivision/path-system equivalences, connectivity and contraction lemmas,
  and rotation-system surgeries with a complete Korean mathematical blueprint.
- Extract reusable permutation, rotation-order, contraction-map, and cyclic-sequence
  APIs while preserving existing public names and argument order.
- Expose `pow_sumCongr_inl`/`inr` and `sameCycle_sumCongr_inl`/`inr` in `PermSum`.
- Replace Korean Lean comments with reviewed English mathematical documentation.
- Remove unused assumptions from `Kuratowski.Smooth` auxiliary lemmas and remove its
  file-wide unused-section-variable suppression. In particular, `fst_ne_w` and
  `snd_ne_w` no longer take `hxy`; `rot_pred` no longer takes `hxy` or `hw`.
  `IsPlanar.of_subdivideEdge` retains its statement.
- Add an explicit license, citation metadata, a library guide, and contribution guidance.

The proof-completion milestone was PR #29. Subsequent changes prepare the library for
reuse; they do not establish the unformalized topological embedding correspondence.
