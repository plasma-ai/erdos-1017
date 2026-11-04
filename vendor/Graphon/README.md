# Graphon source provenance

The 11 Lean modules in this directory are taken from
[cameronfreer/graphon](https://github.com/cameronfreer/graphon) at commit
`9f7be59fa754d260a544b4cfd83d6a5b94f7552e` (2026-09-06), by Cameron Freer.
They are distributed under the Apache License 2.0, whose full text is in
[LICENSE](LICENSE); upstream's LICENSE file, a short Apache 2.0 notice with
its copyright line, is copied unchanged in [NOTICE](NOTICE).

They are the import closure of `Graphon.Compactness`, not the whole upstream
library, and keep their upstream module names: `Graphon.Approximation`,
`Graphon.Basic`, `Graphon.Compactness`, `Graphon.CutDistance`,
`Graphon.CutNorm`, `Graphon.HomDensity`, `Graphon.MeasureIso`,
`Graphon.Overlay`, `Graphon.Pullback`, `Graphon.Regularity`, and
`Graphon.Step`. `Graphon.Compactness` proves that graphons are totally bounded
and complete in the cut distance, so every sequence has a subsequence that
converges in it. The development imports `Graphon.Basic`,
`Graphon.Compactness`, `Graphon.CutDistance`, `Graphon.HomDensity`,
`Graphon.MeasureIso`, `Graphon.Pullback`, and `Graphon.Regularity` directly.
Three of its modules, `GraphonFamilyCompactness`, `GraphonFamilyNets`, and
`GraphonFamilyRounding` in `Erdos1017/Models/Kernel/`, adapt arguments of
`Graphon/Compactness.lean` and credit Cameron Freer in their headers.

Upstream pins Lean `v4.32.0` and Mathlib commit `81a5d25`. This project pins
Lean and Mathlib `v4.35.0-rc4`, and every module was changed. The header of
each states that it was modified. The changes that follow Lean, Mathlib and
this project's options keep every statement:

- `Measure.QuasiMeasurePreserving` is now `MeasureTheory.QuasiMeasurePreserving`,
  so its 37 uses in `Approximation`, `Compactness`, `CutDistance`,
  `HomDensity`, `MeasureIso`, `Pullback`, and `Regularity` drop the `Measure.`
  prefix.
- The lemma `Measure.isProbabilityMeasure_map` was removed. The probability
  measure instances it supplied are found by `inferInstance`, twice in
  `CutDistance` and four times in `MeasureIso`.
- `prod_le_one` is now `prod_le_one₀` (`HomDensity`), and
  `measurable_pi_lambda` is replaced by `Measurable.of_eval` (`Pullback`).
- `Measure.map_smul` needs the measurability of the map, so the two rewrites
  with it in `CutDistance` pass it explicitly.
- `CutNorm` binds `S` and `T` in `SymmKernel.rectIntegral_symm` explicitly,
  because this project sets `autoImplicit = false`.

All 11 modules also use the module system: each begins with `module`, imports
with `public import`, and exposes its definitions with
`@[expose] public section`. The imports of `Architect` and the 23
`@[blueprint]` annotations it supports, which only label declarations for
upstream's blueprint, are removed. A module does not export its private
declarations, so `Regularity` drops `private` from `energyRect`, which occurs
in the type of a public theorem, and `Compactness` drops it from
`exists_cutNormDiff_limit_of_summable`, which `GraphonFamilyCompactness` uses.
Comments that refer to upstream's planning notes, development history, or the
removed blueprint annotations are shortened, and two docstrings in
`Compactness` are corrected to state the hypothesis their declarations use.

No `sorry`, `axiom`, or heartbeat option was added. Upstream's seven
`maxHeartbeats` options, in `Compactness`, `Overlay`, and `Regularity`, are
kept as they are.
