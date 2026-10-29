# Verification, reproducibility and trust boundary

**Pinned audited code:** [commit `df21cfa98a66`](https://github.com/shulda/lean_eppa_semigeneric/commit/df21cfa98a668e1a95dceb73ce83d852336e6842) on `main` (26 October 2026).

**Exact certification run:** [GitHub Actions #40344432058 — success](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40344432058). The final full finite SAP had also passed [PR #600 run #40342181226](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40342181226); the independent canonical iteration passed [#40338960118](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40338960118); and literal JEP passed [#40337127618](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40337127618).

**Additional source-facing corollaries:** [PR #601 run #40349653163 — success](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40349653163) certifies literal-source typed EPPA and a native-relational C4 separation wrapper; merged in [`e094e5c0`](https://github.com/shulda/lean_eppa_semigeneric/commit/e094e5c094de1909df70ef8267258e2d92c3f49b). These do not modify the main criteria audited at the earlier pinned baseline.

**Appendix A converse classification (later verified module):** integrated at [`70ae457a`](https://github.com/shulda/lean_eppa_semigeneric/commit/70ae457aa0264af70b01d07844dcfac2109b6c5b), with [successful complete CI #40465889222](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40465889222). That run built **1,861 jobs** and audited **4,050 declarations** under `SemigenericEPPA`, admitting exactly `propext`, `Classical.choice`, `Quot.sound`. It checks the two genuine original-relational SAP-necessity lemmas and the final [finite SAP iff group-valued rule theorem](Converse-rectangle-classification.md).

**v0.11 part-preservation update:** The new fixed-n expanded-language theorem uses the original coherent functor and part-quotient bijection. [Targeted CI #40868624158](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40868624158) successfully built the new theorem chain (1,343 jobs). The full library build and allowed-axiom audit must be checked on the **integrated PR head**; the targeted run alone is not a complete certificate. This is deliberately distinguished from the earlier October 27 baseline.

## What CI checks

The public [Lean workflow](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/.github/workflows/lean.yml) performs:

1. Checkout of the precise commit, setup of the pinned Lean toolchain and retrieval of precompiled Mathlib `.olean` artifacts.
2. A source check rejecting `sorry`, `admit` and explicit custom `axiom` declarations in the project Lean sources.
3. Full `lake build`, including the imported public API and the actual final theorem modules.
4. An allowed-axiom audit of the `SemigenericEPPA` library allowing **only** `propext`, `Classical.choice` and `Quot.sound`.

The precompiled Mathlib cache is a build optimization, not a new logical assumption. GitHub-workspace `.lake` caching is deliberately disabled because large archives were not economical in previous experiments.

## Local reproduction

~~~bash
git checkout df21cfa98a668e1a95dceb73ce83d852336e6842
lake exe cache get
lake build
~~~

An entirely local clean build should use the Lean toolchain from `lean-toolchain`, Mathlib from the version-pinned `lakefile.toml` and the dependencies in `lake-manifest.json`. For GitHub reproducibility, inspect the exact CI run rather than a green check on a different commit or a cancelled workflow run.

## Two separate kinds of correctness

**Lean kernel/type correctness.** The CI proves that the elaborated declarations compile and are not resting on nonallowed axioms. This includes the dependency chain, not only a `#check` of an unproved theorem signature.

**Statement fidelity.** This is independently checked in [Main theorems](Main-theorems.md), [Mathematical definitions](Mathematical-definitions.md) and [Adversarial audit](Adversarial-audit.md). In particular, those pages inspect:

- the full literal `E,R_c` class rather than a colour-coarsened reduct;
- the actual quantifier order of finite EPPA/coherent EPPA;
- the distinction $\forall$-orbit saturation vs. $\exists$-one-good-orbit;
- the genuine automorphism group, countable full age, ultrahomogeneity, density and local finiteness in DLF;
- the native semi-coherent selected-action quantifier pattern;
- arbitrary prescribed SAP embeddings and exact strong overlap.

**What CI does not prove by itself:** that a handwritten manuscript sentence equals the Lean type, nor an abstract Fraïssé uniqueness assertion not present as a Lean declaration. The source audit records these distinctions.

## Maintenance policy

Treat the main source, its pinned SHA and the exact workflow run as authoritative. A PR theorem becomes certified only after successful complete CI at the **specific head SHA**. Update the human theorem crosswalk and audit notes when changing a mathematical interface. Historical `FORMALIZATION.md` entries may contain previously open tasks; do not treat them as current against a later green main.
