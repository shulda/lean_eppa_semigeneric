# Generalized semigeneric structures — Lean formalization

Formalization of the group-valued rectangle construction, EPPA, coherent EPPA, and the dense-locally-finite (DLF) criterion.

**Mathematical source:** the private `shulda/generalized_semigeneric` repository, directory `paper_formalization_prep/`. As of 2026-10-16 the formalization target is `group_valued_rectangles_formalization_v0_8.tex`; see `FORMALIZATION_PROJECT_HANDOFF_2026-10-16.md` and the corrected dependency graph. The paper's proofs have been audited by humans but **are not yet Lean-verified**.

This public repository keeps Lean source, an auditable [formalization ledger](FORMALIZATION.md), and GitHub Actions build/axiom checks. The private paper repository must not run CI. The existing explicit valuation witnesses are the intended proof method; the earlier `AllThoseEPPA` library is used only for its partial-isomorphism/coherence vocabulary, not as a black-box EPPA theorem.

**Project status (2026-10-18):** the formalization now contains machine-checked foundational rectangle/gauge lemmas, finite one-point strong amalgamation, the finite two-layer effective EPPA witness, its exact padded old embedding, compatible partial-map class/real permutations, and affine multiplier/valuation transport gates (through PR #72). **The unconditional effective EPPA theorem and all headline ordinary/coherent EPPA and DLF statements remain OPEN** until the final full old-vertex automorphism assembly and the remaining raw/fixed-action proofs pass CI. See the dated checkpoint at the end of [FORMALIZATION.md](FORMALIZATION.md).

## Build

Lean/mathlib: pinned v4.34.1. A pinned upstream `AllThoseEPPA` dependency supplies reusable definitions.

```bash
lake update
lake exe cache get
lake build
```

CI runs on pushes, pull requests and manual dispatch, with an axiom audit allowing only `propext`, `Classical.choice` and `Quot.sound`.

See [FORMALIZATION.md](FORMALIZATION.md) for the precise theorem roadmap and proof-status distinctions.
