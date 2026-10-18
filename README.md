# Generalized semigeneric structures — Lean formalization

Formalization of the group-valued rectangle construction, EPPA, coherent EPPA, and the dense-locally-finite (DLF) criterion.

**Mathematical source:** the private `shulda/generalized_semigeneric` repository, directory `paper_formalization_prep/`. As of 2026-10-16 the formalization target is `group_valued_rectangles_formalization_v0_8.tex`; see `FORMALIZATION_PROJECT_HANDOFF_2026-10-16.md` and the corrected dependency graph. The central **ordinary EPPA theorem**, both for functional raw-colour presentations and for all literal relational R1–R3 structures, is now Lean-verified. The coherent EPPA and DLF classification arguments remain to be formalized.

This public repository keeps Lean source, an auditable [formalization ledger](FORMALIZATION.md), and GitHub Actions build/axiom checks. The private paper repository must not run CI. The existing explicit valuation witnesses are the intended proof method; the earlier `AllThoseEPPA` library is used only for its partial-isomorphism/coherence vocabulary, not as a black-box EPPA theorem.

**Project status (2026-10-18):** **finite ordinary EPPA is fully Lean-verified for arbitrary finite raw-colour fibres**, using the explicit valuation construction and one witness fixed before choosing a partial automorphism. See [`RawRectanglePresentation.finite_rawEPPA_witness`](SemigenericEPPA/Structure/RawEPPA.lean) (PR #111) and [`IsRectangleStructure.finite_relationalRawEPPA_witness`](SemigenericEPPA/Structure/RelationalRawEPPA.lean) (PR #112). The finite affine residual code and raw cover are actual verified constructions (PRs #103 and #108), not black-box assumptions. The translation to `AllThoseEPPA.Structure.IsEPPAWitness` is being packaged separately in typed API PRs #113–#115. **Coherent EPPA, the DLF criterion, and the complete arbitrary finite SAP iteration are not established by these ordinary EPPA results**; see the most recent [formalization ledger](FORMALIZATION.md).

## Build

Lean/mathlib: pinned v4.34.1. A pinned upstream `AllThoseEPPA` dependency supplies reusable definitions.

```bash
lake update
lake exe cache get
lake build
```

CI runs on pushes, pull requests and manual dispatch, with an axiom audit allowing only `propext`, `Classical.choice` and `Quot.sound`.

See [FORMALIZATION.md](FORMALIZATION.md) for the precise theorem roadmap and proof-status distinctions.
