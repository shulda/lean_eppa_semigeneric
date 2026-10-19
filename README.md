# Generalized semigeneric structures — Lean formalization

Formalization of the group-valued rectangle construction, EPPA, coherent EPPA, and the dense-locally-finite (DLF) criterion.

**Mathematical source:** the private `shulda/generalized_semigeneric` repository, directory `paper_formalization_prep/`. As of 2026-10-16 the formalization target is `group_valued_rectangles_formalization_v0_8.tex`; see `FORMALIZATION_PROJECT_HANDOFF_2026-10-16.md` and the corrected dependency graph. The central **ordinary EPPA theorem**, both for functional raw-colour presentations and for all literal relational R1–R3 structures, is now Lean-verified. The coherent EPPA and DLF classification arguments remain to be formalized.

This public repository keeps Lean source, an auditable [formalization ledger](FORMALIZATION.md), and GitHub Actions build/axiom checks. The private paper repository must not run CI. The existing explicit valuation witnesses are the intended proof method; the earlier `AllThoseEPPA` library is used only for its partial-isomorphism/coherence vocabulary, not as a black-box EPPA theorem.

**Project status (2026-10-19):** The **complete finite ordinary EPPA theorem** is Lean-verified for arbitrary finite raw-colour fibres, both in the raw-function presentation and the original relational R1–R3 language. See [raw EPPA](SemigenericEPPA/Structure/RawEPPA.lean), [relational EPPA](SemigenericEPPA/Structure/RelationalRawEPPA.lean) and the [typed `AllThoseEPPA` API](SemigenericEPPA/Bridge/RawTypedEPPA.lean). The finite affine residual code, fixed raw-cover witnesses and individual automorphism lifts are actual Lean constructions, not HKN applications.

**Positive coherent frontier:** The noncommutative cocycle/group-action infrastructure and fixed-baseline safe raw-cover lifts are formally verified. In the special effective case `G = 1`, the SAME padded valuation witness admits a homomorphic extension for the action of *every* group on *every* induced old substructure preserving E; see [induced singleton group lift](SemigenericEPPA/Valuations/InducedSubsingletonGroupLift.lean). The [projected flip-safety criterion](SemigenericEPPA/Bridge/ProjectedFlipSafety.lean) is also verified. **None of these results is yet a proof of full coherent raw-colour EPPA:** constructing globally flip-safe effective actions, transporting them through the fixed raw cover and assembling one groupoid functor remain separate obligations. The DLF classification and general finite SAP iteration are also open.

## Build

Lean/mathlib: pinned v4.34.1. A pinned upstream `AllThoseEPPA` dependency supplies reusable definitions.

```bash
lake update
lake exe cache get
lake build
```

CI runs on pushes, pull requests and manual dispatch, with an axiom audit allowing only `propext`, `Classical.choice` and `Quot.sound`.

See [FORMALIZATION.md](FORMALIZATION.md) for the precise theorem roadmap and proof-status distinctions.
