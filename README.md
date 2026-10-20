# Generalized semigeneric structures — Lean formalization

Formalization of the group-valued rectangle construction, EPPA, coherent EPPA, and the dense-locally-finite (DLF) criterion.

**Mathematical source:** the private `shulda/generalized_semigeneric` repository, directory `paper_formalization_prep/`. As of 2026-10-16 the formalization target is `group_valued_rectangles_formalization_v0_8.tex`; see `FORMALIZATION_PROJECT_HANDOFF_2026-10-16.md` and the corrected dependency graph. The central **ordinary EPPA theorem**, both for functional raw-colour presentations and for all literal relational R1–R3 structures, is now Lean-verified. The positive coherent EPPA theorem for the trivial effective group G is now Lean-verified in the original R1–R3 binary language for every finite functional raw-colour presentation (PR #227). Its direct wrapper for an arbitrary original relational structure is still under CI; the nontrivial-group coherent and DLF classifications remain open.

This public repository keeps Lean source, an auditable [formalization ledger](FORMALIZATION.md), and GitHub Actions build/axiom checks. The private paper repository must not run CI. The existing explicit valuation witnesses are the intended proof method; the earlier `AllThoseEPPA` library is used only for its partial-isomorphism/coherence vocabulary, not as a black-box EPPA theorem.

**Project status (2026-10-19):** The **complete finite ordinary EPPA theorem** is Lean-verified for arbitrary finite raw-colour fibres, both in the raw-function presentation and the original relational R1–R3 language. See [raw EPPA](SemigenericEPPA/Structure/RawEPPA.lean), [relational EPPA](SemigenericEPPA/Structure/RelationalRawEPPA.lean) and the [typed `AllThoseEPPA` API](SemigenericEPPA/Bridge/RawTypedEPPA.lean). The finite affine residual code, fixed raw-cover witnesses and individual automorphism lifts are actual Lean constructions, not HKN applications.

**Certified positive coherent EPPA for G=1 (2026-10-20):** The same finite raw-cover witness now supports one strictly coherent groupoid functor extending all exact old partial isomorphisms, preserving literal E and every ordered raw colour (PR #222). The final original-language upstream typed statement, [RawRectanglePresentation.finite_typedCoherentEPPA_witness](SemigenericEPPA/Bridge/GOneTypedCoherentEPPA.lean), was CI-certified and merged as PR #227. It returns a finite witness and actual typed embedding, satisfying IsCoherentEPPAWitness with the exact Equivalent and CoherentTriple clauses. The universal witness, old embedding, residual code and baseline are chosen before all partial maps.

**Pending:** the direct theorem for every preexisting IsRectangleStructure relational input (PR #225/#228). Nontrivial effective-G coherent/negative classification, relative DLF, and full finite SAP remain open. See [2026-10-20 checkpoint](CHECKPOINT_TYPED_COHERENT_GONE_2026-10-20.md).

## Build

Lean/mathlib: pinned v4.34.1. A pinned upstream `AllThoseEPPA` dependency supplies reusable definitions.

```bash
lake update
lake exe cache get
lake build
```

CI runs on pushes, pull requests and manual dispatch, with an axiom audit allowing only `propext`, `Classical.choice` and `Quot.sound`.

See [FORMALIZATION.md](FORMALIZATION.md) for the precise theorem roadmap and proof-status distinctions.
