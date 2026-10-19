# Generalized semigeneric structures — Lean formalization

Formalization of the group-valued rectangle construction, EPPA, coherent EPPA, and the dense-locally-finite (DLF) criterion.

**Mathematical source:** the private `shulda/generalized_semigeneric` repository, directory `paper_formalization_prep/`. As of 2026-10-16 the formalization target is `group_valued_rectangles_formalization_v0_8.tex`; see `FORMALIZATION_PROJECT_HANDOFF_2026-10-16.md` and the corrected dependency graph. The central **ordinary EPPA theorem**, both for functional raw-colour presentations and for all literal relational R1–R3 structures, is now Lean-verified. The coherent EPPA and DLF classification arguments remain to be formalized.

This public repository keeps Lean source, an auditable [formalization ledger](FORMALIZATION.md), and GitHub Actions build/axiom checks. The private paper repository must not run CI. The existing explicit valuation witnesses are the intended proof method; the earlier `AllThoseEPPA` library is used only for its partial-isomorphism/coherence vocabulary, not as a black-box EPPA theorem.

**Project status (2026-10-19):** The **complete finite ordinary EPPA theorem** is Lean-verified for arbitrary finite raw-colour fibres, both in the raw-function presentation and the original relational R1–R3 language. See [raw EPPA](SemigenericEPPA/Structure/RawEPPA.lean), [relational EPPA](SemigenericEPPA/Structure/RelationalRawEPPA.lean) and the [typed `AllThoseEPPA` API](SemigenericEPPA/Bridge/RawTypedEPPA.lean). The finite affine residual code, fixed raw-cover witnesses and individual automorphism lifts are actual Lean constructions, not HKN applications.

**Positive coherent frontier (2026-10-19):** Ordinary raw EPPA and the upstream typed EPPA API remain fully certified. In the G=1 sector there is now a CI-verified *safe homomorphic H-action on a fixed effective carrier* (PR #178), a universal factorial padding-size/divisibility lemma (#179), a fixed effective partial-EPPA geometry and old embedding (#180–#182), and a common affine raw baseline supporting BOTH individual zero-section raw lifts and every subsequently supplied safe H-group action (#185/#187). The old raw reference and literal induced zero-section copy are also verified (#188–#190); the abstract coherent groupoid normal form is checked (#186). **The unconditional combined coherent EPPA theorem remains open:** group actions still need assembling uniformly from actual induced old automorphism groups, and the exact typed groupoid construction is not finished. See the dated checkpoint in [FORMALIZATION.md](FORMALIZATION.md). Coherent nontrivial-G, relative DLF and complete finite SAP remain open.

## Build

Lean/mathlib: pinned v4.34.1. A pinned upstream `AllThoseEPPA` dependency supplies reusable definitions.

```bash
lake update
lake exe cache get
lake build
```

CI runs on pushes, pull requests and manual dispatch, with an axiom audit allowing only `propext`, `Classical.choice` and `Quot.sound`.

See [FORMALIZATION.md](FORMALIZATION.md) for the precise theorem roadmap and proof-status distinctions.
