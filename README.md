# Generalized semigeneric structures — Lean formalization

Formalization of the group-valued rectangle construction, finite SAP and JEP, EPPA, coherent EPPA, semi-coherent EPPA, the dense-locally-finite (DLF) criterion, and the converse classification of finite unrestricted SAP rectangle laws.

**Mathematical source:** private `shulda/generalized_semigeneric`, in
`paper_formalization_prep/` (initial Lean target:
`group_valued_rectangles_formalization_v0_8.tex`). The public repository
contains Lean code, an auditable [historical formalization ledger](FORMALIZATION.md),
and GitHub Actions checks; no CI is run in the private manuscript repository.
The explicit valuation/raw-colour proofs are used rather than the HKN EPPA
existence theorem; the `AllThoseEPPA` dependency supplies typed syntax and
coherence vocabulary.

## Research Wiki

[Human-readable main theorems](docs/wiki/Main-theorems.md),
[Appendix A converse classification](docs/wiki/Converse-rectangle-classification.md),
[mathematical definitions](docs/wiki/Mathematical-definitions.md), and
[independent manuscript-to-Lean audit](docs/wiki/Adversarial-audit.md)
are maintained in the [source-controlled research Wiki](docs/wiki/README.md).
The pages are synchronized to the [GitHub Wiki tab](https://github.com/shulda/lean_eppa_semigeneric/wiki)
once that separate Wiki repository is initialized; the public source
pages remain available regardless of Wiki initialization.

## Verified results (through 27 October 2026)

- **Ordinary finite EPPA: complete.** Actual witnesses for *all* finite
  original relational R1–R3 members and equivalent raw presentations,
  including the upstream typed `IsEPPAWitness` API. See
  [raw EPPA](SemigenericEPPA/Structure/RawEPPA.lean),
  [relational EPPA](SemigenericEPPA/Structure/RelationalRawEPPA.lean),
  and [typed bridge](SemigenericEPPA/Bridge/RawTypedEPPA.lean).
- **Coherent finite EPPA: complete, including arbitrary nontrivial finite
  effective groups.** Exact original-language typed coherent witnesses
  are formalized for `G=1` and for globally saturated good affine
  congruence orbits. The 2+1 / 3+1 obstruction gadgets give necessity.
  The *full* classification is
  [`RawDatum.hasFiniteRelationalCoherentEPPAInCanonicalUniverses_iff`](SemigenericEPPA/Bridge/FiniteCanonicalUniverseCoherentClassification.lean):
  `Subsingleton G ∨ (d.selfReverseEffective.Nonempty ∧ d.IsCongruenceSaturated)`.
  The theorem explicitly handles the different canonical witness
  universes in the two cases. See also the
  [nontrivial original relational iff](SemigenericEPPA/Bridge/FiniteRelationalCoherentClassification.lean).
- **DLF classification: complete for existence of a countable homogeneous
  original E/R_c raw presentation with the full finite age.**
  [`RawDatum.countableHomogeneousDLF_iff`](SemigenericEPPA/Structure/DLFCompleteClassification.lean)
  states
  `d.HasCountableHomogeneousDLF ↔ Subsingleton G ∨ d.HasCompleteGoodOrbit`.
  Here `HasCompleteGoodOrbit` requires just **one** whole affine
  congruence orbit of effective colours to lie inside the set of
  effective fibres containing reversal-fixed raw colours; no global
  saturation is assumed. The actual countable witness has full
  induced canonical finite age (hence all finite raw presentations),
  finite-partial-map ultrahomogeneity, and a dense locally finite
  subgroup of its **genuine** E- and every R_c-preserving permutation
  group. See the [positive complete-orbit limit](SemigenericEPPA/Structure/DLFCompletePositiveHomogeneousWitness.lean),
  [positive G=1 limit](SemigenericEPPA/Structure/DLFGOneCompletePositiveHomogeneousWitness.lean),
  and [negative necessity](SemigenericEPPA/Structure/DLFNegativeCompleteNecessity.lean).
  There is also a **direct original-relational formulation**
  [`RawDatum.countableRelationalHomogeneousDLF_iff`](SemigenericEPPA/Structure/DLFRelationalClassification.lean)
  with an actual `AllThoseEPPA.Structure (rectangleLanguage C)`,
  original `E` and every ordered `R_c`, and the literal automorphism
  subgroup. [The arbitrary finite relational age audit](SemigenericEPPA/Structure/DLFRelationalFullAgeAudit.lean)
  verifies induced universality on any finite carrier, not only
  canonical `Fin n` presentations.
  Original relational structures and raw presentations have an exact
  [round-trip equality](SemigenericEPPA/Structure/RelationalRoundtripEquality.lean).
  The semigeneric-specific unrestricted semi-coherent EP ⇔ DLF
  theorem is also Lean-certified; it is proved by a direct finite
  action-pair tower, not by assuming Sági's general result. An
  independent *general* Sági theorem and a stand-alone Fraïssé
  existence/uniqueness theorem are **not** yet Lean results.
- **Finite safe-action semi-coherence: complete.**
  [`RawDatum.cofinalSafeFiniteGroupExtension_iff`](SemigenericEPPA/Structure/DLFSemiCoherentSafeDLFClassification.lean)
  classifies the *concrete cofinal family of all safe finite original-raw
  automorphism actions*: it exists exactly when `G=1` or there is one
  complete good congruence orbit. Its proof includes a genuine countable
  age-cofinal finite-subgroup tower and a dense locally finite subgroup
  in the automorphism group of the limit.
- **Unrestricted semi-coherent EP: complete equivalence and classification.**
  [`RawDatum.HasFiniteRawSemiCoherentEP`](SemigenericEPPA/Structure/DLFFiniteUnrestrictedSemiCoherentEP.lean)
  selects an *arbitrary*, not necessarily locally safe, cofinal
  family of actual finite original-raw automorphism subgroup actions.
  The genuine relative group embeddings and all-partial-map
  extension clause are part of its definition. The full Lean-certified
  [converse and iff](SemigenericEPPA/Structure/DLFUnrestrictedSemiCoherentClassification.lean)
  prove
  `d.HasFiniteRawSemiCoherentEP ↔ d.HasCountableHomogeneousDLF` and
  `d.HasFiniteRawSemiCoherentEP ↔ Subsingleton G ∨ d.HasCompleteGoodOrbit`.
  The proof constructs an explicit age-cofinal finite-action tower
  and its faithful, dense locally finite subgroup in the full raw
  automorphism group; **no safety condition** is imposed on the
  selected family. The original-relational DLF correspondence is
  [also certified](SemigenericEPPA/Bridge/SemiCoherentRelationalDLFClassification.lean).
  Exact green heads: #570 `67f2d243` and #571 `58ebcdd8`
  (both merged into `main`).
- **Explicit separation example: complete.**
  [`FourColourSeparation.c4Datum`](SemigenericEPPA/Examples/FourColourDLFNotCoherent.lean)
  has `G = C₄` and `S = {0,1,2}`. Lean checks its concrete
  original raw colours and proves DLF while coherent EPPA fails
  for the same original-relational finite class. The additional
  [strict separation theorem](SemigenericEPPA/Examples/FourColourSemiCoherentSeparation.lean)
  establishes unrestricted semi-coherent EP and original-relational
  DLF together with failure of coherent EPPA in this single concrete
  example (PR #572, green head `7a9e2c34`, merged).
- **Full finite original-relational strong amalgamation (SAP): complete.**
  [`RawDatum.finiteRelationalStrongSAP`](SemigenericEPPA/Structure/FiniteRelationalStrongSAPComplete.lean)
  proves unconditional SAP for any three finite R1–R3 structures
  and any two **prescribed induced** original `E/R_c` embeddings.
  The result supplies a finite original-language amalgam with an exact
  strong square: the copies intersect precisely in the old base and
  jointly cover the amalgam carrier. The canonical finite one-point
  chain, relative transport and exact second induction are all
  Lean-certified. Integration [PR #600](https://github.com/shulda/lean_eppa_semigeneric/pull/600),
  green head `d1a31ebb`, merged into `main` as `43db8433`.
- **Finite original-relational joint embedding (JEP): complete.**
  [`RawDatum.finiteRelationalJEP`](SemigenericEPPA/Structure/FiniteRelationalJEP.lean)
  constructs actual induced embeddings from any two finite original
  `E/R_c` structures into one finite member by disjoint raw union.
  Green [PR #598](https://github.com/shulda/lean_eppa_semigeneric/pull/598),
  merged as `f6e59b86`.
- **Part abundance in homogeneous full-age models:** the certified [finite-avoidance lemma](SemigenericEPPA/Structure/DLFFullAgePartAbundance.lean) implies infinitely many infinite $E$-classes, conditional on full age and ultrahomogeneity. This module is imported by the root library.
- **Converse classification of SAP rectangle constraints (Appendix A): complete.**
  [`RectangleRule.finiteStrongSAP_iff_groupRectangle`](SemigenericEPPA/Classification/MainClassification.lean)
  proves that a finite nonempty raw palette, equipped with a reversal and
  an arbitrary isomorphism-invariant rectangle predicate over the **unrestricted
  triangle base**, has full finite original-language strong amalgamation iff
  its rectangle law is a noncommutative finite-group difference law with
  surjective reversal-equivariant raw map and an affine anti-involution.
  Crucially, the reconstructed `RawDatum.reverse` equals the original
  predicate's reversal. The SAP necessity direction is proved using literal
  induced relational embeddings and exact strong-overlap squares. See
  [the theorem statement and audit](docs/wiki/Converse-rectangle-classification.md)
  and [independent source-facing audit](CLASSIFICATION_STATEMENT_AUDIT_2026-10-27.md).
  Full integrated certification: [CI #40465889222](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40465889222), with 1,861 successful build jobs and an allowed-axiom audit of 4,050 declarations.
- **Fraïssé existence/uniqueness:** the mathematical consequences
  of hereditary closure, JEP, SAP and a finite relational language
  are standard, but an *independent Lean construction/uniqueness proof*
  for the Fraïssé limit is deliberately not claimed here.

See the [final statement-and-scope audit](FINAL_STATEMENT_AUDIT_2026-10-26.md)
and the [DLF classification audit](DLF_CLASSIFICATION_AUDIT_2026-10-25.md)
for the exact theorem interfaces, proof dependencies and manuscript comparison.

**Audit rule:** a theorem in a PR counts as certified only on an exact
head SHA with successful full GitHub Actions Lean build and allowed-axiom
audit. PR statuses change; inspect current `main` and CI, not historical
checkpoint descriptions. Previous dated notes below are historical.

## Build

Lean/mathlib: pinned v4.34.1. A pinned upstream `AllThoseEPPA` dependency supplies reusable definitions.

```bash
lake update
lake exe cache get
lake build
```

CI runs on pushes, pull requests and manual dispatch, with an axiom audit allowing only `propext`, `Classical.choice` and `Quot.sound`.

See [FORMALIZATION.md](FORMALIZATION.md) for the precise theorem roadmap and proof-status distinctions.
