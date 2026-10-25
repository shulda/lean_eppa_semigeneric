# Generalized semigeneric structures — Lean formalization

Formalization of the group-valued rectangle construction, EPPA, coherent EPPA, and the dense-locally-finite (DLF) criterion.

**Mathematical source:** private `shulda/generalized_semigeneric`, in
`paper_formalization_prep/` (initial Lean target:
`group_valued_rectangles_formalization_v0_8.tex`). The public repository
contains Lean code, an auditable [historical formalization ledger](FORMALIZATION.md),
and GitHub Actions checks; no CI is run in the private manuscript repository.
The explicit valuation/raw-colour proofs are used rather than the HKN EPPA
existence theorem; the `AllThoseEPPA` dependency supplies typed syntax and
coherence vocabulary.

## Verified results (25 October 2026)

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
  The *independent general semi-coherent EP ⇔ DLF theorem* and an
  independently packaged Fraïssé-uniqueness theorem are **not** Lean
  results; the DLF proof instead constructs its homogeneous witness
  and derives the converse directly from its full-age homogeneity.
- **Finite safe-action semi-coherence: complete.**
  [`RawDatum.cofinalSafeFiniteGroupExtension_iff`](SemigenericEPPA/Structure/DLFSemiCoherentSafeDLFClassification.lean)
  classifies the *concrete cofinal family of all safe finite original-raw
  automorphism actions*: it exists exactly when `G=1` or there is one
  complete good congruence orbit. Its proof includes a genuine countable
  age-cofinal finite-subgroup tower and a dense locally finite subgroup
  in the automorphism group of the limit.
- **Unrestricted semi-coherent finite EP: definition and positive
  implication are complete.**
  [`RawDatum.HasFiniteRawSemiCoherentEP`](SemigenericEPPA/Structure/DLFFiniteUnrestrictedSemiCoherentEP.lean)
  allows an *arbitrary*, not necessarily safe, selected cofinal family
  of actual finite automorphism groups. Its exact relative embeddings
  and all-partial-map extension clause are formalized, as is
  `HasCountableHomogeneousDLF → HasFiniteRawSemiCoherentEP`.
  The converse for arbitrary selected families is under active
  Lean CI review in PR #567 and is **not yet certified**.
- **Explicit separation example: complete.**
  [`FourColourSeparation.c4Datum`](SemigenericEPPA/Examples/FourColourDLFNotCoherent.lean)
  has `G = C₄` and `S = {0,1,2}`. Lean checks its concrete
  original raw colours and proves DLF while coherent EPPA fails
  for the same original-relational finite class.
- **SAP:** genuine one-point original-language strong amalgamation is
  certified, including actual induced embeddings; the unrestricted
  finite SAP iteration and Fraïssé existence bridge remain open.
  See [literal one-point SAP](SemigenericEPPA/Structure/LiteralSAPEmbeddings.lean).

See the [DLF classification audit](DLF_CLASSIFICATION_AUDIT_2026-10-25.md) for the precise statement, proof dependencies, manuscript comparison and remaining scope.

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
