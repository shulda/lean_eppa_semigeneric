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

## Verified results (24 October 2026)

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
- **DLF/semi-coherent: the finite relative safe-group EPPA theorem is
  certified, but the complete DLF classification is NOT.** Under only
  `d.HasCompleteGoodOrbit`, with no global saturation assumption,
  [`RawRectanglePresentation.exists_finiteSafeGroupEPPAExtension_of_completeGoodOrbit`](SemigenericEPPA/Structure/DLFFiniteSafeGroupEPPAExtension.lean)
  constructs a finite original-language raw extension, a finite locally
  involution-safe subgroup of its *actual* automorphism group, a strict
  injective action extending any safe selected old subgroup action, and
  individual extensions of all old partial raw automorphisms. The
  finite graph/chain cover, several negative orbit/delta-profile
  obstructions, and abstract algebraic density/local-finiteness lemmas
  are certified as separate modules. A genuine age-cofinal directed
  chain, its Fraïssé-limit automorphism subgroup and the final
  DLF necessity/iff remain to be assembled and certified.
- **SAP:** genuine one-point original-language strong amalgamation is
  certified, including actual induced embeddings; the unrestricted
  finite SAP iteration and Fraïssé existence bridge remain open.
  See [literal one-point SAP](SemigenericEPPA/Structure/LiteralSAPEmbeddings.lean).

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
