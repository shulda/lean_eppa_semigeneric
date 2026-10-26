# Final semigeneric statement and scope audit — 26 October 2026

## Authority and certification

Public Lean repository: `shulda/lean_eppa_semigeneric`.
Private mathematical source: `shulda/generalized_semigeneric`,
`paper_formalization_prep/group_valued_rectangles_formalization_v0_8.tex`.
This note describes the *literal Lean theorem statements* and what they
do or do not formally imply, rather than extrapolating from an informal proof.

The exact final finite-SAP integration was full-CI certified on
[PR #600](https://github.com/shulda/lean_eppa_semigeneric/pull/600),
head `d1a31ebb7a2cf20d14616e9a5aef91147f563d07`,
[successful workflow run 40342181226](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40342181226).
The six substantive Lean file blobs in this PR are byte-identical to the
independently green stacked proof #597, head `bda3030b137e`;
#600 combines them on the current main together with already green JEP
and the optimized cache. Merged SAP commit: `43db8433a0857d208bdcfd8089de336a24fa26ac`.
The JEP integration was certified by #598, head `d60d6b4897ec`,
then merged as `f6e59b86434e`.

The GitHub workflow requires a full `lake build`, rejects source-level
`sorry`/`admit`/custom `axiom` placeholders, and runs an allowed-axiom audit
permitting only `propext`, `Classical.choice` and `Quot.sound`.
This statement does not eliminate the need to check the newest `main`
workflow after later commits.

## Exact mathematical input

- `RawDatum G C` has a group `G`, an arbitrary affine anti-involution
  `s` with `s (xy) = s y * (s 1)⁻¹ * s x` and `s² = id`,
  an involutive raw reversal on `C`, a surjective `phi : C → G`
  and reversal equivariance `phi (reverse c) = s (phi c)`.
  The source does **not** impose `s 1 = 1` or commutativity of `G`.
- `rectangleLanguage C` contains exactly the binary symbols `E`
  and ordered `R_c`, with no functions. A structure satisfies
  `IsRectangleStructure d A` exactly when `E` is an equivalence,
  every cross-`E` ordered pair has a unique raw colour, within-part
  pairs are colourless, reversal is equivariant and the effective
  four-corner displacement identity holds. The Lean rectangle axiom
  also allows repeated row/column vertices; under the uniqueness
  conditions those cases reduce to tautologies.
- The functional `RawRectanglePresentation` and literal relation
  structure roundtrip preserve `E` and **every** named `R_c`.
  The embeddings used in the headline properties are genuine
  `AllThoseEPPA.Structure.Embedding` maps with identity language
  action, not merely effective-colour morphisms.

## Theorem-to-manuscript crosswalk

| Manuscript claim | Certified Lean statement | Precise scope |
|---|---|---|
| Strong amalgamation, `prop:sap` | `RawDatum.finiteRelationalStrongSAP` in `Structure/FiniteRelationalStrongSAPComplete.lean` | Every three finite original R1–R3 structures, every pair of **given** induced embeddings, a finite original-language strong amalgam; exact image intersection and joint coverage. No finiteness assumption on the parameter types `G,C` is needed for this purely finite-carrier SAP proof. |
| Joint embedding in Fraïssé-class discussion | `RawDatum.finiteRelationalJEP` in `Structure/FiniteRelationalJEP.lean` | Any two finite literal R1–R3 structures embed inducedly in a finite disjoint-union rectangle. |
| EPPA, `thm:main-intro(i)` | `IsRectangleStructure.finite_relationalRawEPPA_witness` in `Structure/RelationalRawEPPA.lean`, upstream typed witness in `Bridge/RawTypedEPPA.lean` | Every finite original-relational rectangle has one finite EPPA witness extending all its partial automorphisms. |
| Coherent EPPA, `thm:main-intro(ii)` | `RawDatum.hasFiniteRelationalCoherentEPPAInCanonicalUniverses_iff` in `Bridge/FiniteCanonicalUniverseCoherentClassification.lean` | Exactly `Subsingleton G ∨ (selfReverseEffective.Nonempty ∧ IsCongruenceSaturated)`; coherent witnesses are true typed `IsCoherentEPPAWitness` objects. Output universe differs in the trivial and nontrivial `G` branches, without changing the mathematics. |
| DLF, `thm:main-intro(iii)` | `RawDatum.countableRelationalHomogeneousDLF_iff` in `Structure/DLFRelationalClassification.lean` | Exactly `Subsingleton G ∨ HasCompleteGoodOrbit`. The existential witness is an actual countable original-relational homogeneous full-age structure with a dense locally finite subgroup of its literal full automorphism group. |
| Semigeneric-specific semi-coherent EP / DLF | `RawDatum.finiteRelationalSemiCoherentEP_iff_relationalDLF` in `Bridge/NativeRelationalSemiCoherentConverse.lean` | An unrestricted cofinal family of actual finite original-relational subgroup-action pairs with faithful relative group embeddings and all partial-map connectors; no artificial involution-safety assumption. |
| Strict separation | `FourColourSeparation.c4Datum` and `FourColourSemiCoherentSeparation.lean` | A concrete `C4` datum has DLF and unrestricted semi-coherent EP, but not coherent EPPA. |

## Full SAP proof spine

1. `LiteralSAPEmbeddings.lean` and `RelativeOnePointSAP.lean` construct
   actual finite two-new-vertex one-point strong amalgams in the
   original binary language.
2. `FinitePrefixOnePointChain.lean` decomposes an arbitrary finite
   extension into genuine original-relational induced one-point
   prefixes, preserving exact old maps.
3. `FiniteChainExactBaseMap.lean`, `PrefixChainExactBaseMap.lean`,
   `FinitePrefixBoundaryEquiv.lean` and
   `CanonicalOnePointAgainstFiniteSAP.lean` iterate the one-point
   strong square with the *prescribed* composite base embedding.
4. `OnePointAgainstCanonicalFiniteSAP.lean`,
   `FiniteExtensionNormalForm.lean`,
   `CanonicalToRelativeOnePointSAP.lean` and
   `StrongSquareRenaming.lean` transport that statement to arbitrary
   finite named carriers and actual prescribed embeddings.
5. `FiniteSAPExactSecondInduction.lean` iterates against a second
   arbitrary finite extension; `FiniteRelationalStrongSAPComplete.lean`
   eliminates its explicit intermediate local hypothesis and proves
   the unconditional final theorem.

All three `StrongSquare` requirements are retained:
commuting on the specified base, intersection of images exactly equal
to the base and covering of every output vertex by one of the two images.
Joint coverage is stronger than the bare usual SAP requirement.

## Deliberate limits of this formalization

- The preceding proofs formalize finite hereditary closure (via
  `IsRectangleStructure.pullback`), JEP and unconditional finite SAP.
  **A separate Lean theorem constructing and uniquely characterizing
  the arbitrary-data Fraïssé limit is not claimed.**
  In particular the DLF witness theorem only produces its countable
  homogeneous full-age object when its stated DLF criterion holds.
  Standard mathematical Fraïssé consequences are described in the
  manuscript but not hidden inside the SAP statement.
- The semigeneric-specific semi-coherent iff DLF is fully formalized.
  A *general*, external-language Sági iff is intentionally omitted.
- The optional converse classification of all abstract SAP rectangle
  laws (the manuscript's classification appendix) is not a dependency
  and is intentionally omitted.
- The manuscript's Ramsey/ample-generics discussion and any
  additional unrelated EPPA classes are outside the Lean scope.

Older dated sections of `FORMALIZATION.md` are preserved as
**historical checkpoint reports**: past phrases such as "SAP OPEN"
do not override the latest certified integration.
