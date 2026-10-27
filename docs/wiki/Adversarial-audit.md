# Independent audit — does Lean really prove the human statements?

**Audit baseline:** [public `main` commit `df21cfa98a66`](https://github.com/shulda/lean_eppa_semigeneric/commit/df21cfa98a668e1a95dceb73ce83d852336e6842) with [successful full CI/axiom audit](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40344432058). Mathematical comparison: unpublished/private formalization-preparation manuscript **`group_valued_rectangles_formalization_v0_8.tex`**, SHA `3124ec728658652c0c9ac288d4640d195d97037c`. This page does not reproduce its private proof text.

**Meaning of "audited":** the exact Lean declarations, the definitions appearing in their propositions, and the manuscript's theorem statements were read separately. Successful CI certifies proofs *of the Lean statements*, not this independent semantic correspondence. This is a source-facing mathematical review, **not a second kernel verification**.

## Main manuscript-to-Lean crosswalk

| Human manuscript result | Direct Lean result | Verdict and qualifications |
| --- | --- | --- |
| `prop:sap`: strong amalgamation | [`RawDatum.finiteRelationalStrongSAP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/FiniteRelationalStrongSAPComplete.lean) | **Verified, stronger finite amalgam:** given any *actual induced* finite original `E,R_c` span, the images overlap exactly in the specified base **and cover the witness**. Fraïssé existence/uniqueness is not included in this named theorem, but a separate proved conditional lemma establishes the infinite-parts clause: [RawRectanglePresentation.freshPart_and_oldPartExpansion_of_fullAge_homogeneous](https://github.com/shulda/lean_eppa_semigeneric/blob/782778d7c5b0c9090d80f425c446b4d824a7a1a7/SemigenericEPPA/Structure/DLFFullAgePartAbundance.lean). |
| Joint embedding used in the Fraïssé argument | [`RawDatum.finiteRelationalJEP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/FiniteRelationalJEP.lean) | **Verified** in the original language. `IsRectangleStructure.pullback` supplies hereditary closure under induced restrictions. |
| `thm:main-intro(i)` / `thm:eppa`: ordinary EPPA | [`IsRectangleStructure.finite_relationalRawEPPA_witness`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/RelationalRawEPPA.lean), [typed raw witness](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/RawTypedEPPA.lean) | **Verified.** One finite witness before *all* original partial automorphisms. Actual original relations, not just the effective $G$-colour reduct. |
| `thm:main-intro(ii)` / `thm:coherent`: coherent EPPA iff | [`hasFiniteRelationalCoherentEPPAInCanonicalUniverses_iff`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/FiniteCanonicalUniverseCoherentClassification.lean) | **Verified with explicit witness-universe packaging.** The condition is **trivial $G$ OR ($S\ne\emptyset$ and globally saturated)**, not merely existence of one good orbit. Real typed coherent witnesses. |
| `thm:main-intro(iii)`: DLF of $Aut(M(G,s,\phi))$ | [`countableRelationalHomogeneousDLF_iff`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/DLFRelationalClassification.lean) | **Verified existential homogeneous-model iff; one standard external step remains:** the structure is not explicitly identified by a separate Lean Fraïssé uniqueness theorem with a predefined limit $M(G,s,\phi)$. |
| `thm:semi`: semi-coherent EP iff DLF iff one good orbit/trivial $G$ | [`finiteRelationalSemiCoherentEP_iff_relationalDLF`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/NativeRelationalSemiCoherentConverse.lean) and the [DLF classification](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/DLFRelationalClassification.lean) | **Verified for this exact semigeneric class**, without assuming safety of the selected family. Not a formalization of the general Sági theorem for all Fraïssé classes. |
| `cor:separation`: C4 example | [`c4Datum` and negative/positive claims](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourDLFNotCoherent.lean), [`semiCoherentDLFNotCoherent`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourSemiCoherentSeparation.lean) | **Verified concrete raw palette, not just an abstract orbit argument.** Relational semi-coherence follows using the separately proved raw-to-native equivalence. |
| `thm:converse-classification` (optional appendix) | — | **Not formalized** by agreement. It is not used as an assumption in EPPA, SAP or DLF. |
| `thm:sagi-bridge` (general Sági theorem) | — | **Not formalized** by agreement. The class-specific semi-coherent ⇔ DLF theorem is proved internally instead. |

## Additional post-baseline native wrappers

The main theorem crosswalk above is pinned to `df21cfa9`. A separate [successful full CI + axiom audit on PR #601](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40349653163) additionally certifies two *non-strengthening* interface results, merged as `e094e5c0`: [original-relational typed EPPA](https://github.com/shulda/lean_eppa_semigeneric/blob/e094e5c094de1909df70ef8267258e2d92c3f49b/SemigenericEPPA/Bridge/RelationalTypedEPPA.lean) from literal source-structure equality, and [the fully native C4 separation](https://github.com/shulda/lean_eppa_semigeneric/blob/e094e5c094de1909df70ef8267258e2d92c3f49b/SemigenericEPPA/Examples/FourColourNativeSemiCoherentSeparation.lean) from raw↔relational semi-coherent equivalence. These wrappers make the correspondence easier to consume directly in Lean but do not alter the proven criteria.

## Checks designed to catch misleading theorem names

### 1. Is the class genuinely the printed binary class?

**Yes.** [`RawDatum`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Algebra/RawDatum.lean) carries `s^2=1`, the **shifted** anti-multiplication law, raw reversal, surjective $\phi$ and equivariance. [`IsRectangleStructure`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/Language.lean) expresses the equivalence $E$, unique directed raw cross-colour, reversal and rank-one group equation. The absence of explicit distinctness assumptions in formal (R3) only adds degenerate tautologies under (R2); it does not remove a genuine valid structure.

**Warning avoided:** no use of $s(1)=1$, abelian $G$, globally normalized torsor origin, or injective $\phi$.

### 2. Could the raw presentation be a weaker reduct?

**No.** [`toRawPresentation_toStructure_eq`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/RelationalRoundtripEquality.lean) establishes **actual equality** with the original relational structure. Both positive constructions preserve/reflect all ordered $R_c$, rather than only $\phi(c)$.

### 3. Could "coherent EPPA" mean only individual lifts?

**No.** The target [`Structure.IsCoherentEPPAWitness`](https://github.com/shulda/lean_all_those_eppa_classes/blob/d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d/AllThoseEPPA/EPPA.lean) contains a `CoherentExtension` assigning lifts to **all** partial automorphisms, with explicit equality on equivalent maps and the compatible-triple law. The classification's positive branch produces such a typed witness; necessity comes from separate obstructions.

**Universe caveat:** the publicly named relational class predicate quantifies input carriers at `Type` (universe zero) and permits distinct output universes for $G=1$ and $G\ne1$. All ordinary finite mathematical structures admit representatives in a small universe. This is not a hidden algebraic restriction, but the Wiki should not claim that Lean's statement quantifies **all meta-theoretic universes**.

### 4. Is the DLF group the real full automorphism group?

**Yes.** [`HasCountableRelationalHomogeneousDLF`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/DLFRelationalClassification.lean) has a single actual original relation structure with its true full subgroup of `Equiv.Perm X` preserving $E$ and every $R_c$. Density means matching finite restrictions of all full automorphisms, and local finiteness quantifies finite generation inside the selected subgroup.

**Scope caveat:** it is an **existence theorem** for a countable *homogeneous full-age* original model; it does not formally name/identify that model with a separately constructed Fraïssé limit, even though this is the standard mathematical interpretation.

### 5. Is semi-coherent EP really unrestricted?

**Yes.** [`HasFiniteRelationalSemiCoherentEP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/NativeRelationalSemiCoherentEP.lean) quantifies arbitrary selected cofinal finite original-relational subgroup-action pairs. Its relative extension clause uses **injective group homomorphisms**, exact equivariance and extensions of **all** partial automorphisms of the prescribed overstructure. No condition that the selected family be *safe* appears in the property. Safety is used to exhibit one successful family in one direction.

### 6. Is SAP only for canonical inclusions?

**No.** [`HasFiniteRelationalStrongSAP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/FiniteRelationalStrongSAP.lean) quantifies all finite $A,B,C$ and *arbitrary specified* typed induced embeddings $A\to B,C$. [`finiteRelationalStrongSAP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/FiniteRelationalStrongSAPComplete.lean) normalizes and transports back exactly; [`StrongSquare`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/StrongSquare.lean) includes exact overlap and joint coverage. This is stronger than bare AP.

### 7. Does the C4 counterexample actually exist as a raw datum?

**Yes.** [`FourColourDLFNotCoherent.lean`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourDLFNotCoherent.lean) explicitly defines five raw symbols with reversal swapping two over effective colour $3$, checks $\phi$ is surjective and equivariant, proves one whole good orbit and failure of global saturation, and proves $G$ is nontrivial. The same datum supplies both DLF and coherent failure.

## Added Appendix A audit — converse rectangle classification

The original v0.8 Appendix A is logically independent of the EPPA/DDL arguments. Its converse is now given by [`RectangleRule.finiteStrongSAP_iff_groupRectangle`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/MainClassification.lean), with the **original** \(E,R_c\) relational predicate [`IsRuleStructure`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/GeneralRuleStructure.lean).

**Independent semantic checks.** (1) \(C\) is finite and nonempty. (2) \(P\) is assumed only to respect the three isomorphisms of \(2+2\) rectangles, and there are no further triangle restrictions. (3) The general \(P\) is checked only on *distinct* rows and columns; the reconstructed group equation also automatically handles coinciding corners. (4) SAP is checked on all prescribed finite original-relational induced embeddings; its `StrongSquare` demands exact overlap and joint coverage. (5) The classification explicitly asserts the **same** reversal \(c\mapsto c^*\) in the returned `RawDatum`. (6) \(G\) is finite and need not be abelian, and \(s(1)\) is not constrained to be \(1\). (7) The two SAP-to-algebra lemmas are proved from literal spans, not given as independent hypotheses in the final iff. Crucially, row amalgamation uses `StrongSquare.exact_overlap` to prevent identification of two fresh row vertices.

**Joint-coverage nuance.** The Lean SAP predicate requests the amalgam carrier to be exactly the union of the two images, an apparently stronger formulation than the usual SAP. For any hereditary class of finite relational structures, restriction to the induced union turns an arbitrary strong amalgam into one with joint coverage, so these are mathematically equivalent. No independent general Fraïssé existence/uniqueness statement is asserted by this theorem.

**Boundaries.** This is **not** a classification for additional forbidden triangles, finitely bounded imprimitive classes with extra constraints, arbitrary higher-arity ages, or ordinary AP without SAP. The [dedicated Appendix A page](Converse-rectangle-classification.md) cross-references every Lean proof component.

## Open *semantic* scope, not unproved main statements

- **Not formalized here:** unconditional standalone Fraïssé limit existence/uniqueness for every datum. **Already formalized:** [RawRectanglePresentation.freshPart_and_oldPartExpansion_of_fullAge_homogeneous](https://github.com/shulda/lean_eppa_semigeneric/blob/782778d7c5b0c9090d80f425c446b4d824a7a1a7/SemigenericEPPA/Structure/DLFFullAgePartAbundance.lean) directly proves finite-avoidance consequences implying infinitely many infinite $E$-classes for any model having full finite age and ultrahomogeneity. This does not construct such a model for every datum.
- **Not a Lean theorem here:** general Sági equivalence for arbitrary classes. The converse classification of finite unrestricted SAP rectangle laws was **subsequently formalized** in Appendix A modules; it does not cover extra triangle constraints or AP-only classes.
- **Not an extra hypothesis:** global saturation in coherent EPPA is part of its iff, but must **not** be imposed on DLF/semi-coherence. For $G=1$, neither statement requires $S\ne\emptyset$.
- **Not claimed:** structure-faithful EPPA or coherent EPPA for nonsaturated datums, a general Ramsey theorem, ample generics, or typed EPPA for an unrelated class.

**Conclusion of the independent comparison:** the original-language finite SAP/JEP, ordinary EPPA, coherent-EPPA iff and the class-specific semi-coherent/DLF iff have matching proved Lean endpoints. The named Fraïssé-limit existence/uniqueness remains a standard external consequence, while the conditional infinite-parts property is machine-checked in [RawRectanglePresentation.freshPart_and_oldPartExpansion_of_fullAge_homogeneous](https://github.com/shulda/lean_eppa_semigeneric/blob/782778d7c5b0c9090d80f425c446b4d824a7a1a7/SemigenericEPPA/Structure/DLFFullAgePartAbundance.lean). No additional algebraic assumptions or contradictory definitions were found in this audit.
