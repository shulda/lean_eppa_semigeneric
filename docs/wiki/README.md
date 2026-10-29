# Generalized semigeneric structures — formally verified EPPA

A mathematical guide and proof audit for the Lean 4 development of the generalized semigeneric rectangle classes $\mathcal K(G,s,\phi)$. The public library proves **finite strong amalgamation, joint embedding, EPPA, the coherent-EPPA classification, the semi-coherent/DLF classification**, an explicit strict separation example, **and the converse classification of all strong-amalgamation rectangle predicates over the unrestricted triangle base**.

**Certified baseline:** [main commit `df21cfa98a66`](https://github.com/shulda/lean_eppa_semigeneric/commit/df21cfa98a668e1a95dceb73ce83d852336e6842), with [successful full Lean build and allowed-axiom audit](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40344432058). The final SAP proof was additionally verified [independently on PR #600](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40342181226). Links below lead to the **actual Lean theorem declarations**, rather than to informal summaries alone.

**Appendix A certification:** [integrated commit `70ae457a`](https://github.com/shulda/lean_eppa_semigeneric/commit/70ae457aa0264af70b01d07844dcfac2109b6c5b), with [successful full build and allowed-axiom audit #40465889222](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40465889222). This is a later certificate than the EPPA/DLF baseline above.

> A green Lean build certifies a proof of the *formal statement*. This Wiki also audits whether that statement means what the mathematical article says. The audit is an independent source/definition review, not a second proof checker.

## The mathematical results

Let $G$ be a finite group; let $s:G\to G$ be an affine anti-involution; and let $C$ be a finite raw-colour set with reversal $c\mapsto c^*$ and an equivariant surjection $\phi:C\twoheadrightarrow G$. The binary language contains an equivalence relation $E$ and one directed relation $R_c$ for each $c\in C$. The class $\mathcal K(G,s,\phi)$ consists of complete cross-part colourings satisfying the group-valued rectangle identity.

Put
$S=\{g\in G:\exists c\in C\;(\phi(c)=g\ \wedge\ c=c^*)\}$.
The affine congruence action is $a\star g=a\,g\,s(1)^{-1}s(a)$.

**Theorems (in human language).**

1. **SAP and JEP.** Every finite amalgamation diagram in $\mathcal K(G,s,\phi)$ has a *strong* finite amalgam with the specified induced embeddings, in fact with no vertices outside the union of their images. Any two finite members jointly embed.
2. **Ordinary EPPA.** Every finite member has a single finite witness extending *all* its partial automorphisms.
3. **Coherent EPPA.** The class has coherent EPPA **if and only if** $G$ is trivial, or $S$ is nonempty and a union of complete affine-congruence orbits.
4. **Semi-coherent EP and DLF.** The class has the unrestricted semi-coherent extension property **if and only if** $G$ is trivial, or **at least one** complete congruence orbit is contained in $S$. Exactly under that condition, there exists a countable homogeneous full-age original-relational structure whose full automorphism group contains a dense locally finite subgroup.
5. **Strict separation.** An explicit $G=C_4$ datum, with five raw colours and $S=\{0,1,2\}$, has ordinary EPPA, semi-coherent EP and DLF, but **not** coherent EPPA.
6. **Converse classification (Appendix A).** For any finite nonempty raw-colour alphabet with reversal and arbitrary isomorphism-invariant 2+2 rectangle predicate (and no further triangle constraints), finite strong amalgamation holds exactly for the group-difference laws with finite group, affine anti-involution and surjective reversal-equivariant raw palette map. See [Converse rectangle classification](Converse-rectangle-classification.md).
7. **Part-preserving coherent EPPA (v0.11).** When G=1, every finite A has a coherent witness B with the induced quotient map A/E_A → B/E_B bijective. Consequently every fixed bound n on the number of nonempty E-classes is preserved by the witness. For two opposite orientation colours this gives the fixed-n result in the expanded E/R_c language; the separate pure-arrow typed translation is not yet a Lean theorem. See [the v0.11 formalization page](Part-preserving-GOne-fixed-n.md).

See [Main theorems](Main-theorems.md) for complete mathematical statements, names of the corresponding Lean declarations, and precise scope qualifications.

**Fraïssé qualification.** The human paper states DLF for the automorphism group of *the* Fraïssé limit. Lean directly proves the equivalent **existence of a countable homogeneous full-age model with DLF**. Identifying that model with the Fraïssé limit uses the standard uniqueness theorem; this project does **not** additionally formalize that abstract identification. A separate certified conditional lemma, [RawRectanglePresentation.freshPart_and_oldPartExpansion_of_fullAge_homogeneous](https://github.com/shulda/lean_eppa_semigeneric/blob/782778d7c5b0c9090d80f425c446b4d824a7a1a7/SemigenericEPPA/Structure/DLFFullAgePartAbundance.lean), **does** prove that every homogeneous full-age model has infinitely many infinite $E$-parts. What remains omitted is the general Lean Fraïssé existence/uniqueness theorem. See [Adversarial audit](Adversarial-audit.md).

## Navigation

| Page | Content |
| --- | --- |
| [Part-preserving G=1 and fixed-n coherent EPPA](Part-preserving-GOne-fixed-n.md) | v0.11 strengthened witness, n-bounded classes, two orientations, and exact pure-arrow language boundary |
| [Converse rectangle classification](Converse-rectangle-classification.md) | Appendix A: exact SAP iff group-valued rectangle law, true structural witnesses and semantic scope audit |
| [Main theorems](Main-theorems.md) | Mathematician-readable results with links to exact proved Lean statements |
| [Mathematical definitions](Mathematical-definitions.md) | Raw data, affine reversal, rectangle constraints, EPPA, coherence, semi-coherence and DLF |
| [Proof architecture](Proof-architecture.md) | One-point SAP, finite iteration, valuations/raw covers, coherent lifts and DLF towers |
| [The four-colour-group example](Four-colour-group-example.md) | Actual five-raw-colour $C_4$ separation and its Lean code |
| [Adversarial audit](Adversarial-audit.md) | Independent semantic check, manuscript crosswalk, limitations and potentially misleading formulations |
| [Using the library](Using-the-library.md) | Pinned Lake dependency, useful imports and actual `#check` declarations |
| [Verification](Verification.md) | Source hashes, Actions logs, allowed axioms and reproducible builds |
| [Publishing](Publishing.md) | Publishing the version-controlled `docs/wiki` pages to the GitHub Wiki tab |

**Supplementary native APIs (independently green after the baseline):** [typed EPPA for the literal original structure](https://github.com/shulda/lean_eppa_semigeneric/blob/e094e5c094de1909df70ef8267258e2d92c3f49b/SemigenericEPPA/Bridge/RelationalTypedEPPA.lean) and [native-relational C4 separation](https://github.com/shulda/lean_eppa_semigeneric/blob/e094e5c094de1909df70ef8267258e2d92c3f49b/SemigenericEPPA/Examples/FourColourNativeSemiCoherentSeparation.lean), [CI #40349653163](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40349653163).

## Provenance

This audit compares the public Lean source to the **private `v0.8` formalization-preparation manuscript** (blob `3124ec728658652c0c9ac288d4640d195d97037c`), without publishing that manuscript or copying its proof text. The public repository is [`shulda/lean_eppa_semigeneric`](https://github.com/shulda/lean_eppa_semigeneric); [`FORMALIZATION.md`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/FORMALIZATION.md) is a historical research ledger, and [`FINAL_STATEMENT_AUDIT_2026-10-26.md`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/FINAL_STATEMENT_AUDIT_2026-10-26.md) contains the earlier completion checkpoint.

Source-controlled Wiki pages in [`docs/wiki/`](https://github.com/shulda/lean_eppa_semigeneric/tree/main/docs/wiki) are authoritative. Their synchronization to GitHub's separately initialized Wiki repository is explained under [Publishing](Publishing.md).
