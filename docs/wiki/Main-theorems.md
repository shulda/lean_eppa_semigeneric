# Main mathematical theorems — human statements and Lean proofs

**Version pinned for this crosswalk:** [`df21cfa98a66`](https://github.com/shulda/lean_eppa_semigeneric/commit/df21cfa98a668e1a95dceb73ce83d852336e6842), successful [full build + axiom audit](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40344432058). See [Definitions](Mathematical-definitions.md) for $\mathcal K(G,s,\phi)$, $S$, and the affine congruence action.

Throughout, $G$ and $C$ are finite, $s:G\to G$ is an arbitrary affine anti-involution, $c\mapsto c^*$ is a raw reversal involution, and $\phi:C\to G$ is surjective and reversal-equivariant. No commutativity of $G$ or normalization $s(1)=1$ is required. These hypotheses are packaged in [`RawDatum G C`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Algebra/RawDatum.lean), with finiteness imposed where needed.

## Theorem 0 — the converse classification of strong-amalgamation rectangle laws

**Statement (Appendix A).** Fix a finite, **nonempty** set of directed raw colours $C$, equipped with an involution $c\mapsto c^*$. Let $P:C^4\to\mathrm{Prop}$ be an arbitrary $2+2$ rectangle predicate invariant under row interchange, column interchange and starred transpose. The finite original-language class $\mathcal K_P$ has an equivalence relation $E$, exactly one directed $R_c$ on every cross-$E$-class ordered pair (with reversal $c^*$), **no additional triangle restrictions**, and the constraint $P$ precisely on genuine rectangles with two distinct vertices in each of two different $E$-classes.

Then $\mathcal K_P$ has the **strong amalgamation property** if and only if there exist a finite (possibly noncommutative) group $G$, an affine anti-involution $s:G\to G$, and a surjection $\phi:C\twoheadrightarrow G$ such that
$

\phi(c^*)=s(\phi(c))
\quad\text{and}\quad
P(a,b,c,d)\ \Longleftrightarrow\
\phi(a)^{-1}\phi(b)=\phi(c)^{-1}\phi(d).

$

**Certificate:** [full root build and allowed-axiom audit #40465889222](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40465889222), commit [`70ae457a`](https://github.com/shulda/lean_eppa_semigeneric/commit/70ae457aa0264af70b01d07844dcfac2109b6c5b).

**Exact Lean theorem:** [`RectangleRule.finiteStrongSAP_iff_groupRectangle`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/MainClassification.lean). The classifier explicitly requires **the reconstructed raw reversal to equal the given reversal of $P$** (not merely some alternative involution). [`RectangleRule.HasFiniteRuleStrongSAP`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/GeneralRuleStructure.lean) quantifies over every prescribed finite induced $E,R_c$ embedding span and returns an exact strong amalgamation square. The witness covers the union of the two embedded structures; for this hereditary relational class that is equivalent to usual SAP by restricting any strong amalgam to that union.

**Proof:** [SAP implies corner completion](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/SAPCornerCompletion.lean), [SAP implies row amalgamation](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/SAPRowAmalgamation.lean) using exact overlap, [quotient of displacement profiles](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/RectangleDisplacements.lean), [regular permutation group](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/DisplacementTranslations.lean), [affine anti-involution and raw datum](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/AffineClassification.lean), and [SAP of the reconstructed group class](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Classification/GeneralRuleStructure.lean), using the already certified original-language SAP theorem.

See the dedicated [converse classification page](Converse-rectangle-classification.md) for the independent hypothesis/statement audit and proof dependency crosswalk. This is **not** a classification with extra forbidden triangles, nor a theorem with ordinary AP in place of SAP.

## Theorem A — strong amalgamation and joint embedding

**Statement.** Let $A,B_1,B_2\in\mathcal K(G,s,\phi)$ be finite, with **given induced embeddings** $f_i:A\hookrightarrow B_i$. Then there are a finite $D\in\mathcal K(G,s,\phi)$ and induced embeddings $g_i:B_i\hookrightarrow D$ such that

$
g_1 f_1=g_2 f_2,\qquad g_1(B_1)\cap g_2(B_2)=g_1f_1(A),
\qquad D=g_1(B_1)\cup g_2(B_2).
$

Moreover, any two finite members have a common finite induced extension (JEP), with no identifications between the two initial vertex sets.

**Exact Lean results:** [`RawDatum.finiteRelationalStrongSAP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/FiniteRelationalStrongSAPComplete.lean) proves [`RawDatum.HasFiniteRelationalStrongSAP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/FiniteRelationalStrongSAP.lean), using an explicit [`StrongSquare`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/StrongSquare.lean). The separate [`RawDatum.finiteRelationalJEP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/FiniteRelationalJEP.lean) uses disjoint raw union. Both are in the **original binary `E,R_c` language** and use genuine typed induced embeddings. SAP actually needs no ambient finiteness of the parameter types $G,C$ (only finite *input carriers*), a safe strengthening of the manuscript's finite-datum statement.

**Certificate:** [SAP PR #600, success](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40342181226), [JEP PR #598, success](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40337127618).

**Fraïssé status:** A separate general Lean Fraïssé existence/uniqueness theorem is not part of this library. **The infinite-parts consequence is formalized conditionally:** [RawRectanglePresentation.freshPart_and_oldPartExpansion_of_fullAge_homogeneous](https://github.com/shulda/lean_eppa_semigeneric/blob/782778d7c5b0c9090d80f425c446b4d824a7a1a7/SemigenericEPPA/Structure/DLFFullAgePartAbundance.lean) shows that any original raw structure with full finite age and finite-partial ultrahomogeneity has (i) arbitrarily new $E$-classes disjoint from any given finite set and (ii) arbitrarily many additional vertices in the $E$-class of any fixed vertex. Thus every such model has infinitely many infinite $E$-classes.

## Theorem B — ordinary EPPA

**Statement.** For every finite $A\in\mathcal K(G,s,\phi)$ there exist a **single finite** $B\in\mathcal K(G,s,\phi)$ and a fixed induced embedding $i:A\hookrightarrow B$ such that for every partial automorphism `p` of `A` there is an automorphism $\widehat p\in\operatorname{Aut}(B)$ satisfying $\widehat p(i(a))=i(p(a))$ for every `a` in the domain of `p`.

**Exact Lean results:** [`IsRectangleStructure.finite_relationalRawEPPA_witness`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/RelationalRawEPPA.lean) quantifies **one witness before all partial maps**, preserves $E$ and each ordered $R_c$ and returns an honest permutation preserving the original relations. [`RawRectanglePresentation.finite_typedEPPA_witness`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/RawTypedEPPA.lean) proves the upstream [`Structure.IsEPPAWitness`](https://github.com/shulda/lean_all_those_eppa_classes/blob/d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d/AllThoseEPPA/EPPA.lean). Crucially, [`IsRectangleStructure.toRawPresentation_toStructure_eq`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/RelationalRoundtripEquality.lean) shows exact equality of the original input with its raw encoding. **This is ordinary EPPA, not a coherence statement.**

**Additional directly typed relational endpoint:** after this audit baseline, [`IsRectangleStructure.finite_relationalTypedEPPA_witness`](https://github.com/shulda/lean_eppa_semigeneric/blob/e094e5c094de1909df70ef8267258e2d92c3f49b/SemigenericEPPA/Bridge/RelationalTypedEPPA.lean) was certified in [PR #601](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40349653163) and merged as `e094e5c0`. It proves the actual upstream `Structure.IsEPPAWitness` with the *literal original source A*, using the exact raw/relational structure equality. This is a convenience statement, not a new mathematical hypothesis.

## Theorem C — coherent EPPA classification

**Statement.** The entire finite class $\mathcal K(G,s,\phi)$ has **coherent EPPA** if and only if

$G=\{1\}\quad\text{or}\quad\bigl(S\ne\varnothing\ \text{and}\ a\star g\in S\ \text{for all}\ a\in G,\ g\in S\bigr).$

A coherent witness simultaneously chooses extensions of *all* partial automorphisms so that equivalent partial maps receive the same extension and composition of compatible partial maps becomes multiplication of their chosen extensions.

**Exact Lean result:** [`RawDatum.hasFiniteRelationalCoherentEPPAInCanonicalUniverses_iff`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/FiniteCanonicalUniverseCoherentClassification.lean), where the predicate `HasFiniteRelationalCoherentEPPAInCanonicalUniverses` returns a finite genuine original-relational [`Structure.IsCoherentEPPAWitness`](https://github.com/shulda/lean_all_those_eppa_classes/blob/d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d/AllThoseEPPA/EPPA.lean). The proof includes both the positive coherent construction and necessity via explicit small obstruction gadgets.

**Exact logical condition:** `Subsingleton G ∨ (d.selfReverseEffective.Nonempty ∧ d.IsCongruenceSaturated)`. The positive $G=1$ branch works even if $S=\varnothing$. `IsCongruenceSaturated` requires **all** good congruence orbits to be complete, not just one.

**Universe packaging:** The class predicate quantifies finite input types at `Type` (universe zero) and allows different natural witness universes in the $G=1$ and $G\ne1$ branches. This is a formal representation choice, not an additional algebraic condition; mathematically any finite set can be represented in a small finite universe.

## Theorem C1 — part-preserving coherent EPPA and fixed-n subclasses (v0.11)

**Stronger G=1 assertion.** For every finite member $A$ of the original rectangle class $\mathcal K(1,\mathrm{id},\phi)$, with its finite raw involutive alphabet, there is **one finite coherent EPPA witness** $B$ and induced embedding $\psi:A\hookrightarrow B$ such that
$

A/E_A\ \simeq\ B/E_B,\qquad
[x]\ \longmapsto\ [\psi(x)] .

$
This is a bijection of the actual nonempty equivalence classes, not a numerical equality asserted without a map. The statement includes the empty-carrier case.

**Exact Lean endpoint:** [`RawRectanglePresentation.finite_partPreservingTypedCoherentEPPA_witness`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Bridge/GOneTypedCoherentEPPA.lean). It uses the original **single** coherent witness and full coherent-extension functor. The generic quotient lemma is [`partQuotientEquivOfCover`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Structure/PartQuotientCover.lean); every witness class meets the old copy by [`gOneJointRawPart_coveredByOld`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Bridge/GOnePartPreservation.lean).

**Fixed-n subclass.** For any natural number $n$, an n-bounded member means there exists an injection of its actual nonempty E-class quotient into $\mathrm{Fin}(n)$, hence **at most** n nonempty parts (unused labels permitted). The same coherent witness remains n-bounded. This is proved for **arbitrary original relational E/R_c structures**, not just raw presentations, by [`IsRectangleStructure.finite_boundedPartsRelationalCoherentEPPA_witness`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Bridge/BoundedPartsCoherentEPPA.lean). No assumption $n\geq2$ is needed to prove this more general bounded-class statement.

**Two opposite orientations.** The concrete $G=1$, $C=\mathrm{Bool}$ data, with reversal swapping the two orientations, are given by [`twoOrientationGOneDatum`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Bridge/TwoColourPartiteCorollary.lean). The same file certifies $E(x,y)\leftrightarrow\neg (x\to y)\wedge\neg(y\to x)$ and provides [`finite_twoOrientationExpandedNPartiteCoherentEPPA`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Bridge/TwoColourPartiteCorollary.lean) for the **expanded** original E/R_false/R_true language.

**Precise limitation:** the last file does **not** assert the same fully typed `IsCoherentEPPAWitness` proposition in a *different* one-symbol directed-edge language. Transport of partial automorphisms, `Equivalent`, `CoherentTriple` and the extension functor across the definitional expansion remains an explicit independent API obligation. The usual mathematical fixed-n tournament corollary follows from the definable expansion, but that pure-arrow-language formal statement has not been directly certified. Likewise, DLF of the fixed-n Fraïssé limit follows from the mathematical coherent-EPPA/Sági correspondence; no new fixed-n DLF theorem is claimed in Lean.

See [the detailed v0.11 note](Part-preserving-GOne-fixed-n.md) and [independent audit](Adversarial-audit.md) for scope and dependencies.

## Theorem D — semi-coherent EP, DLF and their classification

**Statement.** The following are equivalent for the given finite datum:

1. The original finite class has the **unrestricted semi-coherent extension property**: a cofinal choice of finite pairs $(A,H)$ with $H\le\operatorname{Aut}(A)$, closed under suitable relative finite extensions that embed `H` injectively and equivariantly into the next group, and extend *every* partial automorphism of the prescribed finite overstructure in that same group.
2. There exists a countable ultrahomogeneous original `E,R_c` structure $M$ with **full age** $\mathcal K(G,s,\phi)$ and a dense locally finite subgroup of its **actual** $\operatorname{Aut}(M)$.
3. $G=1$, or $S$ contains **at least one** entire affine-congruence orbit:
   $\exists g\in S\ \forall a\in G\colon a\star g\in S$.

**Exact Lean results:** [`RawDatum.finiteRelationalSemiCoherentEP_iff_relationalDLF`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/NativeRelationalSemiCoherentConverse.lean), [`RawDatum.countableRelationalHomogeneousDLF_iff`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/DLFRelationalClassification.lean), and the unrestricted raw classification [`RawDatum.finiteRawSemiCoherentEP_iff`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/DLFUnrestrictedSemiCoherentClassification.lean).

The [literal relational DLF predicate](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/DLFRelationalClassification.lean) explicitly requires **countable carrier, induced copies of every finite age object, extension of every finite partial map, and a subgroup dense by finite restrictions and locally finite in the finitely generated subgroup sense**. It is not the existence of some abstract locally finite group unrelated to automorphisms. The native semi-coherent family does **not** assume local involution safety.

**Important distinction:** This proves existence of such a countable homogeneous $M$, not a named theorem asserting its identity with a separately constructed Fraïssé limit. The latter identification follows from ordinary Fraïssé uniqueness *outside this Lean development*. The proof of the equivalence for **this class** is internal to Lean; no general Sági equivalence is assumed.

## Theorem E — strict separation

**Statement.** There is a concrete finite datum with $G=C_4$, $s=\mathrm{id}$ and a five-element raw alphabet such that $S=\{0,1,2\}$. Its congruence orbits are $\{0,2\}$ and $\{1,3\}$, so it has ordinary EPPA, unrestricted semi-coherent EP and DLF, **but not coherent EPPA**.

**Exact Lean results:** [`FourColourSeparation.c4Datum`, `hasCompleteGoodOrbit`, `notCongruenceSaturated`, `notRelationalCoherentEPPA`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourDLFNotCoherent.lean) and [`FourColourSeparation.semiCoherentDLFNotCoherent`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourSemiCoherentSeparation.lean). The last theorem uses raw semi-coherent EP; the previously proved native raw↔relational equivalence transfers it to the same original-relational class. An additional [`FourColourSeparation.nativeSemiCoherentDLFNotCoherent`](https://github.com/shulda/lean_eppa_semigeneric/blob/e094e5c094de1909df70ef8267258e2d92c3f49b/SemigenericEPPA/Examples/FourColourNativeSemiCoherentSeparation.lean) packages **all three conjuncts directly in the original-relational API** ([green PR #601](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40349653163)). See the [example page](Four-colour-group-example.md).

## Reading the type, not only the name

[`RawDatum`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Algebra/RawDatum.lean), [`IsRectangleStructure`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/Language.lean), [`HasFiniteRelationalStrongSAP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/FiniteRelationalStrongSAP.lean), [`HasFiniteRelationalCoherentEPPAInCanonicalUniverses`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/FiniteCanonicalUniverseCoherentClassification.lean), [`HasFiniteRelationalSemiCoherentEP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/NativeRelationalSemiCoherentEP.lean), and [`HasCountableRelationalHomogeneousDLF`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/DLFRelationalClassification.lean) are part of the mathematical assertions, not implementation details to be ignored. Their meanings are audited explicitly on the [Adversarial audit](Adversarial-audit.md) page.
