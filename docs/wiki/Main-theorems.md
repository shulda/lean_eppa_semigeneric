# Main mathematical theorems — human statements and Lean proofs

**Version pinned for this crosswalk:** [`df21cfa98a66`](https://github.com/shulda/lean_eppa_semigeneric/commit/df21cfa98a668e1a95dceb73ce83d852336e6842), successful [full build + axiom audit](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40344432058). See [Definitions](Mathematical-definitions.md) for `\mathcal K(G,s,\phi)`, `S`, and the affine congruence action.

Throughout, `G` and `C` are finite, `s:G\to G` is an arbitrary affine anti-involution, `c\mapsto c^*` is a raw reversal involution, and `\phi:C\to G` is surjective and reversal-equivariant. No commutativity of `G` or normalization `s(1)=1` is required. These hypotheses are packaged in [`RawDatum G C`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Algebra/RawDatum.lean), with finiteness imposed where needed.

## Theorem A — strong amalgamation and joint embedding

**Statement.** Let `A,B_1,B_2\in\mathcal K(G,s,\phi)` be finite, with **given induced embeddings** `f_i:A\hookrightarrow B_i`. Then there are a finite `D\in\mathcal K(G,s,\phi)` and induced embeddings `g_i:B_i\hookrightarrow D` such that

`g_1 f_1=g_2 f_2,\qquad g_1(B_1)\cap g_2(B_2)=g_1f_1(A),\qquad D=g_1(B_1)\cup g_2(B_2).`

Moreover, any two finite members have a common finite induced extension (JEP), with no identifications between the two initial vertex sets.

**Exact Lean results:** [`RawDatum.finiteRelationalStrongSAP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/FiniteRelationalStrongSAPComplete.lean) proves [`RawDatum.HasFiniteRelationalStrongSAP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/FiniteRelationalStrongSAP.lean), using an explicit [`StrongSquare`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/StrongSquare.lean). The separate [`RawDatum.finiteRelationalJEP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/FiniteRelationalJEP.lean) uses disjoint raw union. Both are in the **original binary `E,R_c` language** and use genuine typed induced embeddings. SAP actually needs no ambient finiteness of the parameter types `G,C` (only finite *input carriers*), a safe strengthening of the manuscript's finite-datum statement.

**Certificate:** [SAP PR #600, success](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40342181226), [JEP PR #598, success](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40337127618).

**Limit:** The manuscript's further claim that the class is Fraïssé and that its limit has infinitely many infinite `E`-parts is a standard mathematical consequence, but an independent Lean Fraïssé-existence theorem and the infinite-parts corollary are **not** proved here under those names.

## Theorem B — ordinary EPPA

**Statement.** For every finite `A\in\mathcal K(G,s,\phi)` there exist a **single finite** `B\in\mathcal K(G,s,\phi)` and a fixed induced embedding `i:A\hookrightarrow B` such that for every partial automorphism `p` of `A` there is an automorphism `\widehat p\in\operatorname{Aut}(B)` satisfying `\widehat p(i(a))=i(p(a))` for every `a` in the domain of `p`.

**Exact Lean results:** [`IsRectangleStructure.finite_relationalRawEPPA_witness`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/RelationalRawEPPA.lean) quantifies **one witness before all partial maps**, preserves `E` and each ordered `R_c` and returns an honest permutation preserving the original relations. [`RawRectanglePresentation.finite_typedEPPA_witness`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/RawTypedEPPA.lean) proves the upstream [`Structure.IsEPPAWitness`](https://github.com/shulda/lean_all_those_eppa_classes/blob/d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d/AllThoseEPPA/EPPA.lean). Crucially, [`IsRectangleStructure.toRawPresentation_toStructure_eq`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/RelationalRoundtripEquality.lean) shows exact equality of the original input with its raw encoding. **This is ordinary EPPA, not a coherence statement.**

## Theorem C — coherent EPPA classification

**Statement.** The entire finite class `\mathcal K(G,s,\phi)` has **coherent EPPA** if and only if

`G=\{1\}\quad\text{or}\quad\bigl(S\ne\varnothing\ \text{and}\ a\star g\in S\ \text{for all}\ a\in G,\ g\in S\bigr).`

A coherent witness simultaneously chooses extensions of *all* partial automorphisms so that equivalent partial maps receive the same extension and composition of compatible partial maps becomes multiplication of their chosen extensions.

**Exact Lean result:** [`RawDatum.hasFiniteRelationalCoherentEPPAInCanonicalUniverses_iff`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/FiniteCanonicalUniverseCoherentClassification.lean), where the predicate `HasFiniteRelationalCoherentEPPAInCanonicalUniverses` returns a finite genuine original-relational [`Structure.IsCoherentEPPAWitness`](https://github.com/shulda/lean_all_those_eppa_classes/blob/d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d/AllThoseEPPA/EPPA.lean). The proof includes both the positive coherent construction and necessity via explicit small obstruction gadgets.

**Exact logical condition:** `Subsingleton G ∨ (d.selfReverseEffective.Nonempty ∧ d.IsCongruenceSaturated)`. The positive `G=1` branch works even if `S=\varnothing`. `IsCongruenceSaturated` requires **all** good congruence orbits to be complete, not just one.

**Universe packaging:** The class predicate quantifies finite input types at `Type` (universe zero) and allows different natural witness universes in the `G=1` and `G\ne1` branches. This is a formal representation choice, not an additional algebraic condition; mathematically any finite set can be represented in a small finite universe.

## Theorem D — semi-coherent EP, DLF and their classification

**Statement.** The following are equivalent for the given finite datum:

1. The original finite class has the **unrestricted semi-coherent extension property**: a cofinal choice of finite pairs `(A,H)` with `H\le\operatorname{Aut}(A)`, closed under suitable relative finite extensions that embed `H` injectively and equivariantly into the next group, and extend *every* partial automorphism of the prescribed finite overstructure in that same group.
2. There exists a countable ultrahomogeneous original `E,R_c` structure `M` with **full age** `\mathcal K(G,s,\phi)` and a dense locally finite subgroup of its **actual** `\operatorname{Aut}(M)`.
3. `G=1`, or `S` contains **at least one** entire affine-congruence orbit:
   `\exists g\in S\ \forall a\in G\colon a\star g\in S`.

**Exact Lean results:** [`RawDatum.finiteRelationalSemiCoherentEP_iff_relationalDLF`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/NativeRelationalSemiCoherentConverse.lean), [`RawDatum.countableRelationalHomogeneousDLF_iff`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/DLFRelationalClassification.lean), and the unrestricted raw classification [`RawDatum.finiteRawSemiCoherentEP_iff`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/DLFUnrestrictedSemiCoherentClassification.lean).

The [literal relational DLF predicate](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/DLFRelationalClassification.lean) explicitly requires **countable carrier, induced copies of every finite age object, extension of every finite partial map, and a subgroup dense by finite restrictions and locally finite in the finitely generated subgroup sense**. It is not the existence of some abstract locally finite group unrelated to automorphisms. The native semi-coherent family does **not** assume local involution safety.

**Important distinction:** This proves existence of such a countable homogeneous `M`, not a named theorem asserting its identity with a separately constructed Fraïssé limit. The latter identification follows from ordinary Fraïssé uniqueness *outside this Lean development*. The proof of the equivalence for **this class** is internal to Lean; no general Sági equivalence is assumed.

## Theorem E — strict separation

**Statement.** There is a concrete finite datum with `G=C_4`, `s=\mathrm{id}` and a five-element raw alphabet such that `S=\{0,1,2\}`. Its congruence orbits are `\{0,2\}` and `\{1,3\}`, so it has ordinary EPPA, unrestricted semi-coherent EP and DLF, **but not coherent EPPA**.

**Exact Lean results:** [`FourColourSeparation.c4Datum`, `hasCompleteGoodOrbit`, `notCongruenceSaturated`, `notRelationalCoherentEPPA`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourDLFNotCoherent.lean) and [`FourColourSeparation.semiCoherentDLFNotCoherent`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Examples/FourColourSemiCoherentSeparation.lean). The last theorem uses raw semi-coherent EP; the previously proved native raw↔relational equivalence transfers it to the same original-relational class. See the [example page](Four-colour-group-example.md).

## Reading the type, not only the name

[`RawDatum`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Algebra/RawDatum.lean), [`IsRectangleStructure`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/Language.lean), [`HasFiniteRelationalStrongSAP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/FiniteRelationalStrongSAP.lean), [`HasFiniteRelationalCoherentEPPAInCanonicalUniverses`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/FiniteCanonicalUniverseCoherentClassification.lean), [`HasFiniteRelationalSemiCoherentEP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/NativeRelationalSemiCoherentEP.lean), and [`HasCountableRelationalHomogeneousDLF`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/DLFRelationalClassification.lean) are part of the mathematical assertions, not implementation details to be ignored. Their meanings are audited explicitly on the [Adversarial audit](Adversarial-audit.md) page.
