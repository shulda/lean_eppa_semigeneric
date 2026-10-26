# The exact mathematical definitions in Lean

This page compares the mathematical data and structures with the actual Lean predicates. For main results in readable form, see [Main theorems](Main-theorems.md).

## 1. Raw data $(G,s,C,*,\phi)$

- $G$ is a group, not assumed abelian.
- An **affine anti-involution** is a map $s:G\to G$ such that $s^2=\mathrm{id}$ and, writing $t=s(1)$,
  $s(xy)=s(y)t^{-1}s(x)$ for all $x,y$. It is **not** assumed that $t=1$.
- $C$ is an alphabet with involution `*` and an onto map $\phi:C\to G$ with $\phi(c^*)=s(\phi(c))$.
- The theorem classifications assume $G,C$ finite. $C$ is automatically nonempty because the nonempty group $G$ is a quotient of it.

Sources: [`AffineAntiInvolution`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Algebra/AffineReversal.lean) and [`RawDatum`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Algebra/RawDatum.lean).

## 2. The original binary rectangle language

The Lean language [`rectangleLanguage C`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/Language.lean) has precisely one binary symbol $E$ and one binary symbol $R_c$ for each $c\in C$, with **no functions**.

A structure `A` belongs to $\mathcal K(G,s,\phi)$ precisely when:

- (R1) $E$ is an equivalence relation; its classes are *parts*.
- (R2) Exactly one raw colour `c` labels each **ordered** cross-part pair, none labels an intra-part pair, and $R_c(x,y)\iff R_{c^*}(y,x)$.
- (R3) Whenever `x_0 E x_1`, `y_0 E y_1` and the raw colours of all four edges are `c_{ij}`, their effective colours satisfy
  $\phi(c_{00})^{-1}\phi(c_{01})=\phi(c_{10})^{-1}\phi(c_{11})$.

The Lean predicate is [`IsRectangleStructure d A`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/Language.lean). Unlike the printed statement, the formal `rectangle` field does not impose explicit inequalities $x_0\ne x_1$ and $y_0\ne y_1$. This is *not a stronger constraint*: under (R2), coinciding vertices turn the displacement identity into a tautology. The four actual cross-pair colour hypotheses already exclude rectangles within one $E$-part.

The convenience presentation [`RawRectanglePresentation`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/RawPresentation.lean) encodes cross-pair colours by a function $V\times V\to\mathrm{Option}(C)$, with `none` exactly for $E$-pairs. It is **not a reduct** dropping raw relations: [`IsRectangleStructure.toRawPresentation_toStructure_eq`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/RelationalRoundtripEquality.lean) proves literal equality of the recovered original relation structure, symbol by symbol.

## 3. Congruence orbits and good colours

Let
$S=\{g\in G:\exists c\in C,\ \phi(c)=g\ \wedge\ c^*=c\}.$

The source is [`RawDatum.selfReverseEffective`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Algebra/RawDatum.lean). This set is contained in $\mathrm{Fix}(s)$, but $S$ need **not** equal the entire fixed-point set: a fibre can contain only reversal-paired colours.

The [congruence action](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Algebra/CongruenceAction.lean) on $\mathrm{Fix}(s)$ is
$a\star g = a\,g\,s(1)^{-1}s(a).$
The formalization proves that this preserves the fixed locus and is an actual group action, including for shifted affine anti-involutions.

There are two **different** requirements:

- [`IsCongruenceSaturated`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Algebra/CongruenceAction.lean): for **every** $g\in S$ and $a\in G$, $a\star g\in S$. Equivalently, $S$ is a union of whole orbits. Along with $S\ne\varnothing$, this characterizes **coherent EPPA** when $G$ is nontrivial.
- [`HasCompleteGoodOrbit`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Algebra/CongruenceAction.lean): **some** $g\in S$ satisfies $a\star g\in S$ for **every** `a`. This weaker condition characterizes **semi-coherent EP and DLF** when $G$ is nontrivial.

The alternative $G=1$ is essential in **both** classifications and needs no $S\ne\varnothing$ assumption.

## 4. Genuine embeddings and strong squares

An original-language induced embedding is a typed `AllThoseEPPA.Structure.Embedding` with the *identity* language action [`rectangleTrivialAction`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/RawTypedEPPA.lean). It is injective and preserves **and reflects** $E$ and each ordered $R_c$; it cannot merely preserve effective $G$-colours.

[`StrongSquare`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/StrongSquare.lean) records three obligations: commutativity over the specified old base, exactly the intended intersection of images, and joint surjectivity of the two target maps. The latter is stronger than the usual definition of SAP.

## 5. EPPA and coherent EPPA

For an embedding $i:A\hookrightarrow B$, the upstream typed [`IsEPPAWitness`](https://github.com/shulda/lean_all_those_eppa_classes/blob/d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d/AllThoseEPPA/EPPA.lean) asserts that **every** partial automorphism `p` of `A` extends along the same `i` to a **total** automorphism of `B`.

The upstream [`IsCoherentEPPAWitness`](https://github.com/shulda/lean_all_those_eppa_classes/blob/d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d/AllThoseEPPA/EPPA.lean) asserts the existence of one function assigning automorphisms to *all* partial automorphisms, respecting equivalent partial maps and the exact compatible-triple composition law. In particular, the coherent theorem is not merely separate homomorphic lifts of chosen automorphism subgroups.

## 6. Semi-coherence and actual DLF

The **unrestricted** [`RawDatum.HasFiniteRelationalSemiCoherentEP`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Bridge/NativeRelationalSemiCoherentEP.lean) selects a cofinal family of finite original-language pairs $(A,H)$ with $H\le\operatorname{Aut}(A)$. It demands:

- finite selected extensions over every given finite original-relational overstructure;
- an **injective** homomorphism $H\hookrightarrow K$ respecting old vertices;
- extensions of **all** finite original-language partial automorphisms of the overstructure by elements of the *same* selected finite group `K`.

The family is **not** assumed safe for cross-part involutions. Safety is an internal technique for constructing a cofinal family in the positive proof, not an additional definition of the target.

[`RawDatum.HasCountableRelationalHomogeneousDLF`](https://github.com/shulda/lean_eppa_semigeneric/blob/df21cfa98a668e1a95dceb73ce83d852336e6842/SemigenericEPPA/Structure/DLFRelationalClassification.lean) has a single genuinely original-relational countable carrier `X` and requires: induced copies of all finite age objects; extension of every finite injective partial map to a genuine full automorphism of `X`; and a subgroup $L\le\operatorname{Aut}(X)$ which is dense on finite pointwise restrictions and locally finite (all finitely generated subgroups are finite).

For the precise comparison with the manuscript's Fraïssé-limit formulation, see [Adversarial audit](Adversarial-audit.md).
