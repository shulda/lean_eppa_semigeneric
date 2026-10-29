# v0.11 — part-preserving coherent EPPA and fixed-n multipartite tournaments

## The precise mathematical strengthening

The new human manuscript v0.11 strengthens `thm:coherent-g1`. For **any finite $A\in\mathcal K(1,\mathrm{id},\phi)$** with a finite involutive raw-colour alphabet, there are **one finite coherent EPPA witness** $B$ and an induced embedding $\psi:A\hookrightarrow B$ such that the induced map of nonempty $E$-classes is **bijective**:
$

A/E_A\longrightarrow B/E_B,\qquad [x]\longmapsto[\psi(x)].

$

This is stronger than merely $|A/E_A|=|B/E_B|$; it proves no new E-class appears, and none of the old classes merge. It is satisfied by the **existing witness construction**.

The proof's fixed effective carrier is
$

\bigl(A/E_A\bigr)\times\mathrm{Fin}(M),\qquad M=|A|!

$
(where the human proof uses a smaller lcm padding). The raw residual cover has vertices $(u,\eta)$ above this base, and its E-relation depends **only** on the first coordinate of $u$. Every E-class therefore has a representative among the embedded old vertices. In particular, for empty $A$ the quotient and witness are empty.

## Exact Lean declarations and logical dependencies

| Result | Certified file | Mathematical content |
| --- | --- | --- |
| The original cover uses precisely the old part-index quotient | [`GOneFactorialCarrier`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Valuations/GOneFixedEffectiveEPPAAndSafeActions.lean), [`RawCoverVertex`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Structure/RawCover.lean) | Fixed carrier, no new part indices |
| Every witness class meets the old copy | [`gOneJointRawPart_coveredByOld`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Bridge/GOnePartPreservation.lean) | $\forall z\in B\;\exists x\in A\;E_B(\psi x,z)$ |
| Canonical bijection on quotients | [`partQuotientMap_bijective_of_partCover`, `partQuotientEquivOfCover`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Structure/PartQuotientCover.lean) | Reflecting/preserving E plus part-surjectivity implies the desired equivalence |
| Coherence uses same actual embedding and exact functor | [`coherentTypedEPPA_of_exactRawFunctor_with_map`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Bridge/RawExactFunctorToTypedCoherent.lean) | Stronger wrapper; old API preserved |
| The strengthened $G=1$ theorem | [`finite_partPreservingTypedCoherentEPPA_witness`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Bridge/GOneTypedCoherentEPPA.lean) | One *typed coherent witness* plus exact E-quotient equivalence and its action on $[x]$ |
| At most n nonempty parts | [`HasAtMostNonemptyParts`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Bridge/BoundedPartsCoherentEPPA.lean) | An injection $A/E_A\hookrightarrow\mathrm{Fin}(n)$, not exactly n |
| Original-relational bounded-class coherent EPPA | [`finite_boundedPartsRelationalCoherentEPPA_witness`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Bridge/BoundedPartsCoherentEPPA.lean) | An arbitrary finite original $E,R_c$ member retains its n-bound and a coherent extension |
| Two orientation colours and definable E | [`twoOrientationGOneDatum`, `twoOrientation_part_iff_nonadjacent`, `finite_twoOrientationExpandedNPartiteCoherentEPPA`](https://github.com/shulda/lean_eppa_semigeneric/blob/main/SemigenericEPPA/Bridge/TwoColourPartiteCorollary.lean) | $G=1$, two opposite raw orientations, fixed n: **expanded** language coherent EPPA, and $E(x,y)\iff\neg(x\to y)\wedge\neg(y\to x)$ |

No new condition on n is needed for the bounded-class formalization: it holds for every natural $n$, including all $n\ge2$. Empty parts correspond to unused labels in $\mathrm{Fin}(n)$.

## Exact boundary: the one-arrow tournament language

The mathematical HJKS finite $n$-partite tournaments have **one directed edge relation**, with the partition not named in the language. Nonadjacency defines E, and the two-colour expansion is therefore definitional; the usual mathematical coherent EPPA corollary for fixed finite $n\ge2$ follows.

**A separate typed Lean theorem for this reduct has NOT yet been formalized.** To obtain it, the following genuinely new language-transport API would be needed:

1. Define the single-binary-relation directed-graph language $L_{\to}$, its finite $n$-partite model predicate, and the definitional expansion from arrow-only $A$ to the two-colour $E,R_c$ structure. Prove its exact inverse (reduct) on the intended class.
2. For both source and target structures, convert actual induced embeddings and **every** partial automorphism between $L_{\to}$ and expanded $E,R_c$, using definability of E by nonadjacency and $R_\mathrm{false}(x,y)\iff R_\mathrm{true}(y,x)$.
3. Prove that this conversion preserves mathlib/`AllThoseEPPA` `PartialEquiv.EqOnSource` (therefore `Equivalent`) and `CoherentTriple` exactly, with no shrinking source/target domains.
4. Transfer every full expanded-language automorphism to the arrow reduct, preserving identity and composition; convert the expanded `CoherentExtension` functor, not just individual EPPA extensions.
5. Package the resulting $L_{\to}$-typed `IsCoherentEPPAWitness` with the already-certified part bound.

Until these interfaces exist, the proof is a **fully verified expanded-language result**, and the one-arrow coherent EPPA claim is a valid **standard definitional consequence**, not a literally named Lean result. Do not conflate the two.

## Dense locally finite subgroups

The private v0.11 also deduces that the automorphism group of the fixed-n Fraïssé limit contains a dense locally finite subgroup, via coherent EPPA and the established mathematical semi-coherent/Sági correspondence. This note **does not** claim a new Lean proof of the general Sági implication or of a fixed-n homogeneous Fraïssé limit with DLF. That remains an external mathematical corollary, distinct from the now formally proved bounded-class EPPA statement.

## Verification and independent audit

The targeted [CI #40868624158](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40868624158) successfully compiled 1,343 dependencies and the top `TwoColourPartiteCorollary` module. **Full root-library verification and the allowed-axiom audit are tracked separately in the PR.** The independent statement crosswalk is [here in the public source](https://github.com/shulda/lean_eppa_semigeneric/blob/main/PART_PRESERVING_AUDIT_2026-10-29.md). No unpublished manuscript TeX or proofs are copied to the public repository.
