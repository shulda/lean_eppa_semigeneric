# DLF formalization audit — 25 October 2026

## Verified headline and exact Lean interpretation

Repository: `shulda/lean_eppa_semigeneric`.
The classification is stated in
[`SemigenericEPPA/Structure/DLFCompleteClassification.lean`](SemigenericEPPA/Structure/DLFCompleteClassification.lean)
as

```lean
RawDatum.countableHomogeneousDLF_iff :
  d.HasCountableHomogeneousDLF ↔
    Subsingleton G ∨ d.HasCompleteGoodOrbit
```

The final API source was independently tested by the **full Lean build
and allowed-axiom audit** on PR #545, exact head
`99bb61dc92d458208ce52bd8c0e2aba5c23d5de7`,
workflow run `40179812750` (SUCCESS). The negative integration
PR #544, exact head `9b22a94f14d0c6bf0d36dc26099434049894c51e`,
workflow run `40179553322` (SUCCESS), was merged beforehand.
Final iff integration was merged as commit
`2e08d98d6db153855c32b1aad940a61b2eabf463`.
Always separately inspect current main CI; an earlier PR success
does not substitute for a green later main SHA.

The predicate `HasCountableHomogeneousDLF` asserts the existence
of a carrier `X : Type (max u v)` and a complete original raw
`RawRectanglePresentation d X` satisfying, **on the same X**:

1. `Countable X`;
2. induced copies of every finite original raw R1–R3 rectangle on
   every canonical `Fin n`, including exact preservation/reflection
   of `E` and literal equality of every ordered `Option C` colour;
3. extension of every finite injective original-language partial
   isomorphism to an actual member of `M.fullRawAutGroup`;
4. a subgroup `L ≤ M.fullRawAutGroup` dense on exact finite
   pointwise restrictions and locally finite in the sense that
   every finitely generated subgroup is finite.

Universality on `Fin n` is equivalent to universality on
**arbitrary finite carriers** by the already certified
`RawRectanglePresentation.inducedFiniteAge_of_canonicalFinAge`.
The language is the original binary `E,R_c` language:
`RawRectanglePresentation.toStructure` gives the literal
relational object, and
`IsRectangleStructure.toRawPresentation_toStructure_eq`
proves exact round-trip equality from any original relational
R1–R3 structure. Nevertheless, the final DLF **named theorem**
is phrased using the functional raw presentation, not as a
separate top-level `AllThoseEPPA.Structure` predicate.

## Mathematical statement and manuscript cross-check

The corresponding manuscript result is
`paper_formalization_prep/group_valued_rectangles_formalization_v0_8.tex`,
Theorem `thm:main-intro(iii)` and `thm:semi`:
for finite `G`, finite involutive raw alphabet `C`,
surjective equivariant `phi:C↠G`, and affine anti-involution
`s`, the Fraïssé limit's full automorphism group has a dense
locally finite subgroup precisely when `G=1` or the good
effective set `S` contains **at least one complete congruence
orbit**. Here

```text
S = { g : G | ∃ c : C, phi c = g and reverse c = c }
congruence(s,a,g) = a * g * (s 1)⁻¹ * s(a).
```

The Lean predicate `GoodCompleteOrbitAt g` is
`∀ a, congruence d.s a g ∈ d.selfReverseEffective`,
and `HasCompleteGoodOrbit` existentially chooses such a `g`
(and certifies its own goodness). Crucially, this is **weaker**
than the global `IsCongruenceSaturated` condition in the
already-certified coherent EPPA classification. No commutativity
of G or unjustified `s(1)=1` recentering is used.

## Proof dependencies and audit points

**Positive, one complete good orbit.**
`RawDatum.exists_countableHomogeneousDLF_of_completeGoodOrbit`
builds a literal finite-safe-pair tower with exact induced
embeddings and strict finite subgroup homomorphisms; its true
vertex/group directed limit has full finite original raw age,
ultrahomogeneity, and a dense locally finite subgroup of
its actual `fullRawAutGroup`.
No HKN EPPA existence or Sági bridge is imported.

**Positive, G=1.**
`RawDatum.exists_countableHomogeneousDLF_of_subsingleton`
constructs the analogous witness with no complete good orbit
assumption, including the case where the raw palette has
no reversal-fixed colour. Genuine G=1 raw automorphism groups
are automatically locally involution-safe.

**Negative, G≠1.**
`RawRectanglePresentation.completeGoodOrbit_of_denseLocallyFinite`
uses the full original finite age and finite-partial-map
ultrahomogeneity. A swapped cross-E pair under a global
involution forces its whole congruence orbit good, because
relative three-point raw gadgets realize every affine
row multiplier. If the involution moves a pair within E,
a fresh clone and a singleton delta row force a cross-E swap.
Thus no nontrivial global involution exists without any
complete good orbit. Yet the full age provides a genuine
partial two-point transposition that extends to a full raw
automorphism with a literal two-cycle. Density and local
finiteness yield a nontrivial involution in a finite subgroup:
contradiction. The extension automorphism with the two-cycle
is *not* incorrectly assumed to have order two.

The negative proof directly uses `M.fullRawAutGroup`
and never replaces it with an effective-colour permutation
group. It requires no semicoherent finite action family.

## Still separate / not claimed formalized

- A *general* proof of Sági's equivalence between the finite
  semi-coherent extension property and DLF for all countable
  homogeneous finite-relational structures; and a direct
  named classification of the semi-coherent extension property.
  The manuscript gives a human proof, not yet the Lean theorem.
- An independent general finite SAP induction and stand-alone
  unconditional Fraïssé existence and uniqueness theorem for
  all data. The positive DLF branches construct the needed
  homogeneous limits directly **under the positive DLF
  conditions**. The final Lean DLF predicate is existential;
  uniqueness/isomorphism to an externally postulated Fraïssé
  limit is not a separate certified theorem.
- A separately exported *relational-typed* DLF iff API
  (rather than using the already certified exact raw/relational
  correspondence). This is an API/documentation enhancement,
  not a missing algebraic step in the proved raw theorem.
- The optional `G=C₄, S={0,1,2}` explicit separator as a
  single packaged example theorem and the manuscript's
  human-facing editorial cleanup.

## Verification discipline

Use the exact head SHA and completed SUCCESS of GitHub Actions
`Lean CI`; it runs the entire Lean project and the permitted
axiom audit (`propext`, `Classical.choice`, `Quot.sound`).
Individual PR proof descriptions are NOT independent proof
certificates. Do not use `sorry`, `admit`, or custom axioms.
