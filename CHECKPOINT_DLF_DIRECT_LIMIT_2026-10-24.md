# DLF direct-limit handoff — 2026-10-24

## Authority and strict status convention

Authoritative repository: `shulda/lean_eppa_semigeneric`; check **exact
head SHA and the completed GitHub Actions full Lean build/axiom audit**.
No `sorry`/`admit` or additional custom axioms. Distinguish finished
independent source proofs from a branch still waiting for its combined CI.

The private `shulda/generalized_semigeneric` is the human paper source.
The complete finite original-language coherent EPPA classification is
already certified (`Bridge/FiniteCanonicalUniverseCoherentClassification`).
DLF is distinct and needs strictly less positive good-colour structure:
ONE complete affine congruence orbit, not global saturation.

## Already certified finite DLF spine in main

- `DLFFiniteSafeGroupEPPAExtension.lean`: actual **finite**
  safe-group EPPA under `HasCompleteGoodOrbit`, with exact original E
  and ordered `R_c` relations. Returns one finite safe K with selected
  subgroup action and all partial-map connectors on the same witness.
- `DLFFiniteSafePairEmbeddings.lean`: finite pairs (A,H≤Aut_raw(A)),
  genuine induced injective vertex maps and injective strict equivariant
  H→K homomorphisms.
- `DLFFiniteSafePairOneStep.lean`: take S=UNIV A, produce one safe
  successor pair and extend all partial automorphisms of old A.
- `DLFSafePairTower.lean`: finite towers and exact n→m transition maps.
- `DLFSafePairOverAgeExtension.lean`, clean integrated #467:
  **crucial stronger successor:** for any induced A→P with P an arbitrary
  finite age superstructure (NOT assumed to carry H action), produce
  a safe (B,K) containing ALL of P, injectively/strictly extending H,
  and realizing every partial raw automorphism of P inside ONE K.
- `DLFInducedRawEffectiveReduct.lean`: exact effective colour and E
  preservation on arbitrary induced original-language embeddings,
  no fake raw-colour gauge equality.
- `DLFPairSwapEvenGroup.lean`: two-cycle in a finite action forces
  an even finite group order and some genuine nontrivial involution.
- `DLFDenseLocallyFiniteTowerCriterion.lean` and related algebra files:
  a verified abstract criterion for density by finite restrictions
  and local finiteness of a covering ascending chain of finite groups.

**Important**: these do NOT alone give a countable Fraïssé limit,
a dense subgroup of its Aut, or the DLF iff.

## 2026-10-24 follow-up finite tower compatibility

- `DLFSafePairTowerCoherence.lean`: exact successor identities for
  both vertex and finite-group transition maps, certified source
  `cbdf0d8` on #466 with green CI run 40084101597; clean #475 merged
  into main as `7e641796`.
- `DLFSafePairTowerTransitivity.lean`: strict n→k =
  (m→k) ∘ (n→m), all n≤m≤k, for both vertex and group maps,
  certified source blob `2f9471e` on #468 and clean #476 with
  SUCCESS run 40085141116. New clean current-main replay is #480.
  **Check its combined CI before merging.**

## In-progress genuine directed-limit modules: NOT certified yet

All depend on the correct three-stage cocycle.

- #469, `DLFSafePairTowerDirectedLimits.lean`: instantiate
  `DirectedSystem` for actual vertex embeddings and group
  homomorphisms, then form quotient `VertexLimit`, `GroupLimit`,
  with injective old-stage inclusions.
  Initial CI failed because a raw function type has no `FunLike`
  instance in Mathlib's general DirectLimit. Corrected ALL dependent
  branches to use **`V i ↪ V j` Function.Embedding** as the vertex
  transition, not a bare `V i → V j`. Recheck corrected #469 CI.
- #470: genuine group-limit local finiteness via ascending finite
  images of each acting H_n; full CI pending.
- #471: quotient `limitPart` and literal ordered Option C
  `limitColour`, exact agreement on finite stages; CI pending.
- #474: E equivalence, none iff same E, and literal reverse
  raw colours on the vertex limit; CI pending.
- #477: four-vertex common finite-stage representatives and
  complete original R1--R3 rectangle on vertex limit; CI pending.
- #472: canonical well-defined group-limit-on-vertex-limit
  binary evaluation by Mathlib `DirectLimit.map₂`, with strict
  equivariance providing the compatibility condition; CI pending.
- #473: action unit globally and multiplication on same-stage
  triples; CI pending.
- #479: multiplication on arbitrary group/group/vertex quotient
  triples and a real `MulAction` instance; CI pending.
- #478: finite subset F of vertex colimit has representatives
  in ONE finite stage, by Finset induction; CI pending.

The PRs are stacked in their stated dependencies: source blobs need
careful clean replay onto current main after individual CI passes,
since concurrent root imports cause GitHub merge conflicts. Never
merge a failing or currently unverified head just because its
mathematical statement looks plausible.

## Next mathematical tasks

1. Certify/directly fix #469's corrected `Function.Embedding`
   transitions, then close the directed-limit branch stack.
2. Certify the full original raw rectangle on the quotient, group
   action, local finiteness, finite support, and faithful embedding
   of group colimit into `Aut_raw(VertexLimit)`. Show the action
   preserves BOTH E and every ordered raw colour, not merely F.
3. **Existence of a suitable age-cofinal finite safe-pair tower:**
   construct one countable tower using the stronger
   `exists_safeExtension_overRawEmbedding`, unrestricted finite SAP
   and a countable enumeration of the finite age extension
   requirements. The existing certified SAP is for arbitrary
   literal ONE-POINT diagrams; the full finite iteration is an
   additional formalization gate.
4. **Fraïssé extension property/density:** any finite set F of the
   limit and its image under a global automorphism lie in a common
   stage. The induced partial map is extended at the NEXT stage
   by the certified K-connector property. Thus the image of the
   locally finite limit group approximates every limit
   automorphism on any finite set.
5. Complete negative DLF classification from finite
   incomplete-orbit/delta-profile gadgets, parity and local
   involution-safety. The final countable necessity is NOT yet
   a Lean theorem.
6. Handle the G=1 branch separately using certified coherent EPPA
   if `HasCompleteGoodOrbit` is not automatic from raw reversal.

**Mathematical invariant**: safe means each square-one group element
reversing an E-cross pair has a complete GOOD congruence orbit.
An element swapping two points need NOT have order two. Do not
replace this by global good-set saturation or silently assume
arbitrary age superstructures carry an H action.
