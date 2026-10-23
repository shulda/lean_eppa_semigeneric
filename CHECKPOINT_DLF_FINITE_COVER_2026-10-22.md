# DLF finite-cover formalisation: authoritative handoff (2026-10-22)

**Scope:** The `lean_eppa_semigeneric` repository. This file is a forward-looking
technical checkpoint, NOT proof that DLF has been formalised.

## Established and audited on main

The positive coherent EPPA construction is on main via PR #333, and the
full iff classification (finite original R1--R3 relational class, as well
as the functional raw version) via PR #334. Clean nontrivial-G iff API
is additionally on main via PR #340. Main after #340:
`2b0f35675f205641851e9ddb90ec00c4a3a8d9b9`, green full Lean build
and allowed-axiom audit. The classification is:

`G = 1 OR (selfReverseEffective.Nonempty AND IsCongruenceSaturated)`.

Trivial/nontrivial explicit witness universes are deliberately kept
separate in the final iff API. Never claim this gives a DLF subgroup.

## DLF mathematical target

`G = 1 OR RawDatum.HasCompleteGoodOrbit`, where
`HasCompleteGoodOrbit` means **one complete affine congruence orbit**
is contained in the good raw-colour fibres. It does NOT mean all good
fibres are globally saturated. The affine action is
`congruence(s,a,g)=a*g*(s 1)⁻¹*s(a)`, even when `s 1 != 1`.

The human audit in private `shulda/generalized_semigeneric` provides:
- `paper_formalization_prep/AUDIT_SAFE_RELATIVE_V0_5.md`
- `paper_formalization_prep/AUDIT_RELATIVE_COVER_POSITIVE_DLF_2026-10-16.md`
- `paper_formalization_prep/AUDIT_NEGATIVE_DLF_COHERENT_G1_2026-10-16.md`
- the formalisation-target v0.8 TeX.

Those are human-audited sources, not Lean-certified lemmas.

## Active local algebra and graph PRs

Always check the **latest head SHA** and full workflow conclusion before
claiming or merging:
- #335 and #342: one complete good congruence orbit controls the
  same-old-index swapped witness colours, and colour-specific
  complete-orbit safety is invariant under affine congruence.
  Both source modules passed CI independently; #345 consolidates them.
- #336: literal left cosets for arbitrary subgroup H≤Q (not necessarily
  normal); strict Q action, fixed coset iff q⁻¹tq∈H.
  Original fixed-import commit 829492f7 had green CI. Later branch
  was synchronised with main; inspect its new CI.
- #338: graph with 3 vertex layers and 2 edge layers, actual strict Q
  permutations, edge endpoint equivariance, no inverted edges, free
  edges for g≠1 and free vertices for t not conjugate into H.
  Its inl-coset simplification was undergoing Lean correction.
- #339: explicit graph paths to a free-layer hub and no loops; depends
  on #338.
- #341: finite F₂ graph edge-boundary augmentation is zero, and a
  singleton vertex has augmentation one. Source head 7afd1215
  received green full CI/axiom audit; may still need consolidation
  against newer main.
- #343: every invariant F₂-valued coefficient family for a
  fixedpoint-free order-two permutation has total sum zero; CI pending.
- #344: inverse-indexed, noncommutative, strict Q-action on the F₂
  edge-chain coefficient functions; CI pending.

The first attempt to compile PR #336 lacked the permutation-group
instance; `Mathlib.Algebra.Group.End` fixed that. Follow-up graph
problems were definitional reductions of `Equiv.sumCongr`; no
mathematical counterexample was found. Some current CI jobs may take
several minutes. Do not infer success from an earlier green SHA.

## Graph / parity cover to formalise next

For finite Q and H≤Q define:
- `V = Q/H ⊕ (Bool × Q)`, where the Bool layers are the two regular
  Q-sets;
- `E = Q ⊕ (Q × Q)`, with endpoints
  `q ↦ (qH, (false,q))` and
  `(q,r) ↦ ((false,q),(true,r))`.
  Left Q translation acts on all vertices/edges. Each graph edge
  connects DIFFERENT invariant layers, so edge inversion is impossible.
- `C₁=E→ZMod 2`, `C₀=V→ZMod 2`, boundary
  `∂e = δ_(source e) + δ_(target e)`.
- `Q` acts on functions by
  `(q·c)(e) = c((rho_E(q⁻¹))e)`.
- Form the finite semidirect group with pairs `(q,c)` satisfying
  `∂c = δ_(x0) + δ_(q x0)`, where `x0=H` in the coset layer.
  Multiplication is `(q,c)(r,d)=(qr,c+q·d)`.
  Connectivity supplies a chain connecting `x0` to `q x0`,
  projection onto Q is onto, kernel is the cycle space, and the
  map `h ↦ (h,0)` on H is a homomorphic section.

### Direct parity proof to consider INSTEAD of quotient multigraphs

For an involution `t∈Q` not conjugate into H, its vertex and edge
actions are fixedpoint-free. Assume `c` is t-invariant and
`∂c=δ_(x0)+δ_(t x0)`. Choose one representative from each
t-vertex orbit via a finite linear order: a selector `χ:V→ZMod 2`
with `χ(v)+χ(tv)=1`.

Evaluate the boundary against χ:
`Σ_v χ(v)∂c(v) = Σ_e f(e)`,
`f(e)=c(e)*(χ(source e)+χ(target e))`.
Endpoint equivariance, c-invariance and characteristic two imply
`f(te)=f(e)` (the two selector terms each toggle, so their sum is
unchanged). Since t has no fixed **edge**, the invariant F₂ sum
`Σ_e f(e)` is zero; #343 is precisely this needed pairing lemma.

But evaluation of `δ_(x0)+δ_(t x0)` is 1 because χ toggles.
Contradiction. This avoids an explicit quotient multigraph and
quotient-chain descent, while requiring exactly the same audited
edge-free and vertex-free hypotheses. This simplification has NOT
yet been checked in Lean end-to-end.

## Subsequent mathematical gates

1. Build and certify the split finite relative group cover above.
2. Add one new E-class indexed by its regular action, with constant
   raw cross-colours to the old structure; prove faithful realisation
   of the cover group in the original R1--R3 language.
3. Prove relative safe-group EPPA from a single complete good orbit,
   with H action on A but no assumed H action on prescribed larger B.
   Preserve the audited phase distinction: H-regular phase outside
   A, trivial phase on A. Never assert that an arbitrary swapped
   clone forces h²=1.
4. Combine relative safe EPPA and finite cover into a cofinal
   semi-coherent family; prove necessity via delta-profile forcing,
   the orbit killer, and parity.
5. Formalise the optional countable Fraïssé-limit / Sági bridge
   `semi-coherent EP ↔ DLF` after the finite statement is complete.
6. Independently audit SAP / Fraïssé existence if the final DLF
   statement needs it. Do not infer SAP from coherent EPPA.

**Method:** prefer small CI-certified Lean modules, no `sorry`,
`admit`, or new custom axioms. If CI crashes or turns end without an
answer, GitHub source and exact CI head SHA are authoritative.


## 2026-10-23 checkpoint — relative finite cover is in construction

This update supersedes the *active-PR status* above, but not the mathematical
definitions or the relative safety cautions. Status is based on the exact CI
heads observed in the 2026-10-23 conversation; recheck CI before merging.

### Verified and merged into main

- Main `f0b7bc92cd55181be3f26a92e1736b88f89e995e`:
  exact seven source modules from independently green #350–#356, green
  combined full build/axiom audit, merged as PR #358. This includes
  direct quotient-free fixedpoint-free graph involution parity, the
  ACTUAL Q/H graph application, the group Q⋉F₂^E, additive/equivariant
  boundary, the prescribed boundary subgroup, and the square-one
  invariant-chain obstruction.
- Main `95630713b82f7b0f53565cbcfe2c1419a36154cd`:
  PR #359 proves the ACTUAL prescribed-boundary subgroup
  `relativeBoundaryCover H` cannot contain a square-one element
  projecting to any t outside all conjugates of H. Green full
  build/axiom audit. This is the central no-bad-involution statement.

### Individually green results or work in integration

- PR #357: `DLFGraphPathChainBoundary.lean` proved that explicit
  graph connectivity supplies a chain with boundary δ_x+δ_y.
  Final checked head `f0e9e220` green after eliminating ambiguous
  endpoint metavariables.
- PR #361: `DLFChainSemidirectFinite.lean` certifies the semidirect
  group's finite carrier and all its finite subgroups. Final head
  `4affa5bc` green. Old PR was retargeted to main but had an import
  conflict; clean source replay is PR #364, CI pending.
- PR #360: `DLFRelativeCoverSurjectiveSplit.lean` intends the
  surjective projection from the genuine relative boundary subgroup
  onto Q and an injective homomorphic section of H. First CI flagged
  a coset-vertex equality elaboration at line 68. Corrected head
  `05fa6bde` sent to CI; **NOT yet certified** at time of writing.
  This is the next mathematical closure gate.

### Faithful R1–R3 realization and relative safe EPPA

- PR #362: adding one entire new equivalence class with constant
  new-to-old raw colours, and proving the exact R1–R3 rectangle
  axioms. First CI encountered recursive simplification in the
  raw-reversal proof, replaced by explicit four cases on branch
  `formalize/dlf-constant-new-e-class` (head `495f5727`).
  CI pending.
- PR #363: strict action T on old V and on one new regular T-class,
  preserving all E/raw colours and faithful even if old action is
  not faithful. Stacked on #362; parent reversal fix was propagated
  to the stacked branch (head `45abc588`); CI pending.
- PR #365: land that regular action inside literal
  `binaryRawAutSubgroup` of the genuine enlarged raw presentation,
  with strict homomorphism and injection, stacked on #363.
  Parent reversal fix propagated (head `27412820`); CI pending.
- PR #366: independent relative regular-phase H-action on
  V×H, trivial phase on an invariant old subset S and left H
  phase elsewhere. Proves that a swapped outside-S pair forces
  h²=1, **not** on S. This preserves the corrected human proof,
  where order-four h can swap old-sector pairs. CI pending.

### Next mathematical work

1. Finish CI and merge #360 and #364 on the canonical main with
   no separate H-dependent choices. This closes the algebraic
   relative cover: a finite group with surjection to Q, split
   original H, and no bad involution lifts.
2. Complete #362/#363/#365 to realize the cover group faithfully as
   actual E- and every R_c-preserving permutations after adjoining
   exactly one new E-class.
3. Formalize the **relative safe H-action extension for A⊆B** under
   one complete good congruence orbit, starting from #366, the
   existing factorial effective H-action and safe prescribed raw
   colour/baseline APIs. The phase action over B\\A must be regular;
   old A sector must have trivial phase. Do NOT require H to act
   on B before the extension.
4. From relative safe EPPA + relative cover, construct cofinal
   finite safe pairs and the semi-coherent extension property.
   Formalize the negative orbit-killer/delta-profile obstruction.
5. Only then formalize the Fraïssé-limit/Sági DLF bridge and the
   resulting iff. Ordinary EPPA and coherent EPPA do not entail
   this stronger/separate theorem.

One critical invariance: on real old selected pairs, a reversed
H-orbit has a genuinely self-reversing raw colour; on new phase
orbits the order-two condition and one complete good congruence
orbit supply raw flip-safety. Do not replace this with global
saturation or assume all h flipping a pair are involutions.
