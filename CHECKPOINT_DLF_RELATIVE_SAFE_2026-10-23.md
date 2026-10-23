# DLF relative safe EPPA: 2026-10-23 handoff and proof gates

## Source of truth

Repository: `shulda/lean_eppa_semigeneric`. All statuses below refer
to GitHub source and exact GitHub Actions runs; an open PR or
an assistant-written proof is NOT automatically a certified result.
Every merge requires green full Lean build and allowed-axiom audit
on the exact head. No `sorry`, `admit` or new custom axioms.

## Certified theorem landmarks

- Full coherent EPPA classification in the original relational R1–R3
  language is green on main (#333, #334, #340):
  G=1 OR (good self-reversing effective set is nonempty and globally
  affine-congruence saturated). This is **not** the DLF theorem.
- Finite involution-killing Q/H cover group: the actual finite
  `relativeBoundaryCover H` with surjective projection to Q, strict
  injective split H-section, and no order-two element projecting
  outside every conjugate of H. Certified and on main (#368, #374).
- Faithful original-language raw realization of that cover by one
  additional regular E-class. The old R_c and E are literally
  preserved. Certified and on main (#374).
- Strict relative H-phase blow-up and two-sector flip-safety:
  phase is unchanged over H-invariant old A, regular outside A;
  swapped outside-A pairs imply h²=1, but swapped pairs inside A
  MAY arise from order-four elements. Original raw invariance is
  used on A, complete-good-orbit safety only for involutions
  outside A. Certified and on main (#376, #377).
- Affine complete-good-orbit algebra, the original Q/H free graph,
  F₂-chain/group cover and parity proofs are also on main.

At start of this handoff, main included
`9a2b59c5b2caded4e7297b4fee2272c9a58d4fac`
(merged #377). Re-check current HEAD before merging anything.

## Active safety bridge PRs (CI status MUST be rechecked)

- #375: conjugacy preserves local good-orbit safety of H involutions
  under exact Q E/F automorphisms; corrected import, exact green
  head `7c2b029...` in the previous cycle.
- #378: package that with the actual finite split cover: every
  upstairs involution acts safely on the old E/F geometry.
  CI first failed because the projected cover action definition
  lacked required Fintype graph instances; these were inserted,
  and then `noncomputable` was added for `relativeBoundaryCover`.
  Current branch `formalize/dlf-relative-cover-safe-involutions`.
- #379: adjoining a new constant-colour regular E-class preserves
  the original effective colour on old cross-E pairs, and swapped
  cross-E pairs of the enlarged sum action must be old-old.
  CI first found an Option case split using `hc` where `rfl`
  was required; fixed.
- #380: stacks the exact #378 and #379 bridges: all square-one
  elements in the faithfully realized finite cover are safe on
  actual swapped original-language cross-E pairs. NOT certified
  at time of this checkpoint.
- #377 is already merged: phase flip-safety with true old raw
  invariant colours and only involution-only orbit safety outside.

## Noninvariant prescribed raw colour work (new relative A⊆B gate)

The old B×{1} phase-one copy is **NOT H-invariant**. H originally
acts only on A⊆B, and regular phases move B\A out of the copy.
Do not assume H preserves raw colours on arbitrary B edges.
The correct orbit condition is: whenever an H-translate of an
old ordered B-cross-pair returns to an old ordered B-cross-pair,
the two prescribed raw colours agree.

- #381 defines `orbitSaturation rho S` and proves that exact
  return consistency suffices to extend colours from arbitrary S
  to a globally H-invariant colouring on the ambient set.
  First CI found two missing transported-membership proofs and
  an overly aggressive nested `map_mul` rewrite. Corrected on
  #381 and propagated through all stacked branches.
- #382 proves relative phase returns from outside A to B×{1}
  force h=1, and that actual original raw B-pair colours satisfy
  this return consistency using raw H invariance ONLY on A×A.
- #383 proves H-saturation of a reversal-stable S remains
  reversal-stable and an invariant colour extension preserves
  raw reversal on the whole H-saturation.
- #384 generalizes abstract raw orbit selection to noninvariant
  prescribed S: first saturate, then use the certified invariant
  subset raw orbit theorem. First CI was blocked by the forbidden
  placeholder keyword appearing only in a comment; corrected.
- #385 applies #384 to the actual directed effective cross-pair
  geometry, producing raw phi/reversal/H-invariant colours
  extending ALL old B raw colours from the noninvariant S.
  An accidental old-H-invariance parameter was explicitly
  deleted; only the correct return-consistency premise remains.

None of #378–#385 should be reported as proved until its
head's full CI/axiom audit passes; pending PRs are conditional
work, not evidence of the final DLF theorem.

## Next constructive target

1. Finish CI repairs and consolidate exact certified source modules.
2. Combine the actual relative effective factorial H-action over
   old A⊆B, the regular phase construction, #382's return
   consistency, and #385's noninvariant raw colour selection.
   This should yield the safe H raw group action on a finite
   witness for B, while preserving its entire old raw B zero section.
3. IMPORTANT: on that SAME witness, extend every individual
   partial isomorphism of B, using the independently certified
   ordinary effective and raw residual-cover extension machinery.
   This is the remaining **relative safe EPPA** theorem.
4. Combine relative safe EPPA with the certified split finite
   cover and faithful regular-class action to obtain a cofinal
   semi-coherent family. Retain faithful group embeddings and
   order-two safety after each step.
5. Separately formalize the negative DLF side: delta-profile
   forcing, orbit killer, and the odd-group contradiction.
6. Finally formalize the countable Fraïssé/Sági bridge from
   semi-coherent EP to a dense locally finite subgroup. Ordinary
   EPPA or coherent EPPA alone does not imply this bridge.

## Noncommutative / safety caveats

Always keep the affine action
`congruence(s,a,g)=a*g*(s 1)⁻¹*s(a)`. One complete good
orbit is weaker than global saturation. Group Q and H may be
nonabelian, H may be nonnormal. Never infer that an H-element
swapping an old-sector pair has order two. For outside-A
phase-swapped pairs, regular phase is exactly what forces h²=1.

Human mathematical proof audits remain in private
`shulda/generalized_semigeneric/paper_formalization_prep/`,
especially `AUDIT_SAFE_RELATIVE_V0_5.md` and
`AUDIT_RELATIVE_COVER_POSITIVE_DLF_2026-10-16.md`.
