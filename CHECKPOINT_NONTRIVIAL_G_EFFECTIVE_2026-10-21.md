# Semigeneric EPPA Lean — positive nontrivial-G checkpoint (2026-10-21)

**Authority:** merged public `main` with green complete GitHub Actions
(build + allowed-axiom audit), NOT previous chat summaries. Check the
open PR CI before treating anything below labelled "submitted" as
proved. This checkpoint concerns the original, non-recentred affine
anti-involution on an arbitrary nonabelian group G.

## Completed upstream results

- Unconditional ordinary EPPA for finite original R1–R3 rectangle
  structures, including original-language typed upstream witnesses.
- **G=1:** complete finite original-language coherent EPPA, including
  the genuine partial-automorphism groupoid and typed conversion
  (PR #228 and its certified prerequisites).
- **Necessary coherent criterion for nontrivial G:** if the whole
  finite class has coherent EPPA, then the good self-reversing effective
  set is nonempty and globally congruence-saturated (PR #246).
  The 2+1 and 3+1 obstruction gadgets are certified in the typed
  relational setting. This is NOT the positive sufficiency theorem.
- Affine, noncommutative multiplier cocycles and good-colour
  congruence-orbit transport, with NO assumption `s(1)=1`.

## Fixed effective witness and genuine selected-group H actions

The following are verified/merged as of this checkpoint:

- #269, #270: Every effective old E/F geometry admits a
  constant-reversal-fixed skeleton gauge presentation, with a
  literal induced old embedding into its two-layer valuation carrier.
- #279: Fix `M=|A|!` and an old injection `j:A→Fin M` BEFORE any
  selected induced S or H. Every E-preserving H-action on S extends
  strictly to the SAME full auxiliary old-label carrier
  `(A/E)×Fin M`, preserving old selected vertices and moving first
  coordinates by an induced iota; unoccupied classes are fixed.
  This auxiliary action need NOT preserve old F outside S.
- #280, #284: One finite factorial indexed gauge Q over the fixed
  carrier, with skeleton a genuinely fixed good colour g0,
  normalised diagonal rows, and literal old E/F induced embedding
  is constructed independently of S/H. Includes the empty-A case.
- #281, #287: The genuine `Quotient B.part` is equivalent to the
  original index sort I; gauge reindexing along this equivalence
  preserves E/F, skeleton constants and diagonal normalisation.
- #272, #271: Canonical S-dependent but H-INDEPENDENT reference gauge
  on visited/unvisited indices, and exact whole-old-vertex transport
  for its strict coboundary H-action.
- #273, #274/#277/#278: Restrict a gauge to the TRUE selected
  subtype S; genuine old H E/F invariance solely on S produces
  strict noncommutative H-multipliers on ALL old index pairs,
  including diagonals and unused-index neutral defaults.
  Combined with the selected-reference coboundary, this builds
  a strict H→Perm of the whole two-layer effective witness.
  In the final relative factorial API (#288) all auxiliary
  group/index actions and multiplier/reference hypotheses are
  constructed, not supplied.
- #283: The factorial auxiliary action is an E/F automorphism on
  the embedded selected image old(S), even though outside-S colours
  may change; this is the exact hypothesis for the multiplier step.
- #285: The constant-skeleton gauge recoding retains the selected
  old E/F invariance, without requiring F preservation elsewhere.
- #291: The ACTUAL reference-indexed witness H action transports
  original old-label and old-class indices literally; it lifts
  equivariant Option-valued old projections and ensures any cross
  pair swapped across distinct original E-indices must be in
  occupied indices when iota fixes unoccupied ones.

## Raw flipped-edge safety: precise case split

- The algebraic affine common-middle congruence law is certified
  for arbitrary nonabelian G, nontrivial affine shift s(1), and all
  group elements h (not just involutions).
- #286: Actual swapped two-layer witness edge with the SAME original
  E-index is certified good under global congruence saturation.
- The DIFFERENT-original-E-index case needs an equivariant partial
  projection onto genuine selected old vertices and the actual
  common-middle relation for the genuinely swapped projected old
  pair. Existing abstract ingredients include the copied-fibre
  projection, occupied-only swapped-pair lemma, exact old raw
  reversal and congruence-orbit transfer.

## Submitted / not yet counted as verified in main

- **#289:** Real swapped witness F and a genuinely swapped projected
  old F share the precise noncommutative middle `g0⁻¹ M_h(i,j)`;
  then saturation transfers old good colour. Recompiling after a
  corrected multiplication associativity proof.
- **#290:** Arbitrary quotient-indexed gauge old zero-section is an
  injective induced E/F embedding, independent of being definitionally
  the canonical quotient gauge. Recompiling after old-part skeleton
  rewriting correction.
- **#292:** Every different-old-index swapped valuation pair projects
  to an actual swapped old selected cross-E pair from occupied
  equivariant Option projections.
- **#293:** Stronger fixed-quantifier-order factorial relative
  H-action, accepting ONE prechosen quotient-indexed gauge R and
  its literal old embedding before S/H. The previous #288 version
  existentially returned an R after S/H; the stronger API is needed
  for one common coherent witness.

Before merging these PRs, check GitHub Actions for the exact head
SHA (not merely the last green run on an older commit).

## Remaining mathematical objectives (not claimed complete)

1. Combine #293 with the fixed factorial base (#284) and actual
   quotient reindexing (#287). Fix the full effective witness
   skeleton K and the old E/F embedding BEFORE `∀S,∀H`, with
   finite carrier whenever A and G are finite.
2. Instantiate the DIFFERENT-index projected-swap geometry
   (#291, #292, replicated occupied projections) with the precise
   common-middle algebra (#289). Combine with the already certified
   SAME-index safety (#286) to prove **all** flipped witness
   cross-edges admit a self-reversing raw effective representative.
3. Choose ONE raw baseline/cover independently of S/H; apply
   the certified finite-group raw-colour orbit lift uniformly
   to each selected H-action, preserving the literal old raw
   colours and the strict group law.
4. Reuse the G=1 certified coherent groupoid and original-language
   typed converter to finish POSITIVE nontrivial-G coherent EPPA.
5. Independently formalize the relative dense locally finite
   (DLF) criterion (requiring only ONE complete good congruence
   orbit, not global saturation), and complete the unrestricted
   finite SAP / amalgamation application.

**Do not collapse these gates into a claim of coherent EPPA for
nontrivial G until a final original-language upstream typed theorem,
on a common finite witness with allowed axiom audit, is in main.**
