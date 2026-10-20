# G=1 coherent EPPA: verified raw theorem and final typed bridge

**Checkpoint:** 2026-10-20 (Europe/Prague)  
**Source of truth:** `shulda/lean_eppa_semigeneric`, current main at checkpoint:
`19fc761daa8877cce2b07f505a176e3e91ebf3e8`. Full public
`lake build` and axioms audit succeeded for this main commit in
GitHub Actions run **39318639359**.

This file supplements the detailed
[October 19 checkpoint](CHECKPOINT_COHERENT_GONE_2026-10-19.md).
Always refresh the live main branch and workflow statuses before
continuing; this checkpoint is historical and was created for
recovery after repeated chat crashes.

## Lean-certified mathematical result

The positive coherent **RAW** result for the trivial effective group
is now proved, with the actual theorem

`RawRectanglePresentation.exists_gOneGlobalCoherentExactRawFunctor`

in `SemigenericEPPA/Valuations/GOneGlobalCoherentRawFunctor.lean`,
merged by PR **#222** at `19fc761d`.

For each finite original raw rectangle presentation `P` whose
effective group `G` is subsingleton, this theorem chooses before
any partial map:

- a *single* factorial-size effective carrier and fixed original
  old zero-section embedding;
- one actual finite raw residual-cover presentation, with a
  single universal finite residual code and affine baseline;
- a global assignment `F S T f` to **every exact raw
  partial-isomorphism arrow** `f : S ≃ T`, valued in the
  literal whole-witness raw automorphism subgroup.

The assignment respects exact identities and exact source/range
composition and extends every old partial arrow *on all points of
its exact source*. Group values preserve original E and every
ordered raw `P_c` predicate, not only the effective colour.

The construction comprises full-CI-verified #168–#203,
#206–#207, #210–#219, and #222 as represented in the current
main. This means the previously challenging safe H-actions,
fixed raw baseline, finite stabilizer-group lifts, component
representatives, conjugation law and global flattening ARE
certified. Full ordinary raw EPPA was certified earlier.

**Important:** `exists_gOneGlobalCoherentExactRawFunctor` is
an exact raw groupoid statement. It is not yet the precise upstream
typed `AllThoseEPPA.Structure.IsCoherentEPPAWitness` API. Do
not report the latter as certified until the final bridge CI passes.

## Remaining final typed API PRs as at this checkpoint

- **#220** `UpstreamExactArrowFunctoriality.lean`, branch
  `formalize/upstream-exact-arrow-equivalence-and-comp`:
  translate the upstream `PartialEquiv.EqOnSource` relation to
  equality of exact raw arrows, and upstream exact composition to
  exact raw groupoid composition. Earlier CI failed on a Lean
  dependent-`generalize` operation; the new proof uses an
  abstract target-cast lemma
  `exactRawArrow_cast_target_val` and pointwise extensionality.
  The replacement was submitted at `e88f037a`.
- **#221** `RawExactFunctorToTypedCoherent.lean`, branch
  `formalize/global-raw-functor-to-typed-coherent-eppa`,
  stacked on #220: given a genuine raw exact groupoid functor
  and a fixed literal raw embedding, produce a real upstream
  `CoherentExtension` with `respects_equivalent`,
  `coherent`, and `extension_spec`.
  The latest version `9301acde` uses abstract helper lemmas
  `rawFunctor_heq_congr` and `rawFunctor_comp_cast`
  to avoid dependent elimination on upstream projections.
- **#223** `GOneTypedCoherentEPPA.lean`, branch
  `formalize/gone-final-typed-coherent-eppa`, stacked on
  #222: intended human-facing theorem
  `RawRectanglePresentation.finite_typedCoherentEPPA_witness`,
  returning a **finite** raw witness `Q`, a typed
  `Structure.Embedding`, and the actual
  `Structure.IsCoherentEPPAWitness` for the original
  `rectangleTrivialAction C` and R1–R3 binary language.
  The latest branch integrates corrections from #220/#221.
  A fresh CI attempt is needed when predecessor changes land.

At this checkpoint, the CI attempts for the revised #220,
#221 and #223 were **in progress** and not certified. Use GitHub
to review exact diagnostics before further edits.

## Recommended immediate work

1. Inspect the latest Actions runs for #220/#221/#223.
   Correct genuine errors, no matter whether they are Lean-level
   equality transports or actual mathematical assumptions.
2. Merge #220 when fully green. Rebase/retarget #221 against main,
   then merge #221 after a complete green build and allowed-axiom
   audit. Retarget #223 onto main containing both #222 and #221.
   Resolve PR root-import conflicts without changing proved
   statements unnecessarily.
3. Build, audit and merge the **typed** #223 main theorem.
   Inspect its actual stated finite-witness, original-language
   embedding and coherent extension properties against the
   manuscript. Confirm there are no extra hypotheses beyond
   the finite original raw presentation, finite colour fibres,
   and singleton effective group.
4. After success, prominently update README and formalization
   documentation and offer a directly linked stable Lean theorem
   to the researcher. The G=1 positive coherent theorem may
   then be called finished. Other sectors — nontrivial-G
   positive or negative coherence, DLF criterion, unrestricted
   finite SAP — remain separate projects.

## Mathematical safety and scope

- `CoherentTriple` insists on **exact** range/domain matching.
  Partial-semigroup composition with shrinking domains is not
  the theorem needed here.
- `PartialIsomorphism.Equivalent` forgets arbitrary values
  outside the source, so Lean identity of full `PartialEquiv`
  records is too strong.
- Each raw witness, original old embedding, universal residual
  code and raw baseline must be selected *before* later partial
  maps/groups, and a group action must be a true homomorphism.
- A fixed effective action is not enough unless every swapped
  cross-part edge has an honest self-reversing raw representative.
  This is why the genuine replicated-fibre construction was used.
- DLF's weaker relative safe-phase condition must not silently be
  replaced by the stronger coherent-positive global saturation
  assumption.
