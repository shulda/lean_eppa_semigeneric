# Checkpoint: finite coherent EPPA, trivial effective group

**Date:** 2026-10-19, evening (Prague time)
**Repository:** public `shulda/lean_eppa_semigeneric`
**Authority:** merged Lean sources and GitHub Actions CI, not chat claims.
**Private paper:** `shulda/generalized_semigeneric`; leave its CI disabled.

## Merged and CI-verified at the beginning of this checkpoint

- Ordinary raw EPPA for every finite raw fibre, including the exact
  original relational language and typed `AllThoseEPPA` EPPA interface
  (earlier work). The coherent theorem is **NOT** proved merely by
  this.
- Strict safe group actions on the *same prechosen* factorial-padded
  effective G=1 carrier, for **every induced** S and arbitrary H
  preserving actual old E/raw colours (PR #197).
- One fixed finite G=1 effective E/F witness carrying **both** ordinary
  partial-automorphism extensions and all safe induced H-actions
  (PR #198, merged as `b27fd7d4`).
- One fixed finite raw cover with a single universal residual code,
  literal original old-zero-section induced embedding, one baseline,
  individual raw extension API, and safe H-action group-lift API
  (PR #199, merged as `9a85f98c`).
- Actual exact old raw partial-isomorphism groupoid `ExactPartialIso`
  with inverse, identity and composition *only on exactly matched
  domains*, verified including all groupoid laws
  (PR #200, merged as `c4b56ee4`).
- Reference-connector groupoid conjugation formula for permutations,
  `beta_j rho(gamma_j^{-1} f gamma_i) beta_i^{-1}`,
  in earlier abstract #186.

The verified base when these new developments began was
`c4b56ee4d8e1c92d953d0b404fede3e0a2d49504`, with CI for
the earlier merged commits green. New main/head CI runs may still be
queued on GitHub after this checkpoint.

## Prepared new PRs — do NOT count as verified until full CI/axiom audit

1. **#201** (`formalize/finite-exact-raw-automorphism-groups`):
   actual `ExactPartialIso P S S` group and its strict
   `Aut(P|S) →* Perm(S)` evaluation, with finiteness.
   The first CI failure was missing a finite-type import; the
   `Mathlib.Data.Fintype.EquivFin` import was added. Recheck CI.
2. **#202** (`formalize/gone-common-effective-raw-witness`):
   one existentially selected factorial old injection, fixed
   effective G=1 carrier AND compatible `FixedJointRawCover`
   with universal APIs before ALL later S/H/partial maps.
   Builds directly from certified #198 and #199.
3. **#203** (`formalize/gone-unconditional-raw-lift-package`),
   stacked on #202: compose effective extensions + invariant
   old raw references + fixed raw cover APIs. Its headline is
   **one finite G=1 raw witness with ordinary EPPA AND actual
   homomorphic raw-automorphism extensions for every induced S**.
   The two expected components are `HasAllJointRawPartialLifts`
   and `HasAllJointRawGroupLifts`. This does not yet assign
   coherent extension to every arrow of the groupoid.
4. **#204** (`formalize/exact-groupoid-conjugation-assembly`),
   stacked on #201: exact `referenceCoordinate(i,j,f)`
   in `Aut(P|R)`, strict identity/composition, and one-component
   coherent conjugation `referenceCoherentArrow`.
5. **#205** (`formalize/exact-groupoid-old-vertex-extension`),
   stacked on #204: literal old-vertex extension property for
   every exact connector and arrow, using the same fixed
   old embedding and whole-witness stabilizer group lift.
6. **#206** (`formalize/binary-relational-automorphism-subgroup`),
   independent: literal relation-preserving permutations for E and
   all indexed raw `P_c` are a subgroup of `Perm(W)`;
   homomorphisms of certified raw automorphisms land in it.
   Needed to ensure connector conjugation preserves the *structure*,
   not only its carrier.
7. **#207** (`formalize/exact-raw-groupoid-components`),
   independent of #201: quotient `Set A` by exact raw
   isomorphism, choose one representative for every component
   and literal exact old connectors from it to all objects.
   These choices depend on the old raw structure, not on the
   later partial arrow.

At submission all the corresponding new GitHub Actions jobs were
reported as **queued**, not passed or failed. Do not merge or
advertise these theorems as complete until CI + allowed-axiom
audit pass. Runs that are still queued are not evidence about
proof correctness.

## Exact next steps

1. First check the current public main and CI/PR statuses. In
   dependency order repair and merge #201, #202, #203, #204, #205;
   #206 and #207 are independent and may merge whenever green.
   Retarget stacked PR bases to main once predecessors are merged;
   avoid treating import-list merge conflicts as mathematical errors.
2. Apply `HasAllJointRawGroupLifts` of #203 specifically with the
   **actual finite stabilizer** `ExactPartialIso P R R` from #201.
   Lift the result to the true raw automorphism subgroup #206.
3. For every exact component q from #207, use old connectors
   `gamma_i` and ordinary raw EPPA from #203 to choose
   whole-witness connector automorphisms `beta_i`. The old
   embedding, witness carrier, raw baseline and raw colouring
   must be common to all q,i and H.
4. Apply #204/#205's conjugation formula within the subgroup
   of literal raw automorphisms. Check the identity, exact
   composition and old-vertex extension in each component.
   There must be **no composition across nonisomorphic
   components**; only exact source/range-matched arrows matter.
5. Package the resulting global functor as actual
   `AllThoseEPPA.Structure.IsCoherentEPPAWitness` with the
   trivial language-action group, including language component 1.
   Audit the final theorem's quantifiers against the paper.
6. Only then claim **coherent EPPA for the G=1 positive sector**.
   The nontrivial-G coherent, DLF, and finite SAP claims remain open.

## Mathematical guardrails

- **EPPA plus separate extensions of individual partial maps** is
  not coherence. Conversely, a strict H-action on every induced
  substructure still requires a groupoid connector assembly.
- The witness and old embedding must be selected **before**
  the substructure or group H; the raw baseline must be the
  **same baseline** in both ordinary and H-group lift proofs.
- An arbitrary uniformly padded E/F action can create artificial
  flipped cross-part pairs. Use the *replicated genuine old fibre*
  safe action (#168–#178/#193/#197), not the naive action of #164
  alone. The needed raw flip-safety is proved.
- Preserve exact original ordered raw relations `P_c`; equality
  of their effective projections is insufficient.
- Do not use global congruence-saturation assumptions from the
  positive coherent branch in the weaker relative DLF branch.
- Do not claim anything is Lean-verified based only on a PR being
  open or on the absence of compilation errors in a local sketch.

This checkpoint is intended to survive chat truncation or crashes;
the live repo and CI are authoritative for later changes.
