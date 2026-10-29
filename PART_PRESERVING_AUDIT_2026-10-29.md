# Source-to-Lean audit: part-preserving G=1 coherent EPPA and fixed-n subclasses

Date: 29 October 2026. **Private source (read-only):** `shulda/generalized_semigeneric`, `paper_formalization_prep/group_valued_rectangles_human_v0_11.tex` at blob `a64b38dd90a5cef15b35123ac4d81582a8fc6084`; `RESEARCH_STATE.md`, opening 27 October 2026 v0.11 checkpoint. Public Lean target: `shulda/lean_eppa_semigeneric`, PR #604.

## Independent statement comparison

| Human assertion and constraint | Exact Lean source | Review |
| --- | --- | --- |
| For every finite A and finite involutive raw alphabet, G=1, one coherent EPPA witness | `RawRectanglePresentation.finite_partPreservingTypedCoherentEPPA_witness` | Existing `GOneJointRawCarrier` and **same** groupoid coherent functor; no new EPPA witness, no assumption `S.Nonempty` |
| Canonical bijection A/E_A → B/E_B, [x] ↦ [ψx] | `PartQuotient`, `partQuotientEquivOfCover`, `finite_partPreservingTypedCoherentEPPA_witness` | Bijection of actual quotients, not merely cardinality; empty A included |
| No new E-parts | `gOneJointRawPart_coveredByOld` | Every z∈B has an old x with E_B(ψx,z); uses quotient first-coordinate and complete raw projection |
| Coherent EPPA, not just EPPA | `coherentTypedEPPA_of_exactRawFunctor_with_map` | Actual `Structure.IsCoherentEPPAWitness` with the existing exact `Equivalent` and `CoherentTriple` semantics |
| Existing coherent construction unchanged | `GOneJointRawCarrier`, `GOneFactorialCarrier`, `RawCoverVertex`; backwards-compatible old theorem | `M=|A|!` rather than human lcm; larger valid witness, **same** set of nonempty E-classes |
| Fixed n means at most n nonempty parts | `IsRectangleStructure.HasAtMostNonemptyParts n` | Injection of E-quotient into Fin n; n labels can be unused and n≥2 is **not** needed for the stronger expanded-language lemma |
| For each finite original E/R_c A with ≤n parts, get same-bound coherent witness | `finite_boundedPartsRelationalCoherentEPPA_witness` | Original *relational* structure argument, typed induced embedding, coherent witness, bound transferred via actual quotient equivalence |
| Two opposite raw orientation colours, G=1 | `twoOrientationGOneDatum`, `twoOrientation_part_iff_nonadjacent`, `finite_twoOrientationExpandedNPartiteCoherentEPPA` | Concrete expansion with reversed Bool colours, E definable by mutual nonadjacency; **expanded** E/R_c typed theorem |
| Pure single-arrow fixed-n tournaments | **Not a separate Lean theorem** | Mathematically follows by the definitional expansion, but needs a genuine complete language-transport API for `PartialIsomorphism`, `Equivalent`, `CoherentTriple`, `CoherentExtension` |
| Dense local finiteness of automorphisms of the fixed-n Fraïssé limit | **Not separately formalized in Lean** | Human manuscript derives via coherent EPPA→semi-coherent→Sági plus fixed-n Fraïssé theory; distinction explicitly maintained |

## Independent mathematical checks

- The $G=1$ raw refined data are the original `RawDatum`, not a new raw-alphabet assumption. Surjectivity $\phi:C\to G$ implies C is nonempty (where a group has identity); **no** reversal-fixed raw colour is required.
- Full coherent EPPA quantifies over all original partial automorphisms and preserves their exact partial-map equivalence and composition. The part condition is appended to the same witness/embedding; it is not obtained by choosing a new witness after the partial maps.
- The effective witness has $I\times\mathrm{Fin}(M)$, $I=A/E_A$; the raw residual carrier is $(I\times\mathrm{Fin}(M))\times((I\times\mathrm{Fin}(M))\to L)$. Its part relation depends only on the I-coordinate. $M=|A|!>0$ even for A empty, but I is empty then, hence the entire witness is empty. No phantom E-classes.
- The use of an injection $I\hookrightarrow\mathrm{Fin}(n)$ is equivalent to $|I|\le n$ for finite I, but does not require **exactly** n nonempty E-classes. Consequently the n-bounded age is hereditary, matching HJKS's convention of n possibly empty parts.
- The pure-arrow relation on two-orientation original structures is $R_\mathrm{true}$, while $R_\mathrm{false}(x,y)$ means $R_\mathrm{true}(y,x)$; E is the conjunction of both negative adjacencies. No loops arise because E is reflexive and edges exist only across E.
- The n-bounded original E/R_c age is **not** another unrestricted `RawDatum`; the theorem preserves the n-bound as a restriction on input and witness, not as a group-theoretic condition. This avoids applying an unrestricted coherent-EPPA classification to an unrelated proper hereditary subclass.
- Human fixed-n DLF follows mathematically by Sági; there is no new Lean theorem claiming a fixed-n Fraïssé limit with dense locally finite subgroup. A separate proof of that consequence in Lean would require the general Sági or a direct fixed-n limit argument.

## Remaining obligation for literal pure-tournament Lean

Build a faithful pair of functors between $L_\to$ n-partite tournaments and the definitional expanded $E,R_\mathrm{false},R_\mathrm{true}$ age. In particular, prove extension/restriction of the **entire typed** `PartialIsomorphism` data, preserve sources, targets, `EqOnSource` and `CoherentTriple`, and push the `CoherentExtension` assignment to the single-arrow language, including automorphism multiplication. Only then call the result `IsCoherentEPPAWitness` for the pure tournament language. These are new library interfaces, not missing steps in the certified G=1 part-preserving witness proof.

## Exact complete CI certificate

At the integrated mathematical head `9ee7642d098a416ad0e65e5cd9e104b71b6c70ef`, [full root Lean CI #40873674942](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40873674942) built the complete `SemigenericEPPA` root library (1,865 jobs) and audited 4,072 declarations. The accepted axioms were exactly `propext`, `Classical.choice`, `Quot.sound`. The branch workflow had been restored byte-for-byte to the original `main` configuration before this certification, and this run checks the strengthened G=1 coherent theorem, the original-relational bounded-n theorem and the two-orientation expanded specialization. Subsequent documentation-only edits do not change these Lean sources.

## Certification checklist

- [x] Fixed original G=1 coherent witness meets every old E-part (focused CI #40864154240).
- [x] Actual quotient equivalence and strengthened coherent witness (focused CI #40864938999).
- [x] n-bounded original E/R_c class and two-opposite-orientations specialization (focused CI #40868624158).
- [x] Full root-library Lean build passed on `9ee7642d098a416ad0e65e5cd9e104b71b6c70ef`, [full root Lean CI #40873674942](https://github.com/shulda/lean_eppa_semigeneric/actions/runs/40873674942): 1,865 jobs.
- [x] Full allowed-axiom audit passed on the same SHA: 4,072 declarations, only `propext`, `Classical.choice`, `Quot.sound`.
- [ ] Re-verify merged source and Wiki against the certified commit.
- [ ] Literal one-arrow `IsCoherentEPPAWitness` (documented follow-up; not a blocker for the expanded-language result).
