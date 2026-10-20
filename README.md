# Generalized semigeneric structures — Lean formalization

Formalization of the group-valued rectangle construction, EPPA, coherent EPPA, and the dense-locally-finite (DLF) criterion.

**Mathematical source:** the private `shulda/generalized_semigeneric` repository, directory `paper_formalization_prep/`. As of 2026-10-16 the formalization target is `group_valued_rectangles_formalization_v0_8.tex`; see `FORMALIZATION_PROJECT_HANDOFF_2026-10-16.md` and the corrected dependency graph. The central **ordinary EPPA theorem**, both for functional raw-colour presentations and for all literal relational R1–R3 structures, is now Lean-verified. Positive coherent EPPA for the trivial effective group G is now Lean-verified in the original R1–R3 binary language for every finite RAW presentation (PR #227) and for every actual finite RELATIONAL member satisfying IsRectangleStructure (PR #228). Both original-language typed theorems return real AllThoseEPPA.IsCoherentEPPAWitness data. The nontrivial-group coherent and DLF classifications remain open.

This public repository keeps Lean source, an auditable [formalization ledger](FORMALIZATION.md), and GitHub Actions build/axiom checks. The private paper repository must not run CI. The existing explicit valuation witnesses are the intended proof method; the earlier `AllThoseEPPA` library is used only for its partial-isomorphism/coherence vocabulary, not as a black-box EPPA theorem.

**Ordinary EPPA status (2026-10-20):** The **complete finite ordinary EPPA theorem** is Lean-verified for arbitrary finite raw-colour fibres, both in the raw-function presentation and the original relational R1–R3 language. See [raw EPPA](SemigenericEPPA/Structure/RawEPPA.lean), [relational EPPA](SemigenericEPPA/Structure/RelationalRawEPPA.lean) and the [typed `AllThoseEPPA` API](SemigenericEPPA/Bridge/RawTypedEPPA.lean). The finite affine residual code, fixed raw-cover witnesses and individual automorphism lifts are actual Lean constructions, not HKN applications.

**Certified positive coherent EPPA for G=1 (2026-10-20):** The same finite raw-cover witness now supports one strictly coherent groupoid functor extending all exact old partial isomorphisms, preserving literal E and every ordered raw colour (PR #222). The final original-language upstream typed statement, [RawRectanglePresentation.finite_typedCoherentEPPA_witness](SemigenericEPPA/Bridge/GOneTypedCoherentEPPA.lean), was CI-certified and merged as PR #227. It returns a finite witness and actual typed embedding, satisfying IsCoherentEPPAWitness with the exact Equivalent and CoherentTriple clauses. The universal witness, old embedding, residual code and baseline are chosen before all partial maps.

**Certified relational G=1 result:** [IsRectangleStructure.finite_relationalTypedCoherentEPPA_witness](SemigenericEPPA/Bridge/RelationalTypedCoherentEPPA.lean) is in main (PR #228).

**Certified nontrivial-G *necessary* coherent criterion (2026-10-20):** The actual typed 2+1 and 3+1 raw gadgets force the exact condition `Subsingleton G ∨ (d.selfReverseEffective.Nonempty ∧ d.IsCongruenceSaturated)`. The completed original-language theorem is [RawDatum.necessaryCoherentCondition_of_allFiniteRawPresentations](SemigenericEPPA/Bridge/CoherentFiniteRawClassNecessity.lean) (PR #246). This proves only the **necessity** direction; the nontrivial-G **sufficiency** construction is not yet established.

**Nontrivial-G positive infrastructure certified through PR #254:** Actual old gauge matrices provide occupied H-multipliers and their strict noncommutative cocycles (#249–#251, #253); a genuinely reversal-fixed good colour completes the old occupied skeleton (#252), and swapped-only congruence-orbit safety is formalized (#245, #247, #254). These are algebraic/conditional group-action components, not yet one full finite coherent EPPA witness. The next gates are a single H-action on the full two-layer valuation witness, old-vertex compatibility, raw-cover lifts and global coherent groupoid assembly. The relative DLF criterion (which requires only **one complete good congruence orbit**, not global saturation) and unrestricted finite SAP also remain open. For the previously completed G=1 case see the [historical checkpoint](CHECKPOINT_TYPED_COHERENT_GONE_2026-10-20.md); consult [FORMALIZATION.md](FORMALIZATION.md) for the current ledger.

## Build

Lean/mathlib: pinned v4.34.1. A pinned upstream `AllThoseEPPA` dependency supplies reusable definitions.

```bash
lake update
lake exe cache get
lake build
```

CI runs on pushes, pull requests and manual dispatch, with an axiom audit allowing only `propext`, `Classical.choice` and `Quot.sound`.

See [FORMALIZATION.md](FORMALIZATION.md) for the precise theorem roadmap and proof-status distinctions.
