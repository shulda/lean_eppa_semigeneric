# Formalization ledger — 2026-10-16

## Authority and verification status

- **Manuscript:** `shulda/generalized_semigeneric` (private),
  `paper_formalization_prep/group_valued_rectangles_formalization_v0_8.tex`,
  blob `3124ec728658652c0c9ac288d4640d195d97037c`.
- **Human research handoff:** `paper_formalization_prep/FORMALIZATION_PROJECT_HANDOFF_2026-10-16.md`.
- **Corrected DAG:** `paper_formalization_prep/FORMALISATION_SPINE_CORRECTED_DEPENDENCIES_2026-10-16.md`.
  It overrides older gates where hypotheses conflict.
- **Lean toolchain:** Lean/mathlib v4.34.1, `autoImplicit = false`,
  `relaxedAutoImplicit = false`.
- **Upstream reusable vocabulary:** `shulda/lean_all_those_eppa_classes`,
  commit `d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d` (verified green CI).
  Only definitions of language, structures, embeddings, exact partial maps
  and coherent extensions may be used; **do not invoke HKN EPPA existence**.
- **No main theorem verified yet.** Paper proof audits are human only,
  not Lean certificates; v0.8 PDF compilation is also unconfirmed.

## Exact paper statements to target

Let `G` be finite, `s` an affine anti-involution,
`C` a finite involutive raw alphabet and `φ : C ↠ G` reversal-equivariant.
Let `S = {g : G | ∃ c : C, φ c = g ∧ reverse c = c}`.
For the class `K(G,s,φ)` of finite complete cross-part colourings satisfying
the **noncommutative rectangle law**:

1. SAP, Fraïssé limit and infinitely many infinite E-classes.
2. **Ordinary EPPA** unconditionally.
3. **Coherent EPPA iff** `G` is trivial, or `S ≠ ∅` is a union of complete
   congruence orbits.
4. **Semi-coherent EP / DLF iff** `G` is trivial, or `S` contains at least
   one complete congruence orbit.
5. Explicit `G = C₄`, `s = id`, `S = {0,1,2}` separator:
   EPPA and DLF but not coherent EPPA.
6. Optional independent SAP rectangle-law converse (appendix A).
7. Low-priority Sági semi-coherent EP ↔ DLF for countable homogeneous
   finite-relational structures (appendix B).

**Not in scope:** Ramsey expansions, SWIR/SIR, ample generics, the
additional transfinite B-Ext characterization.

## Mathematical dependency gates

| Gate | Exact intent | State |
|---|---|---|
| G0 | finite affine reversal, `S`, cross-part colour type | Affine/group/reversal/rectangle algebra green; cross-part typing OPEN |
| G1 | recenter group at `g₀ ∈ S`, rank-one gauge, partial gauge transport | Recenter and gauge-colour identities green; congruence action in review, partial transport OPEN |
| G2 | finite structures, exact induced embeddings, strong amalgamation | Heredity, rank-one/gauge and canonical quotient green; corner-amalgamation algebra in review, global SAP OPEN |
| E0 | effective valuation construction with individual EPPA lifts | OPEN |
| R0/R1 | raw fibre code, one raw cover, individual raw lifts | OPEN |
| H0 | finite-group effective action via M/L cocycles, **without S saturation** | OPEN |
| H1 | separate effective flipped-edge orbit calculation | OPEN |
| H2/H3 | equivariant raw colouring and *one fixed-cover group lift* | OPEN |
| C0 | coherent groupoid normal form from individual connectors + stabilizer lifts | OPEN |
| C1/C2 | both coherent-positive branches and coherent-negative obstructions | OPEN |
| D0/D1 | relative safe finite action, phase separation and zero-section raw lift | OPEN |
| D2 | Q/H × Q binary-matrix F₂ involution-killing cover | OPEN |
| D3 | semi-coherent/DLF positive and negative criteria | OPEN |
| S0 | independent Sági bridge (low priority) | OPEN |
| OPT | converse SAP classification (independent optional appendix) | OPEN |

## Non-negotiable mathematical distinctions

1. The valuation coordinate for **target** part `r = (j,g)` is
   `λ_X(r) = χ(r) g(x)`. It is *not* the source's `h(x)`.
2. In the nonabelian case, keep the order of factors:
   `F(X,Y) = s(λ_X(r)) (K_{qr})⁻¹ λ_Y(q)`.
3. `s(xy) = s(y) t⁻¹ s(x)` with `t = s(1)`; writing an
   anti-homomorphism requires an **explicit** recentering.
4. The raw self-reversal set `S` is not automatically orbit-saturated.
   The coherent-positive argument can assume saturation; DLF cannot.
5. Individual partial-map extensions are not homomorphic extensions of
   an `Aut(D)` action, and neither is an all-partials coherent groupoid functor.
6. Coherent raw lifting uses **one globally fixed raw cover** with
   D-specific invariant references and potential corrections. DLF relative
   lifting uses an invariant baseline/zero section for a *chosen* safe H.
7. The finite relative cover uses binary matrices indexed by `Q/H × Q`,
   not the obsolete graph-chain proof.
8. Edge cases: empty `A`, trivial `G`, `S = ∅`, nontrivial affine shift,
   and higher-order H-elements flipping edges.

## CI and contribution discipline

- All project Lean modules are imported by `SemigenericEPPA.lean`.
- Every push/PR/manual dispatch runs a full build and axiom audit.
- No `sorry`, `admit`, custom axioms or unproved placeholders.
- A green setup / bridge check does **not** establish generalized semigeneric EPPA.
- Prefer small PRs with explicit theorem/gate names and proof/CI evidence.
- A mathematical error exposed by Lean is documented in the private
  manuscript/audit and corrected transparently, not hidden by strengthening
  a hypothesis silently.

## First theorem-gate increment — 2026-10-16

- Algebra/Rectangle.lean proves both directions of the exact noncommutative rank-one/rectangle equivalence for anchored parts.
- Algebra/Recenter.lean proves translated multiplication laws, inverse equations, anti-homomorphism for affine reversal at a fixed origin, invariance of horizontal rectangle constraints, congruence action equations, and transport of congruence expression.
- The translated group laws are still equations, not a separate Lean Group instance; full G1 torsor API and cross-part typing are OPEN.
- This remains algebraic groundwork, not a proof of SAP, EPPA, coherent EPPA, or DLF.

- Algebra/Gauge.lean: direct noncommutative verification of manuscript (2.5)--(2.7), including affine reversal of effective colours, gauge-coordinate invariance and transpose/reversal of the rectangle equation.

## Next algebraic increment — exact orbit action

- Algebra/CongruenceAction.lean gives the genuine group action on the fixed-point subtype of the affine anti-involution, with an explicit proof of fixed-locus stability.
- Distinguishes global congruence-orbit saturation of the raw self-reversing set S from the weaker existence of a single complete orbit, without making any coherence/DLF claim.
- Still required: two-sorted canonical part quotient, cross-part structure typing, and the actual valuation construction.

## 2026-10-16 — structure-language gate

- Structure/Language.lean encodes exactly E and P_c as binary relation symbols of the existing AllThoseEPPA.Language; there are no function symbols.
- IsRectangleStructure is the literal class predicate R1–R3, including exact one-colour cross-part completeness, reversal, and the group-valued rectangle law.
- The canonical quotient setoid is extracted from R1; embeddings, Fraisse-limit existence and SAP remain OPEN.

## R2/R3 relational-to-functional bridge

- Structure/EffectiveColour.lean selects the unique raw colour only on cross-part ordered pairs and proves its uniqueness and exact involutive reversal.
- Defines effective F(x,y)=φ(raw(x,y)) there, proves F(y,x)=s(F(x,y)), derives the other cross-pair conditions and proves the noncommutative rectangle equation for F.
- Choice is ordinary Classical.choice, explicitly allowed by the axiom policy; no new axioms or assumed colour values for same-part pairs.

## Induced-substructure increment (2026-10-17)

- `Structure/Induced.lean` defines arbitrary relational restriction, proves restriction of `E` and `P_c`, and constructs an actual `AllThoseEPPA.Structure.Embedding` for the inclusion.
- The hereditary closure of all R1–R3 axioms is proved without a finiteness assumption; empty vertex subsets are supported.
- The subsequent work needs class-indexed rank-one matrices, invariance of the class under general induced embeddings, then one-point SAP. A green CI for this PR certifies only the stated scope.

## 2026-10-17: anchored part matrices

- `Structure/PartMatrix.lean` turns two actual distinct E-classes into a typed total effective matrix, proves its noncommutative rectangle law, and derives rank-one factorization and the manuscript's reversed-edge gauge formula (2.5).
- It deliberately avoids giving arbitrary values to same-class pairs and keeps `s` affine/noncommutative.
- This block depends on previously verified R1–R3, effective-colour and rectangle/gauge modules. Exact CI/axiom verification is required before treating it as complete.

## Canonical imaginary-sort API (2026-10-17)

- `Structure/PartQuotient.lean` defines the genuine quotient `A/E`, the iff between equality of imaginaries and `E`, functorial maps of parts, injection under `E`-reflection, and composition.
- The canonical quotient of an induced substructure maps injectively into the original quotient. No transversal, gauge, or artificial identification of parts is introduced.
- Partial-isomorphism groupoid action on imaginary sorts and SAP remain OPEN. This checkpoint is green only after CI and axiom audit.

## 2026-10-17 — SAP corner kernel

- `Algebra/CornerAmalgamation.lean`: independently compatible new row/column of a group-valued rectangle matrix have one forced missing effective colour, and the completed `Option X × Option Y` matrix is rank-one.
- The forced corner is unique and independent of the chosen old anchors. The calculation preserves noncommutative factor order, matching manuscript equation (2.4).
- This proves only the local group-valued core of the one-point SAP construction, NOT global SAP: part amalgamation and raw-colour lifts remain OPEN.


## 2026-10-17 — two-new-vertex same-E-class rectangle lemma

- Algebra/SamePartRows.lean constructs two simultaneously appended rows, resp. columns, with each new row/column compatible with a common old matrix, and proves the entire enlarged matrix is rank-one and satisfies the rectangle law.
- It follows that two independently added vertices in the same old E-class are automatically mutually compatible toward every old E-class, covering the algebraic same-part case of one-point SAP.
- This is a local matrix lemma; actual strong amalgamation with raw colours and all E-part patterns remains OPEN.


## 2026-10-17 — completion of prescribed raw cross-colours

- Algebra/PrescribedRawLift.lean constructs, on an auxiliary linearly ordered carrier, a total raw colouring of all ordered cross-E pairs compatible with prescribed partial raw colours and a reversal-compatible effective colour function.
- It proves that old raw colours are retained, the new raw colouring is reversible and excludes same-part edges, and every raw colour projects to the original effective F. Only phi-surjectivity and reversal-equivariance of RawDatum are needed; NO self-reversing colour is assumed.
- This is a standalone raw-fibre choice step, not yet a full SAP witness or an automorphism-extension theorem.
