# Formalization ledger — historical gates from 2026-10-16, with 2026-10-25 status update

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
- **Current verified headline (2026-10-25):** ordinary finite EPPA
  and the complete original-relational coherent-EPPA classification
  are Lean-certified. The complete countable homogeneous DLF
  **existence** criterion is also Lean-certified in
  `Structure/DLFCompleteClassification.lean`:
  `d.HasCountableHomogeneousDLF ↔ Subsingleton G ∨ d.HasCompleteGoodOrbit`.
  This combines both separately constructed positive limits and the
  direct original-raw negative converse, without Sági's bridge.
  The unrestricted semigeneric-specific semi-coherent EP ⇔ DLF
  equivalence and its original-relational DLF formulation are now
  additionally certified in PRs #570 and #571 (merged into main).
  The old relative finite safe-group EPPA module remains one of the
  finite positive ingredients. The arbitrary finite SAP iteration,
  unconditional stand-alone Fraïssé existence/uniqueness formalization,
  and the *general* Sági semi-coherent↔DLF equivalence are separate
  unformalized tasks. **The gate table and older dated entries
  below are historical snapshots, not the present theorem status.**
  See [README](README.md) and
  [DLF audit](DLF_CLASSIFICATION_AUDIT_2026-10-25.md) for current statements.

## Latest certified finite semi-coherent developments (2026-10-25)

- `Structure/DLFSemiCoherentSafeDLFClassification.lean` proves the full
  iff between the concrete cofinal **safe** finite subgroup-extension
  family and actual original-raw homogeneous DLF. Combined original
  E/R_c language CI passed before integration at commit `867ee0b`.
- `Structure/DLFFiniteUnrestrictedSemiCoherentEP.lean` formalizes
  Sági-style unrestricted selected finite action families with no
  involution safety hypothesis and proves the positive implication
  DLF ⇒ unrestricted semi-coherent EP. CI passed on PR #557.
- `Structure/DLFSemiCoherentUnrestrictedAgeTargetSuccessor.lean`
  gives the finite arbitrary prescribed-age successor for such a
  selected family. CI passed on PR #560.
- `Examples/FourColourDLFNotCoherent.lean` supplies a literal
  explicit C₄ model with DLF and failure of coherent EPPA;
  full CI passed on PR #558.
- `Examples/FourColourSemiCoherentSeparation.lean` now proves the
  unrestricted semi-coherent finite extension property for that
  same C₄ datum and packages semi-coherent EP + original-relational
  DLF + failure of coherent EPPA in one exact conjunction.
  Full build and axiom audit passed on PR #572, head `7a9e2c34`,
  merged as `c3a8f29`.
- **UNRESTRICTED converse and classification certified.**
  `Structure/DLFUnrestrictedSemiCoherentClassification.lean` proves
  `RawDatum.finiteRawSemiCoherentEP_iff_dlf` and
  `RawDatum.finiteRawSemiCoherentEP_iff` for an arbitrary selected
  cofinal family of genuine finite automorphism subgroup actions,
  with no involution-safety assumption. The finite relative
  successor, actual countable vertex/group directed limits, faithful
  raw automorphism action, full finite age, ultrahomogeneity, density
  and local finiteness are all constructed in Lean. Full build and
  permitted-axiom audit passed on PR #570, exact head `67f2d243`;
  merged into `main` as `7d4528d`.
- **Original-relational DLF bridge certified.**
  `Bridge/SemiCoherentRelationalDLFClassification.lean` states
  `RawDatum.finiteRawSemiCoherentEP_iff_relationalDLF` for an
  actual `AllThoseEPPA.Structure (rectangleLanguage C)` with its
  literal full relational automorphism group; it also proves
  original-relational coherent EPPA ⇒ unrestricted semi-coherent EP
  ⇒ original-relational DLF. Full build and permitted-axiom audit
  passed on PR #571, exact head `58ebcdd8`; merged as `5a1f486`.
  The finite semi-coherent predicate is expressed via equivalent
  complete original-raw presentations, not yet as a separately named
  native `AllThoseEPPA.Structure` finite-action predicate.
- The **general Sági equivalence** for arbitrary homogeneous
  finite-relational structures, and an independent Fraïssé
  uniqueness theorem for externally specified limits, remain
  separate future formalization tasks. The dated gate table below
  is a historical snapshot, not a claim these current results are open.

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


## 2026-10-17 — exact one-point E-partition amalgam

- Structure/OnePointParts.lean proves that two equivalence-relation extensions of a common old carrier by separate new points admit a strong amalgam on the old carrier plus two *distinct* new vertices. Every old E-equivalence and both one-point restrictions are preserved and reflected.
- Attaching both new vertices to the same old class is allowed while their vertex identities remain distinct. Fresh classes are separated; empty old carrier is supported.
- Together with the already green CornerAmalgamation and SamePartRows modules this closes the **abstract E-partition and local group-valued matrix cases**, but does NOT yet yield full SAP of raw-coloured structures.


## 2026-10-17 — exact option-valued raw relational presentation

- Structure/RawPresentation.lean defines a functional data interface: an E-equivalence relation and an Option C raw-colour function, with exact reversal, absence of same-class colours, completeness of cross-class colours and the noncommutative rectangle law.
- It constructs a genuine AllThoseEPPA.Structure on the L_C language and proves IsRectangleStructure, preserving all four R1--R3 clauses. This is designed as the output of the general prescribed raw-fibre completion lemma.
- Equivalence with every original relational structure and global strong amalgamation remain to be established.

## 2026-10-17 — prescribed raw-colour completion

- `Algebra/PrescribedRawLift.lean` proves total raw-colour completion of a reversible effective colouring with compatible partially prescribed raw edges, preserving all prescribed edges and `φ` values.
- It orients each unordered cross-edge using a temporary linear order, so no self-reversing raw colour or congruence-orbit saturation is needed.
- This is a raw-choice component, not yet the complete one-point SAP theorem; a bridge to `RawRectanglePresentation` and effective geometry is still required.

## 2026-10-17 — exact effective-to-raw construction

- `Structure/EffectiveRawExtension.lean` packages explicit hypotheses for a reversible effective E-rectangle geometry F and compatible prescribed partial raw colours.
- It constructs a genuine `L_C`-structure satisfying R1–R3 with exactly the original E and all old raw-colour predicates preserved. No hypothesis involving S or coherent EPPA is used.
- Full SAP remains OPEN until a compatible effective F is constructed on all one-point amalgams and genuine old-side embeddings are proved.

## 2026-10-17 — exact functional/relational return map

- `Structure/RelationalRoundtrip.lean`: every genuine R1–R3 relational structure yields a canonical Option-valued raw-colour function. Absence of a raw colour is equivalent to E, and the raw option reverses by the given involution.
- Converting the functional presentation back to the literal language reproduces the exact E and every P_c predicate; this is necessary for faithful old-side embeddings in a future SAP construction.
- Global SAP still requires the effective two-new-point colouring and explicit induced embeddings.

## 2026-10-17 — unique transition of rank-one factorizations

- `Algebra/RankOneGaugeTorsor.lean` proves that any two anchored factorizations F(x,y)=row(x)col(y) over an arbitrary noncommutative group are related by a unique multiplier k with row'(x)=row(x)k and col'(y)=k⁻¹col(y).
- The transition leaves all matrix entries unchanged, and this is the elementary algebraic kernel for the paper's affine gauge torsor; the explicit affine statement is developed separately.

## 2026-10-17 — complete two-part affine gauge equivalence

- `Algebra/GaugeConverse.lean` proves the converse of the manuscript's affine gauge change (2.7): equality of effective matrices on two nonempty anchored parts gives unique left multipliers u,v and K'=v K s(1)⁻¹ s(u). The forward direction follows from the already verified gauge-change lemma.
- The iff is verified for arbitrary nonabelian groups and affine anti-involutions; it will allow overlapping local gauge presentations to be aligned in SAP and EPPA.
- This is the two-part torsor law; its globally indexed multi-part/partial-map version is still OPEN.

## 2026-10-17 — effective geometry of actual R1–R3 structures

- `Structure/EffectiveGeometry.lean` isolates the effective E-rectangle geometry from raw fibres, with affine reversal required only on distinct E-parts and the exact noncommutative rectangle equation.
- Every existing `IsRectangleStructure` produces such geometry canonically, using the dummy value 1 on same-part pairs (where all algebraic axioms are indifferent). Old prescribed raw colours are proved compatible with the resulting F.
- `EffectiveGeometry.of_cross_eq` proves same-part dummy values can be changed arbitrarily with no effect on the geometry. This module prepares the common effective F of the one-point amalgam; that existence theorem remains OPEN.

## 2026-10-17 — old-old SAP corner from genuine one-point geometries

- `Structure/OnePointEffective.lean` introduces one-point effective extension with exact E and F on the old carrier, and proves the R3 row/column compatibility hypotheses of the forced-corner lemma directly from each extension.
- For two distinct *old* E-classes P,Q with the two new vertices attached respectively to P and Q, proves that the uniquely forced missing effective colour extends the entire matrix on those two parts with every rectangle valid, independently of old anchors.
- This is the central old-part/old-part SAP case; the same-old-part and fresh-singleton cases and global assembly remain OPEN.

## 2026-10-17 — two new vertices in the same old E-part

- `Structure/OnePointSamePart.lean` proves that two independently added new vertices in the SAME old E-class have mutually compatible rows and columns towards every other old class, using actual R3 in their respective one-point geometries.
- Both simultaneous matrices are rank-one; the exact horizontal/vertical displacement identities and independence of the representative of the common old part are formalized. No equal-colour assumption is imposed.
- This closes the same-old-part local effective SAP case, while global assembly and fresh-part cases remain OPEN.

## 2026-10-17 — fresh E-parts are singleton in one-point strong amalgams

- `Structure/FreshPart.lean` proves a new vertex not attached to an old E-class remains the unique vertex of its own E-class in the strong amalgam. Handles either side, empty old base, and two fresh vertices.
- This supplies the local trivial-rectangle case for the eventual effective SAP assembly, complementary to the checked old-old forced corner and same-old-part lemmas. No full SAP theorem yet.

## 2026-10-17 — quotient-imaginary gauge presentations

- `Structure/QuotientGauge.lean` implements two-sorted gauge data on the canonical quotient `V/E`, with skeleton K and λ coordinates. It proves the paper's formula (2.6) yields an effective E-rectangle geometry with affine reversal and the exact noncommutative rectangle equation, without finiteness or an auxiliary order.
- This is the forward half of the gauge presentation lemma. The converse (anchored reconstruction for arbitrary effective geometry) and the actual global one-point SAP glue remain OPEN.

## 2026-10-17 — full converse canonical gauge presentation

- `Structure/QuotientGaugeConverse.lean`: every effective E-geometry admits quotient-indexed skeleton K_ij and vertex gauges λ_(x,j), choosing one representative per E-class via Quotient.out.
- Proves the skeleton affine reversal and that reconstructing through the gauge formula returns the ORIGINAL effective colour on every cross-part ordered pair, with the noncommutative factor order intact.
- Combined with the verified forward direction, the two-sorted effective presentation (2.6) is now proven both ways; full one-point SAP assembly remains OPEN.


## 2026-10-17 — arbitrary-label gauge for global SAP

- `Structure/IndexedGauge.lean`: gauge coordinates may be indexed by an arbitrary type I and map `label : V → I`, **not necessarily surjective**. The induced E is equality of labels; the exact affine/noncommutative gauge expression yields effective reversal and all rectangle laws.
- Old quotient-indexed gauges embed as a special case. The verified strong one-point part amalgam on `V ⊕ Bool` is realized exactly by the `combinedPartIndex` label map into `(Quotient E) ⊕ Bool`, even when some fresh labels are unoccupied.
- The **global selection** of K and λ preserving both existing one-point effective geometries is still OPEN. This eliminates the label/quotient-type mismatch but is not yet an SAP theorem.

## 2026-10-17 — global SAP skeleton for old and fresh labels

- `Structure/ExtendedSkeleton.lean` constructs a concrete affine-reversal-compatible skeleton on `(V/E) ⊕ Bool`, extending the old quotient gauge skeleton and setting `K(old,fresh)=1`, `K(fresh,old)=s(1)` (and a fixed orientation between two fresh labels).
- This is valid even if the two fresh labels are unoccupied and if `s(1)≠1`. The resulting generic gauge has exactly the verified strong one-point E-partition.
- Remaining SAP proof needs selection of vertex gauges λ and proof that the resulting effective F preserves both old one-point extensions.

## 2026-10-17 — attached-new vertex side-preservation kernel

- `Structure/AttachedGaugeFactor.lean` proves directly from the actual one-point effective geometry that an attached new vertex has the exact noncommutative gauge formula `F(new,a)=s(F(q,new))*F(p,q)⁻¹*F(p,a)` towards a different old part, including transport of the old representative p within its E-class.
- This is the principal algebraic side-preservation lemma for the globally chosen quotient/label gauge, not yet the global SAP assembly itself.

## 2026-10-17 — explicit global SAP vertex gauges

- `Structure/OnePointGaugeChoice.lean` selects concrete λ coordinates from the old effective geometry and the two one-point extensions, distinguishing attached new vertices and fresh singleton labels.
- The indexed skeleton with these coordinates creates one genuine global effective rectangle geometry. It is proved to preserve the exact strong E amalgam and the OLD–OLD effective colours. For a fresh new E-part it also preserves all outgoing effective colours to old vertices (on either side).
- Remaining SAP assembly proof: attached-new/old colour preservation, reversal of the freshly proved edges, then transport of prescribed raw colours and the two exact embeddings. These results are not silently asserted here.

## 2026-10-17 — attached side preservation in the global gauge

- `Structure/OnePointGaugeAttached.lean` proves that the explicit global indexed gauge reproduces every new-to-old effective edge for either one-point extension when the new vertex belongs to an existing old E-class and the old endpoint is cross-part. This uses the actual attached-new R3 factor lemma.
- Combined with the fresh-new/old and old/old preservation lemmas of `OnePointGaugeChoice`, this covers all nontrivial SIDE-preservation cases; the all-pairs cross-preservation theorem is still to be packaged and verified before calling effective one-point SAP complete.

## 2026-10-17 — global effective one-point strong amalgamation

- `Structure/OnePointEffectiveAmalgam.lean` packages the explicit gauge construction as ONE common effective E-rectangle geometry on the strong carrier `V ⊕ Bool` and proves exact E on each side and exact preservation of every CROSS-PART effective colour, with no finiteness or self-reversing-colour hypotheses.
- Cases: old-old from rank-one gauge, new-fresh-old from fresh skeleton, new-attached-old from actual R3 attached factor, reverse directions via affine involution. Every cross-part pair is covered; same-part dummy F-values are correctly irrelevant.
- This is the main *effective one-point SAP* theorem, but NOT yet raw-colour class SAP: the compatible prescribed raw side labels must still be completed into a genuine L_C structure and then finite SAP derived.

## 2026-10-17 — raw one-point prescribed edge gluing

- `Structure/OnePointRawAmalgam.lean` packages exact raw colours on two one-point effective extensions and verifies their joint partial prescription on `V ⊕ Bool` has no same-E colours, is reversal invariant, and projects to the **verified global effective one-point amalgam**. All side raw edges are prescribed; only new-new is left free.
- Consequently the existing raw-fibre completion constructs one genuine R1–R3 structure on the strong carrier, with an explicit auxiliary linear order on that carrier. Exact induced raw-embedding statements and the finite-order-free SAP theorem are still to be proved.

## 2026-10-17 — complete ordered raw one-point SAP

- `Structure/OnePointRawExact.lean`: the previously verified raw completion preserves both side raw-colour functions EXACTLY whenever their old-common raw substructure agrees. It proves all E and all P_c relations on both original sides are preserved AND reflected and packages a genuine one-point strong amalgamation theorem in the literal L_C language on `V ⊕ Bool`.
- An auxiliary `LinearOrder (V ⊕ Bool)` is explicitly assumed for choosing raw representatives. For the paper's finite SAP this can be supplied by a linear order on a finite carrier. General finite SAP and Fraïssé remain OPEN until the finite-order and iterated-one-point bridges are checked.

## 2026-10-17 — finite raw one-point SAP without an order hypothesis

- `Structure/FiniteOnePointRaw.lean` proves every finite common carrier has an auxiliary linear order (chosen via `Fintype.equivFin`) and therefore strengthens the exact raw one-point SAP theorem to finite bases without any additional order condition. The auxiliary order does NOT belong to the relational language.
- The two new vertices remain genuinely distinct in `V ⊕ Bool`, and all old E and raw P_c predicates are preserved and reflected on both sides. Global finite SAP, Fraïssé and EPPA remain separate goals.

## 2026-10-17 — one-point SAP for literal R1–R3 input structures

- `Structure/LiteralOnePointSAP.lean`: for a genuinely finite R1–R3 base A and two literal R1–R3 one-point structures whose *induced* E and raw P_c relations on old vertices agree exactly with A, constructs their common effective base and both true effective extensions, extracts exact raw-colour functions, and derives the compatibility of all old raw colours.
- Uses finite raw one-point SAP to produce a literal R1–R3 structure on `V ⊕ Bool` whose two exact Option-V inclusions preserve/refect EVERY E and P_c relation. No external ordering, S-orbit hypotheses, or EPPA theorem. This is the fully typed finite **one-point** SAP gate; arbitrary finite SAP and Fraïssé remain separate.

## 2026-10-17 — literal typed embedding interface

- `Structure/PairwiseEmbedding.lean` constructs a genuine `AllThoseEPPA.Structure.Embedding` with language component 1 from an injective map preserving/reflection both E and every P_c. Converse APIs read back the exact E and P_c iff from a language-identity embedding.
- The theorem is pure binary-language syntax and does not depend on SAP or use HKN. It is designed to turn one-point SAP's previously proved pointwise relation equivalences into actual typed strong embeddings.

## 2026-10-17 — literal finite one-point SAP as typed embeddings

- `Structure/LiteralSAPEmbeddings.lean` packages the verified literal one-point SAP into genuine `AllThoseEPPA.Structure.Embedding` inclusions for the two source structures, with identity language action.
- Their carrier maps are exactly `firstOnePoint` and `secondOnePoint`, and their images intersect if and only if both vertices are the same old-base vertex. This formally records the strong (no-new-point-identification) character of the amalgam in the API required by iteration.
- The general finite SAP induction remains OPEN and will use the pullback/reindexing API to normalize arbitrary embeddings and transport the one-point theorem.

## 2026-10-17 — exact reindexing and induced-embedding primitive

- `Structure/Pullback.lean` defines full relational reindexing along arbitrary vertex maps and proves the entire R1–R3 class predicate is preserved. Injective reindexing comes with an actual identity-language `AllThoseEPPA.Structure.Embedding`, and bijective renaming is a special case.
- This supplies the renaming/restriction step required to normalize arbitrary finite embeddings to standard `Option V` one-point diagrams for the iteration of SAP.

## 2026-10-17 — normalize arbitrary one-point carrier names

- `Structure/OnePointNormalization.lean` shows an injective old-carrier map `f : V → W` with exactly one remaining fresh vertex induces an equivalence `Option V ≃ W` with `some a ↦ f a` and `none ↦ fresh`.
- Pulling back any R1–R3 structure along it preserves every old-old E and raw P_c relation exactly, gives a valid canonical one-point R1–R3 structure on `Option V`, and provides an actual identity-language `AllThoseEPPA.Structure.Embedding` into the original side.
- This is the key transport step for reducing arbitrary finite extensions to one-point SAP diagrams; the actual arbitrary finite SAP induction remains OPEN.


## 2026-10-17 — pasting exact strong-amalgamation squares

- `Structure/StrongSquare.lean` formalizes the carrier-level strong-square conditions: commutativity on the base, exact intersection of images, and joint image coverage of the amalgam.
- Proves interchange of sides, both identity-square base cases, and **horizontal pasting**: composing two strong squares along their common intermediate side produces another strong square, with exact overlap *and* image coverage.
- This is the algebraic categorical kernel of the induction from one-point to arbitrary finite SAP. It is independent of a relational language; typed `Structure.Embedding` maps supply the injections in applications. The remaining finite-filtration/existence induction is OPEN.

## 2026-10-17 — literal one-point SAP with exact strong-square cover

- `Structure/OnePointStrongSquare.lean` combines the already verified genuine `AllThoseEPPA.Structure.Embedding` one-point SAP theorem with the generic `StrongSquare` interface. The square commutes on all old vertices, has exact overlap and its two images jointly cover the entire carrier `V ⊕ Bool`.
- The exact cover condition allows successive one-point amalgams to be pasted using `StrongSquare.paste`, instead of silently producing additional intermediate vertices. The finite induction over arbitrary diagrams remains OPEN.

## 2026-10-17 — arbitrary-carrier one-point SAP

- `Structure/RelativeOnePointSAP.lean` normalizes two *arbitrarily named* one-point R1–R3 extensions with injective old-carrier maps through `Option X`, applies the verified literal typed one-point SAP and transports both embeddings back.
- The resulting valid structure on `X ⊕ Bool` is a strong amalgam: the two source images intersect *iff* the source vertices are the images of the same old base vertex. Input side carrier types need not match; finiteness of X alone suffices.
- This is the relative pushout step required to iterate one-point SAP along arbitrary finite diagrams, not yet general finite SAP itself.

## 2026-10-17 — exact one-point adjoining on an arbitrary vertex subset

- `Structure/AdjoinSubset.lean` canonically identifies `Option S` with the subtype of `insert x S` for any `x ∉ S`, including infinite/empty S. It proves the old/fresh vertex cover and freshness and yields a genuine `AllThoseEPPA.Structure.Embedding` into the induced extension.
- The restriction to old vertices preserves and reflects every E and P_c relation literally and keeps the result in R1–R3. This is the precise type-level normalization needed to build a finite filtration of arbitrary one-point enlargements.
- Iterating SAP on arbitrary finite diagrams remains OPEN.


## 2026-10-17 — EPPA skeleton multiplier algebra (3.9–3.12)

- `Algebra/SkeletonMultipliers.lean`: for arbitrary affine anti-involution s and nonabelian G, given K,K',m the unique reverse multiplier n=K'·(s(1)⁻¹s(m))⁻¹·K⁻¹ satisfies equation (3.9) in BOTH orientations. The second orientation uses the exact identity α²(g)=s(1)⁻¹g s(1).
- Proves that condition (3.9) preserves every effective cross colour under the corresponding left gauge multipliers, and packages the forced orientation-pair choice. These are the nontrivial algebraic ingredients of (3.10)–(3.12), **not** yet the global witness automorphism construction.

## 2026-10-17 — effective EPPA valuation carrier and target incidence

- `Valuations/EffectiveCarrier.lean` formalizes witness parts `(V/E) × (V → G)`, witness vertices `(q,x,χ)` with `[x]=q.1`, and a vertex-valuation coordinate for every *other* witness part.
- The combined incidence is **literally** `χ(r) * r.2(x)` for the TARGET part `r=(j,g)`; it does not use the source part valuation. This is paper equation (3.5), the critical target/source distinction.
- Any affine-reversal-compatible witness skeleton yields a genuine effective rectangle geometry via the verified `IndexedGauge` theorem, and the exact formula (3.6) is proved. Distinguished old parts/vertices with neutral part valuations are injected and their old incidence coordinates recovered.
- This starts gate E0 but is **not** yet an EPPA witness theorem: finiteness of the carrier, old F preservation for a chosen skeleton, and individual partial-automorphism extensions remain OPEN.

## 2026-10-17 — literal old copy of the effective EPPA valuation witness

- `Valuations/OldEmbedding.lean` introduces the exact neutral-part skeleton hypothesis K[(i,h₀),(j,h₀)]=K^A[i,j]. It proves x↦oldWitnessVertex x preserves and reflects the E-partition and every cross-part effective group colour, using target-part incidences χ(r)·g(x).
- This checks the EFFECTIVE old-embedding step (3.7)–(3.8) with genuinely noncommutative affine reversal. Raw colour lifting and automorphism extension are OPEN, as is the E0 EPPA theorem.

## 2026-10-17 — explicit finite-order witness skeleton

- `Valuations/WitnessSkeleton.lean` constructs an affine-reversal-compatible skeleton for the two-layer effective witness from ANY auxiliary linear order on blown-up parts. Neutral-to-neutral entries reproduce the old quotient skeleton exactly; other unordered pairs get 1/s(1) in the two orientations.
- The old neutral witness embedding therefore preserves all effective cross colours by the verified old-copy theorem. The auxiliary ordering is not part of the structural language. The finite-choice of an order, witness finiteness and extension of partial automorphisms still require their own Lean gates.

## 2026-10-17 — the abstract indexed-gauge automorphism criterion

- `Valuations/GaugeAutomorphisms.lean` states the exact σ,τ,m data of the effective witness automorphisms: a permutation of imaginary labels, a permutation of real vertices, the left gauge-coordinate multipliers, and the affine skeleton condition (3.9). It proves E is preserved and reflected and all cross-part effective colours are fixed.
- This gives the complete SUFFICIENCY direction of the effective automorphism criterion (2.8) and the algebra of (3.11–3.12), independent of the still-open construction of such permutations from partial automorphisms.

## 2026-10-17 — exact witness-coordinate transport (3.11)

- `Valuations/CoordinateTransport.lean` defines the fibre of old labels over each blown-up witness part and constructs the transported vertex under any witness-part permutation σ, fibre bijections ρ_q and ordered pair multipliers m(q,r).
- The defining coordinate uses the TARGET part valuation at the NEW old label. Proves `λ_(ΘX)(σr) = m(q,r) λ_X(r)` exactly, plus uniqueness of each transported χ-coordinate. No automorphism existence, finiteness or coherent-action assumption is smuggled into the lemma.

## 2026-10-17 — global witness-part multipliers (3.9)

- `Algebra/GlobalWitnessMultipliers.lean` chooses a multiplier for each ordered pair of witness parts for an arbitrary σ. It chooses 1 on increasing pairs and the mathematically forced reverse multiplier otherwise, using an auxiliary linear order.
- Proves the exact affine/noncommutative skeleton equation (3.9) for ALL ordered distinct pairs, including the reverse orientation, and packages existence of the full multiplier family without any saturation/fixed-raw-colour assumptions.
- This discharges the ordered multiplier choice in the witness automorphism; the vertex-coordinate bijection and extensions of partial automorphisms remain OPEN.

## 2026-10-17 — effective-colour preservation of candidate witness automorphisms

- `Valuations/ColourPreservingTransport.lean` proves that transport of witness vertices using σ, fibre bijections ρ_q and incidence multipliers m(q,r) preserves and reflects the witness E-relation. If the full affine skeleton equation (3.9) holds, the same map preserves ALL effective cross-part colours by equation (3.12).
- This combines the explicit target-part coordinate formula (3.11) with the verified noncommutative multiplier algebra, without a hidden finiteness or bijectivity hypothesis. Bijectivity of the witness-vertex map and extension of partial automorphisms are separate OPEN gates.

## 2026-10-17 — bijectivity of witness-coordinate transport

- `Valuations/TransportEquiv.lean` identifies the witness vertex type as a dependent sum of old E-class fibres and valuation functions. For ANY σ of witness parts and bijections ρ_q on old-label fibres, the target-part χ-transport (3.11) is built from explicit equivalences of coordinate function spaces and yields a total bijection of witness vertices.
- This removes bijectivity as an assumption in the candidate witness automorphism theorem; preservation of colours follows from the separately verified affine skeleton multiplier equation. Extending every old partial automorphism remains OPEN.

## 2026-10-17 — actual automorphisms of the effective valuation witness

- `Valuations/EffectiveAutomorphisms.lean` combines global affine multipliers, correct target-part χ transport, preservation of the effective geometry, and an explicitly invertible vertex transport into one genuine effective-witness automorphism theorem. For every witness-part permutation σ equipped with per-part old-label fibre bijections ρ, it constructs a total witness-vertex Equiv preserving/reflection E and every cross-part group colour.
- This is the effective automorphism-realization gate, NOT yet the EPPA extension theorem: constructing σ,ρ that extend arbitrary old partial automorphisms remains OPEN, along with raw-fibre colour lifts.

## 2026-10-17 — the complete effective EPPA witness is finite

- Valuations/WitnessFiniteness.lean constructs actual Fintype enumerations of both witness parts (V/E) × G^V and all witness vertices (q,x,χ), via the verified dependent-sum witness equivalence. For finite V and finite G the full witness is finite, including the empty-old-carrier case.
- This closes the finite-carrier component of effective witness E0; extending old partial automorphisms and selecting raw fibre labels remain OPEN.

## 2026-10-17 — effective valuation continuation (verified PRs #54–#58)

All claims in this section concern the **effective group-valued geometry**. They
do not establish ordinary EPPA for the full raw-coloured class, coherent EPPA,
or DLF. These changes were merged to `main` only after their Lean CI builds
and axiom audits succeeded.

- **PR #54** — `Valuations/TwistedPartPermutation.lean`: formula
  `σ(j,h)=(ι(j),h')`, `h'(π x)=L_j(x)h(x)` is an actual permutation,
  even for noncommutative `G`, with inverse and fibrewise old-label
  equivalences. Its induced witness automorphism sends the old-label
  coordinate to `π x`. Neutral valuations remain neutral whenever the
  corresponding twist `L_j` is pointwise 1.
- **PR #55** — `Valuations/PrescribedMultiplierAutomorphisms.lean`:
  an arbitrary **chosen** ordered multiplier family `m(q,r)` satisfying
  affine skeleton equation (3.9) gives a genuine vertex equivalence,
  preserving/reflecting E, fixing every effective cross-part colour,
  and obeying the exact target-incidence law (3.11). Importantly this
  does **not** force the previously used canonical choice `m=1` on
  auxiliary ordered pairs.
- **PR #56** — `Algebra/ConstrainedWitnessMultipliers.lean`:
  distinguish witness parts by `P`; prescribe `a(q,r)` for *all*
  different target parts `r` when `P(q)`. If equation (3.15)
  holds on `P×P`, complete the prescribed data to a multiplier
  family satisfying (3.9) on every ordered pair. Mixed pairs use the
  forced affine reverse (3.10), unconstrained pairs use the verified
  order-based choice. The prescribed values survive exactly.
- **PR #57** — `Valuations/PrescribedAutomorphism.lean`:
  assemble #55 and #56 into one actual automorphism preserving E and
  every effective cross-colour, with the literal incidence equation
  `λ_(T X)(σ r)=a(q,r) λ_X(r)` when the source `q` belongs to `P`.
  A reversed-inequality Lean type error found by CI was corrected
  transparently and the final build passed.
- **PR #58** — `Algebra/AnchoredPartialGauge.lean`:
  equal bipartite effective matrices with nonempty left/right anchors
  determine the explicit unique source multipliers
  `u=a'(x₀)a(x₀)⁻¹` and `v=b'(y₀)b(y₀)⁻¹`. These satisfy the
  coordinate identities (3.14) and the precise noncommutative affine
  compatibility law (3.15), through the existing gauge converse.

**Current authoritative E0 status.** The finite two-layer witness,
the effective old embedding, actual witness automorphisms, compatible
multiplier completion, and anchored gauge multiplier algebra are now
machine checked. The headline **effective EPPA extension theorem is
still OPEN**: for an arbitrary typed old partial automorphism `p`,
formalize the partial injection of old E-classes, extend it to a
permutation of all E-classes, extend `p` to a class-respecting
bijection of old vertices after equal-size padding, construct the
twists `L_{x,j}` from (3.16), establish the required compatibility
of the prescribed multipliers, and finally show that the selected
automorphism sends **every** old vertex in `dom(p)` to its prescribed
old copy in `ran(p)`.

**Other major gates.** The ordinary full raw-colour EPPA theorem
still needs the finite affine residual code and raw-fibre cover
(R0/R1), followed by its individual partial-map lift. Global
finite SAP remains open at the final filtration/pasting stage despite
the verified literal and relative one-point SAP results. Coherent
EPPA, the fixed-cover group action, and relative DLF are separate
later gates; individual extensions do not imply a coherent lift.


## 2026-10-18 — certified E0 checkpoint through PR #72 (supersedes earlier E0 checkpoint)

The statements below are **individual checked Lean gates, NOT yet the
effective EPPA existence theorem**. Each named change passed full CI
(including the allowed-axiom audit) before merging into `main`.
The public repository is authoritative for their exact Lean types.

- **#59** `Valuations/OldVertexExtensionCriterion.lean` proves full
  extensionality of witness vertices from part, old label and all
  target-part cross-incidences. It gives the exact *conditional*
  old-vertex extension criterion for the prescribed automorphism.
- **#61** `Valuations/PartialPartPermutation.lean`: every finite
  partial E-isomorphism induces a partial injection on visited E-parts
  which extends to a permutation of the entire quotient, including
  empty partial domains.
- **#62** `Valuations/UniformFibrePermutation.lean`: a partial real
  injection on a uniformly indexed carrier `I × U` extends to an
  actual permutation of real labels, respecting a chosen permutation
  of `I`, provided the common fibre `U` is finite.
- **#63** `Structure/UniformPadding.lean`: explicit effective
  equal-size padding `(V/E) × V` with old embedding
  `x ↦ ([x],x)`. Exact E and all original cross-part F-colours
  are preserved; the padded geometry is valid for arbitrary affine
  reversal, nonabelian G and even empty V.
- **#64** `Valuations/OldPartialTwists.lean`: defines the literal
  old partial-domain twists `L_(x,j)` of (3.16), proves that (3.14)
  yields the desired incidence transport for EVERY target j, and
  instantiates the actual twisted valuation permutation (3.17).
- **#65** `Valuations/PaddedPartialPermutations.lean`: combines the
  finite quotient permutation and padded real-fibre permutation to
  extend any injective partial E-map of the *original* geometry as
  an E-preserving total real-label permutation on the padded carrier.
- **#66** `Structure/PaddedQuotientEquiv.lean`: identifies the
  canonical quotient of the *padded* E-setoid with the original E
  quotient and transports permutations without type-level conflation.
- **#67** `Valuations/PaddedWitnessAutomorphism.lean`: constructs
  an ACTUAL finite colour-preserving effective-witness automorphism
  after padding from the real/part permutations and any twist family
  trivial on visited old classes. Old vertices have the requested
  target **old-label and neutral witness-part coordinates**, but
  equality of full witness vertices is NOT claimed.
- **#69** `Algebra/PartialGaugeFamilies.lean`: one simultaneous,
  anchored noncommutative affine multiplier family for every pair
  of visited E-indices. Proves (3.14) and (3.15) under explicit
  indexed-gauge matrix preservation and self-gauge normalization,
  including the diagonal and empty-domain cases.
- **#70** `Valuations/PaddedGaugeDiagonal.lean`: confirms the
  padding has same-part dummy F=1 and that its canonical gauge
  satisfies `a_(x,[x])=1`. Also verifies incidence at a different
  blown-up witness part with the SAME old E-index, needed when
  i=j in (3.16)–(3.19). This replaces the mathematically identical,
  CI-green but merge-conflicted #68.
- **#71** `Valuations/PartialGaugeFromGeometry.lean`: removes the
  abstract matrix-equation assumption in #69. From an ACTUAL old
  partial map preserving/reflection E and preserving true group-valued
  F on all cross-pairs, together with the quotient permutation and
  normal same-part dummy F=1, constructs one family m(i,j)
  satisfying (3.14), (3.15), and m(i,i)=1.
- **#72** `Valuations/PaddedPartialIsomorphism.lean`: transports an
  actual partial E/F-isomorphism of the original effective structure
  to the literal old-image subtype of the uniform padded geometry,
  preserving/reflection E and preserving every cross-part effective
  colour; the transported map is injective whenever the old one is.

**Exact E0 assembly still OPEN.** For a partial effective
automorphism p of arbitrary finite A, put B₀ equal to the verified
uniform padding. First use #72 to get a literal partial
E/F-isomorphism of B₀. Apply #65/#66 to its class-respecting real
permutations and #70/#71 to get its concrete multipliers. Define
L by #64, define σ and fibre maps ρ by #54 and #66, prescribe the
multipliers on visited *neutral* witness parts by (3.19), and prove
that (3.15) implies compatibility on their pairwise witness-skeleton
edges, via the neutral-to-neutral skeleton equation (3.4).
Then use #57/#59 together with the target-part incidence identity
to show the resulting **single actual witness automorphism** sends
every distinguished old vertex of dom(p) to its prescribed entire
old witness vertex, not merely to one with the right E-part/old label.
Only after closing that theorem, finite witness and exact old
embedding APIs are to be packaged into ordinary effective EPPA.

**Other gates remain OPEN.** Raw fibre coding and raw EPPA lifts
(R0/R1), general finite SAP iteration, fixed-cover group actions,
coherent EPPA classification, and relative DLF classification have
not been obtained from these E0 increments. In particular, neither
an individual automorphism extension nor the existence of all such
extensions implies a coherent groupoid functor.


## 2026-10-18 — effective EPPA theorem verified (PRs #75–#77)

This section supersedes the earlier statement that the effective E0
assembly is open. **Effective EPPA is now fully verified in explicit
group-valued-geometry semantics.** This does NOT claim the typed
`AllThoseEPPA.Structure.IsEPPAWitness` API bridge or ordinary
EPPA for arbitrary raw colour fibres.

- **#75** `Valuations/NeutralMultiplierCompatibility.lean`: formalizes
  the visited neutral witness parts and literal prescribed family
  a(q,r)=m(q.1,r.1). Verifies that the old noncommutative affine
  identity (3.15), neutral-to-neutral skeleton preservation (3.4),
  and twists trivial on visited parts imply the precise P×P
  compatibility needed for the prescribed witness automorphism.
- **#76** `Valuations/TwistedOldVertexExtension.lean`:
  `exists_twistedWitnessAutomorphism_extending_old` proves that
  the explicit twists (3.16), blown-up permutation (3.17)–(3.18),
  prescribed multipliers (3.19) and fibre maps give one **actual**
  witness automorphism preserving E and ALL cross-part effective
  colours and satisfying `T(oldWitnessVertex x)=oldWitnessVertex(p x)`
  for every domain vertex x. All χ-coordinates are matched
  exactly, not just its old label and neutral witness part. This
  theorem accepts the old multipliers and permutations as
  hypotheses; #74 supplies these after padding.
- **#77** `Valuations/EffectiveEPPA.lean`:
  **`EffectiveGeometry.finite_effectiveEPPA_witness`** is the
  unconditional finite effective EPPA construction for EVERY finite
  old `EffectiveGeometry s V` and finite group `G`.
  The same fixed two-layer witness of the verified padded geometry
  and one fixed skeleton K are chosen *before* the partial map.
  The proof certifies finite witness carrier, injective old
  embedding, exact E-preservation/reflection, all old cross-part
  group colours, and extension of EVERY injective partial old
  E/F-isomorphism by an actual equivalence of the witness carrier
  preserving/reflection E and all cross-part F-colours.
  Uses #74 and #76 with no external padding/equal-class-size or
  group commutativity/recentering conditions; empty V is included.

**Scope check against the manuscript.** These theorems establish
the mathematics of Theorem "Effective EPPA" (the effective reduct
of K(G,s,id_G)) with same-part F-values treated as irrelevant
dummy data, as prescribed in the manuscript. The current
conclusion is stated for `EffectiveGeometry` rather than the
upstream generic binary-relational `Structure.IsEPPAWitness`:
bridging that API is useful for downstream consumers, but is
NOT a missing mathematical extension of the effective witness.
It must not be confused with ordinary EPPA for raw fibres
`phi : C ↠ G` unless phi is injective.

**Remaining major work.** R0 finite affine residual code,
R1 finite raw-fibre cover with exact old embedding and individual
automorphism lifts, then unconditional raw EPPA; separate generic
finite SAP filtration/iteration, coherent EPPA and relative DLF
group-action/cover results. A raw-fibre cover is not obtained by
simply forgetting the effective colours or choosing arbitrary
raw preimages. Explicit automorphism lifts are essential.


## 2026-10-18 — UNCONDITIONAL ordinary raw EPPA verified (PRs #103, #108, #111, #112)

**This is the authoritative current status of ordinary EPPA.** It
supersedes the historical E0/R0/R1 `OPEN` checkpoints above, which
recorded earlier stages of construction. Each of the named theorems
was merged only after passing the full Lean build and axiom audit,
allowing `propext`, `Classical.choice`, and `Quot.sound` only.

- **PR #77** `EffectiveGeometry.finite_effectiveEPPA_witness`:
  one fixed finite explicit two-layer effective group-valued witness,
  induced old embedding, and extension of EVERY partial effective
  E/F-isomorphism by a genuine automorphism.
- **PR #103** `Algebra/FiniteAffineResidualCode.lean`:
  `exists_universalAffineResidualCode`, with the **literal finite**
  coefficient group `(C → ZMod 4) × ZMod 2`. For every finite raw
  datum, the code provides typed fibre encoders/decoders, exact
  sections, and both affine-reversal equations (3.20). Handles
  fixed-point-free reversal fibres without requiring `s(1)=1` or
  commutativity of the effective group.
- **PR #108** `Structure/RawCoverSectionLifts.lean`:
  the fixed finite raw cover, its induced old raw embedding obtained
  from the sections (3.26) and interpolation (3.27), and EVERY
  prescribed raw partial-map lift whenever the underlying effective
  map extends; all raw relations and the complete old valuations
  are preserved literally.
- **PR #111** `Structure/RawEPPA.lean`:
  **`RawRectanglePresentation.finite_rawEPPA_witness`**, full
  unconditional ordinary raw EPPA for ANY finite functional
  R1--R3 presentation. The same finite witness and embedding are
  fixed before the partial map. A total permutation preserving
  E and each raw `P_c` extends every injective partial old map
  preserving/reflection of E and every ordered raw colour.
- **PR #112** `Structure/RelationalRawEPPA.lean`:
  **`IsRectangleStructure.finite_relationalRawEPPA_witness`**
  transfers this result to every actual finite member of the
  original binary relational class `K(G,s,phi)`, proving a
  finite literal raw witness, exact induced embedding, and
  extension of all partial raw automorphisms. No assumption of
  equal E-part sizes, special self-reversing colours, or singleton
  raw fibres is introduced.

**Exact scope.** The central ordinary EPPA result of the manuscript
is now machine-checked in the original relational language. The
theorem presently exposes its old embedding as an injective function
with explicit relation-preservation/reflection and its extensions
as total permutations with exact relation-preservation/reflection.
The optional *generic typed API* wrappers
`AllThoseEPPA.Structure.Embedding`,
`AllThoseEPPA.Structure.Automorphism`, and
`AllThoseEPPA.Structure.IsEPPAWitness`
are being formalized in PRs #113–#115 and must pass CI separately.
The typed wrapper is API integration, not a missing mathematical
proof of ordinary EPPA.

**Still open as independent theorems:** coherent EPPA (simultaneously
choosing composition-compatible lifts), the fixed-cover group-action
and relative DLF criteria, and general finite SAP by iteration of
the verified one-point SAP. No implication from ordinary EPPA to
coherent EPPA is presumed. The functional `RawDatum` hypotheses
(and the action conventions) must continue to be audited against
the article and its stated class definitions.


## 2026-10-18 — coherent and DLF frontier after verified PRs #118–#128

**Ordinary raw EPPA is DONE**, including the typed upstream
`AllThoseEPPA.Structure.IsEPPAWitness` API (merged PR #119).
The following coherent/DLF work is mathematically distinct.
A simultaneous lift of one finite group H of global automorphisms
is not, by itself, a coherent groupoid assignment for all partial
isomorphisms.

### Verified gates in main

- **#118**: the swapped-raw-pair obstruction yields a congruence-orbit
  restriction on possible reversal-good effective colours.
- **#120**: an involutive extension of a prescribed old
  transposition forces the corresponding congruence-good raw fibre
  condition. These are necessary-obstruction components, NOT the
  complete negative coherent-EPPA/relative-DLF classification.
- **#121** `Structure/RawCoverPotentialCocycle.lean`:
  the additive potential correction satisfies exact telescoping
  and composition laws (4.9)–(4.10).
- **#122** `Structure/RawCoverPotentialAutomorphisms.lean`:
  invariant residual potentials yield actual automorphisms of one
  fixed raw-coloured cover, preserving every literal P_c relation.
- **#123** `Structure/RawCoverRelativePotentials.lean`:
  finite relative interpolation (4.8), with ZERO outgoing rows on
  a prescribed old subset and the exact target residual matrix on
  all cross-part pairs.
- **#124** `Structure/RawCoverPotentialGroupAction.lean`:
  a genuine group homomorphism H→Perm(raw cover) from an invariant
  residual matrix, including strict preservation of old zero
  sections where the old subset is H-invariant.
- **#125**: reversal-compatible selection of raw representatives
  on arbitrary finite involutive effective-coloured orbit sets,
  assuming a self-reversing raw representative whenever an orbit
  is fixed by reversal.
- **#127**: extension of prescribed old raw colours on a
  reversal-stable subset of those orbit sets, with strict
  agreement and compatibility on every remaining orbit.
- **#128** `Structure/RawCoverFixedGroupLift.lean`:
  the CONDITIONAL fixed finite-cover action, with a homomorphic
  H-lift and exact action on prescribed old zero-section vertices,
  given one H-invariant reversal-compatible residual matrix r
  agreeing with the baseline b on old-old cross-part pairs.

Each listed merged result passed Lean CI and the allowed-axiom
audit. The canonical source remains the actual Lean declaration,
not this prose summary.

### Still open

1. Instantiate the abstract H-orbit raw-colour construction on
   the actual ordered cross-part edges of an effective geometry,
   deriving the safety condition from the manuscript's
   endpoint-interchange hypothesis. The group-orbit quotient
   proof was originally submitted in #126 and is being rebased
   and corrected in #131.
2. Convert that invariant raw colouring into a single invariant
   affine residual matrix, with the EXACT old baseline values.
   The algebraic conversion is under CI in #129; a canonical
   proof-independent global raw encoder from typed fibre
   sections is under CI in #130.
3. Apply the verified finite-cover group lift to the particular
   effective valuation witness/group action required by the
   POSITIVE coherent theorem. Verify the exact old embeddings,
   compositions and all partial-isomorphism groupoid identities.
4. Prove all necessary NEGATIVE and positive classification
   implications for coherent EPPA and relative DLF; the earlier
   group-congruence obstruction lemmas are only components.
5. Complete the general finite strong-amalgamation iteration
   from the existing one-point SAP infrastructure.

**Scope warning.** Even an actual H→Aut(cover) homomorphism for
every individually given H is weaker than a globally coherent
choice of extensions for the relevant partial-isomorphism
groupoid. No such implication is used without a separate theorem.


## 2026-10-18 — certified group-action gates and fixed-baseline frontier

This checkpoint supersedes the historical *coherent / DLF frontier*
section above. **The ordinary raw EPPA theorem and upstream typed
EPPA API remain DONE. Coherent EPPA and the relative DLF classification
are still OPEN.** The mathematical statements are those in the actual
Lean files; these notes are a status ledger, not additional axioms.

### Certified relative group-action infrastructure

- **#131** transports reversal-safe invariant raw-colour choices on
  abstract finite directed-edge H-sets (rebased from an earlier PR).
- **#133–#134** supply the canonical global affine raw encoder and
  turn an H-invariant reversal-compatible raw edge colouring into
  a literal H-invariant additive residual matrix.
- **#137** extends *prescribed* H-invariant old raw colours on an
  H- and reversal-stable subset of an abstract directed-edge set.
  Safety is needed only for orbits disjoint from the prescribed part.
- **#138** chooses one reversal-compatible affine baseline extending
  prescribed old-old cross-edge references.
- **#139** constructs a homomorphic H-action on a finite raw cover
  with H-invariant old zero-section points and correct prescribed
  old references, given a full H-invariant raw colouring. In this
  theorem the baseline is chosen **after H and its old subset**.
- **#140** specializes abstract orbit selection to the ACTUAL finite
  directed cross-pair subtype of an effective E/F geometry and the
  induced H-action. The safety hypothesis is an actual H-element
  interchanging both endpoints of a cross-E pair; it need not have
  order two.
- **#141** combines #140, #134 and #128: every endpoint-swap-safe
  effective H-action lifts homomorphically to a single finite literal
  raw-colour cover, with no prescribed old subset (S=empty).
- **#145** constructs a baseline b ONCE from all old raw colours
  on a global old subset S0, so the very same b works for every
  later S ⊆ S0 (in particular S=j(D) for different induced D).

PRs #140 and #141 passed full Lean CI/allowed-axiom audit and were
merged into main, superseding historically conflicted #135/#136.

### Further certified gates and current frontier

- **#142 (merged, CI-green)** extends prescribed old H-invariant raw
  colours on actual directed cross-E pairs, requiring safe reversal
  orbits only outside the old subset.
- **#143 (merged, CI-green)** produces a homomorphic H-action on a
  finite raw cover with literal preservation of old zero-section
  vertices and raw edge colours.
- **#145 (merged, CI-green)** fixes one baseline from the WHOLE old
  copy and retains the prescribed data for every later S ⊆ S₀.
- **#147 (merged, CI-green)** rebases the proof of the fixed-baseline
  H-lift onto current main. The raw cover is chosen before H and S.
- **#148 (merged, CI-green)** strengthens this to a single baseline
  chosen before quantifying over ALL later group types H, safe actions
  and invariant old subsets S.

Thus the relative fixed-cover group-action lemma is verified, subject
to the exact endpoint-swap safety hypothesis. The remaining burden
is to construct these safe effective H-actions in the prescribed
valuation witness and verify coherent groupoid assembly.

### Why the fixed baseline matters

The manuscript's fixed-cover lemma chooses the raw cover and old
embedding before the induced substructure D and its group Aut(D).
Choosing a NEW baseline or a NEW raw cover for each H is NOT
sufficient for coherent-EPPA assembly. The verified PR #148 combines the
baseline fixed in #145 with the rebased group lift #147.
Safe effective actions for the actual valuation witness and
coherent groupoid extension identities remain major obligations.
This is distinct from the still-open coherent groupoid assembly,
negative classification and semi-coherent/DLF forcing theorems.

The fixed-cover potential lift currently establishes the correct
group homomorphism using potential corrections; it need not literally
be the pure index-relabeling action (3.29) from the particular
paper presentation. Its semantic action on E and every P_c and on
old zero-section points is the verified output.

## 2026-10-19 — merged coherent-action infrastructure checkpoint

**Authoritative certified base:** merged into public `main` with full Lean
build and allowed-axiom audit, PRs **#158, #161, #162, #163, #164, #165, #166**.
Ordinary EPPA and typed `AllThoseEPPA` integration had already been verified
on `main`. No new `sorry` or custom axiom is used here.

### Fixed-fibre and strict H-actions

- **#158:** `exists_factorialFibreGroupAction` proves that an arbitrary
  H-action on a nonempty old fibre S extends homomorphically along **any
  fixed injection** into `Fin(|A|!)`. The padded fibre carrier is fixed
  before S and H; the multiplication coordinate construction respects
  the prescribed injection exactly. This is a cardinality/action gate,
  not an action on the complete semigeneric witness.
- **#161:** `exists_subsingletonEffectiveWitnessGroupLift` builds an
  honest homomorphism H→Perm of the whole two-layer effective valuation
  witness when G is subsingleton, assuming compatible actions on real
  labels and quotient E-classes. It preserves the whole effective E/F
  geometry and the exact distinguished old vertices.
- **#162:** `exists_paddedSubsingletonWitnessGroupLift` transports
  compatible relative group actions from an induced subset S onto the
  one fixed padded carrier `(V/E) × V`, then invokes #161. Old-class
  equivariance is required on S, not on all old V.
- **#163:** `exists_compatibleSubsetAndQuotientActions` removes those
  extra input actions: any H→Perm(S) preserving the restricted E-relation
  induces a strict H-action on *occupied* E-class indices (extended by
  identity on unoccupied classes) and a strict old-label action (fixed
  outside S). The old-label action is **not claimed** to preserve the
  original E globally.
- **#164:** `exists_inducedSubsingletonWitnessGroupLift` combines #162
  and #163. For ANY S⊆V, group H and E-preserving H-action on S, the
  **same preselected effective valuation witness** has a genuine
  E/F-preserving H-action extending S. The skeleton and padded witness
  are fixed BEFORE S and H. This is a complete effective H-action gate
  for the trivial G sector, not a coherent raw-cover result.
- **#165:** `projectedFlippedPair_hasSelfReversingRawColour` proves
  a reusable flip-safety transfer: if a lifted pair exchanged by h
  projects H-equivariantly to an actual old cross-E pair and old raw
  colours are H-invariant, the projected colour is self-reversing.
  This holds for ANY element h of H, not only involutions.
- **#166:** `finite_subsingletonEffectiveEPPA_and_allGroupLifts`
  packages the verified effective EPPA witness and #164 into **one
  finite, preselected E/F witness**. It embeds old E/F and extends
  every old partial E/F-isomorphism individually, while every induced
  S and every compatible H-action extends homomorphically on the
  SAME finite witness. Neither the skeleton nor the old embedding
  depends on S or H. This is still weaker than raw coherent EPPA.

### Mathematical guardrail: effective action ≠ raw-colour safety

Do **not** feed the action of #164 blindly into the fixed-baseline raw
lift #148. In the uniform padded product `(V/E) × V`, a nontrivial
H-element exchanging occupied class indices i,j while fixing an
outside-S old label x can artificially exchange **(i,x)** with
**(j,x)**. That is a cross-part pair but does not project to an
actual old cross-part pair. There need not be a self-reversing raw
colour of its effective group colour. This invalidates any attempted
claim that all swaps in #164 automatically satisfy #148's safety
hypothesis. No such claim is made in the proved Lean files.

A correct positive raw-coherent action will need either an additional
H-equivariant fibre-copying/phase construction that removes these
artificial flips, or another rigorous orbit-by-orbit safety argument.
The factorial divisibility/action gate #158 may be useful when
replicating the actual occupied old fibres, rather than copying a
single global unrelated old label into every padded E-class.

### Remaining obligations (not Lean-proved)

1. Construct flip-safe **fixed-witness** H-actions for all relevant
   induced S and H, not merely E/F-preserving group actions. Handle the
   nontrivial-G affine/noncommutative sector with the existing cocycle
   kernel; do not impose global S saturation in the DLF branch.
2. Combine safe actions with the existing H2/H3 fixed raw baseline
   lemmas (#145/#147/#148) for **one** fixed raw witness; for the
   positive coherent branch use global congruence saturation only
   where genuinely necessary.
3. Formalize C0 coherent groupoid assembly with exact domains,
   equivalence of partial isomorphisms and composition. Independent
   group homomorphisms for each S are NOT already a functor.
4. Prove the remaining coherent-negative implications, the relative
   safe group construction and DLF classification, and the full finite
   strong-amalgamation iteration. Keep the private mathematical v0.8
   paper and this public Lean repository separate.

**Certified interface:** PR #166 (merged with full CI/allowed-axiom
check) is the recommended single theorem for reusing the finite effective
EPPA witness together with all relative H-action extensions when G=1.
The additional raw-colour safety/groupoid proof obligations above are
unchanged.

## 2026-10-19 — G=1 fixed safe actions and one raw-cover checkpoint

**Verified and merged, full public Lean CI plus allowed-axiom audit:**
PRs #168–#178, #179–#190 (their exact declarations, not their PR
descriptions, are authoritative).

- **#168–#172:** strict group action on actual replicated old fibres,
  transported to one fixed carrier. On occupied parts there is an
  H-equivariant Option-valued projection to real old vertices;
  unoccupied part indices are fixed. Swapped cross-E pairs therefore
  have self-reversing raw representatives, even when the swapping
  group element is not an involution.
- **#173–#178:** assemble one exact classwise coding
  `Fin M ≃ S_i × Fin(t_i)`, preserving the prescribed old
  copy-zero injection. The resulting H→Perm of `I×Fin M`
  genuinely preserves effective E/F, acts literally on all
  old vertices, and has the required raw flip-safety.
- **#175, #179:** class sizes are H-invariant; with a fixed
  `M=|A|!` every later nonempty occupied fibre has positive
  multiplicity `t_i=M/|S_i|`, satisfies `|S_i|*t_i=M`,
  and has `t_(hi)=t_i`. Its numerical size is expressed by
  the canonical instance-independent `oldClassFibreCard`.
- **#176:** induced quotient H-actions fix every unused E-class
  index. This explicit property is essential, not decorative.
- **#180–#183:** there is an actual fixed G=1 effective geometry
  on `(A/E)×Fin M` and a single old injection chosen before
  any induced subgroup. Every individual partial effective
  isomorphism extends on this SAME carrier; genuine effective
  induced-subtype geometry is available.
- **#184–#185, #188–#190:** original raw-colour data yield
  a fixed total old reference, which respects old partial
  automorphisms. If the baseline encodes these actual old colours,
  the old zero section is an EXACT induced raw embedding and
  individual raw partial maps lift on this SAME cover.
- **#187:** a single baseline is chosen before ALL later partial
  maps and safe H-actions; it supports BOTH individual zero-section
  extensions and homomorphic safe-group raw-cover lifts. This is
  a key common-witness quantifier-order gate.
- **#186:** the normal form `Phi(i,j,f)=beta_j rho(f) beta_i⁻¹`
  has identity, composition and old-vertex extension laws.
  It is an algebraic groupoid gate, not yet a complete typed
  `AllThoseEPPA.Structure.CoherentExtension` construction.

**Prepared but not counted as merged/certified here:**
#191 explicitly returns the old-old baseline encoding in the
common-cover theorem; #192 bridges canonical old-class cardinality
with explicitly supplied Fintype structures; stacked #193 eliminates
multiplicity assumptions from the safe fixed-carrier H-action; #194
derives invariant total old raw references from actual old H-actions.

**Remaining coherent-positive G=1 assembly:** for all induced
S⊆A and H=Aut(S), construct H-safe actions on the SAME fixed
effective carrier from #176/#179/#181/#192/#193, instantiate one
finite raw coefficient code and one fixed old-reference baseline
(#185/#187/#188/#189/#190/#191/#194), combine with individual
effective EPPA #182, and complete the **exact typed groupoid**
representatives/connector construction beyond the abstract #186.

Do NOT infer coherent EPPA from separate group actions without that
last groupoid theorem. The nontrivial G coherent sector, negative
classification, relative safe-phase DLF and its converse, and
unrestricted finite SAP iteration are still open. Never use global
congruence saturation in the weaker DLF branch. Private manuscript
repo has no CI.

## 2026-10-20 — positive G=1 typed coherent EPPA certified

**Verified by full public Lean build and permitted-axiom audit:**
`RawRectanglePresentation.finite_typedCoherentEPPA_witness` in
`SemigenericEPPA/Bridge/GOneTypedCoherentEPPA.lean`, PR #227,
merged as `fc35a357ad05f05eef16a9575f4194daef19e00f`.

For any finite original raw rectangle presentation with finite
raw colour type C and subsingleton finite effective group G, there
is a finite actual raw witness, a typed embedding of the original
binary R1--R3 relational structure, and one authentic upstream
`Structure.IsCoherentEPPAWitness` with exact Equivalent and
CoherentTriple laws. Its proof uses the CI-certified global raw
groupoid functor #222 and the typed converter #221. A single raw
carrier, old zero-section embedding, universal residual code and
baseline are selected before all partial maps, induced subgroups
and connectors. No HKN EPPA theorem is invoked.

**Still pending:** direct statement for arbitrary original
`IsRectangleStructure d A`, requiring the literal
`h.toRawPresentation.toStructure = A` roundtrip (#225) and final
original-relational wrapper (#228). Both remain under CI at this
checkpoint; do not report them as certified. Coherent nontrivial-G
cases, negative coherent classification, relative DLF and finite
SAP remain open.

## 2026-10-20 — actual relational G=1 coherent EPPA finished; nontrivial G frontier

**Verified in public GitHub Actions, including full Lean build and
allowed-axiom audit:**

- **PR #228** merges the human-facing original relational theorem
  `IsRectangleStructure.finite_relationalTypedCoherentEPPA_witness`
  from `SemigenericEPPA/Bridge/RelationalTypedCoherentEPPA.lean`.
  For every finite ORIGINAL `Structure (rectangleLanguage C) V`
  satisfying the complete literal `IsRectangleStructure d A` with
  subsingleton effective G, it gives one FINITE genuine coherent
  EPPA witness, actual upstream typed embedding and
  `Structure.IsCoherentEPPAWitness (rectangleTrivialAction C)`.
  The theorem needs no initially supplied raw function or auxiliary
  old embedding. This supersedes the earlier checkpoint's statement
  that the relational wrapper was pending.
- **PR #241** proves the original-language exact partial
  involution on the old tripleton E-part in the genuine 3+1 gadget,
  irrespective of its three raw cross-colours.
- **PR #243** proves that coherent typed witnesses for all genuine
  2+1 old gadgets based at self-reversing raw colours force
  `d.IsCongruenceSaturated`. This includes the case where the
  good set is empty; it does not assert nonemptiness.
- **PR #239** certifies the negative geometry of the 3+1
  obstruction: a total raw-colour-preserving involution with
  old effective profile `delta,1,1` for `delta≠1`
  forces a genuinely self-reversing raw colour. The alternative
  (new point in the old singleton's E-part) contradicts the
  effective rectangle equation.
- **PR #245** proves the positive affine congruence/gauge
  transport law
  `congruence s (s a * (s aStar)⁻¹) (s aStar * M * aStar)
    = s a * M * a`
  for arbitrary affine anti-involution on a nonabelian G.
  Thus global congruence saturation transports good raw
  representatives across all such effective gauge colours.
  This key safety step was formalized WITHOUT assuming
  `s 1 = 1` or recentering the group.

**Not yet Lean certified at this checkpoint:** #242 upgrades
the certified 3+1 geometry to a TRUE typed coherent-EPPA
obstruction from the actual old partial involution; #244
combines 2+1 saturation and 3+1 nonemptiness into the
necessary dichotomy `Subsingleton G ∨
(S.Nonempty ∧ d.IsCongruenceSaturated)`; #246 specializes
that dichotomy to coherent EPPA of EVERY finite old raw
presentation; #247 generalizes safe occupied old projections
to effective colours agreeing only up to congruence orbit.

The major remaining positive theorem for nontrivial effective
G is the simultaneous, fixed-witness H-action with multipliers
`M^h_{ij}`, references `L^h_{x,j}`, cocycle identities
and the orbit safety condition. Many underlying multiplier,
valuation and homomorphic raw-cover gates are already certified,
but this actual nontrivial-G construction is NOT complete.
The relative DLF criterion and finite SAP remain separate
open formalization objectives. DLF must retain the weaker
"one complete good congruence orbit" hypothesis, not silently
require saturation of all good orbits.

As always, do not infer a certified theorem from an open PR:
check the current public main commit and GitHub Actions
full CI/axiom audit before reporting completion.


## 2026-10-20 — verified coherent-negative classification and positive algebra through PR #254

**Authority:** current merged public `main` and full GitHub Actions
build/allowed-axiom audit; historical sections above describe earlier
checkpoints and MUST NOT be interpreted as current OPEN statuses.

### Now complete and merged

- **PR #228:** `IsRectangleStructure.finite_relationalTypedCoherentEPPA_witness`
  proves actual finite original-language typed coherent EPPA for G=1.
- **PRs #242, #244, #246:** the negative obstruction is now FULLY
  upgraded from geometric gadgets to typed coherent witnesses. The
  original-language necessary theorem is
  `RawDatum.necessaryCoherentCondition_of_allFiniteRawPresentations`
  in `Bridge/CoherentFiniteRawClassNecessity.lean`, proving
  `Subsingleton G ∨ (d.selfReverseEffective.Nonempty ∧ d.IsCongruenceSaturated)`
  from coherent EPPA of the full finite class. The old notes saying
  these PRs are pending have been superseded.
- **PRs #249–#251 and #253:** canonical occupied H-indexed gauge
  multipliers come from actual old affine rank-one matrices; their
  strict noncommutative cocycle and neutral all-index completion are
  formalized. Literal matrix invariance follows from real old
  effective H-automorphism equations, not from a hidden assumption.
- **PR #252:** one fixed reversal-invariant effective default obtained
  from a genuinely self-reversing raw colour completes the occupied
  skeleton, including all affine multiplier equations and arbitrary
  nonabelian G; no assumption `s 1 = 1`.
- **PRs #245, #247, #254:** exact common-middle congruence transfer,
  an equivariant occupied old projection, and **swapped-only** orbit
  flip-safety for all H-elements (not just order-two elements).

### Immediate positive nontrivial-G spine

1. Obtain complete multipliers and a fixed good skeleton from genuine
   old indexed H-actions; preserve the quantifier order that fixes the
   witness/skeleton before any induced subset or H-action.
2. Use the actual witness-coordinate permutation to prove the exact
   swapped cross-pair common-middle formula (manuscript (4.29)).
3. Construct the common full two-layer witness H-action, including
   inhabited copied fibres, occupied and unused indices, old embedding,
   and all effective E/F colours. Combine the actual swap analysis with
   global congruence saturation to obtain raw reversal safety.
4. Lift all induced stabilizer H-actions homomorphically on ONE fixed
   raw-cover witness and reuse the already proved exact groupoid
   normalization/typed converter from the G=1 coherent proof.

The raw coherent groupoid assembly is already formalized; that does
not by itself prove the nontrivial-G uniform group-lift hypothesis.

**Submitted but not yet counted as verified at this checkpoint:**
PR #255 (fixed old-index good skeleton + old H multipliers from actual
invariance) and PR #256 (genuine swapped-witness formula) were opened
for CI review. Consult their latest Actions status; do NOT treat an
open PR or a green preparation step as proof completion.

**Other goals:** Relative DLF requires just one whole good congruence
orbit and a separate phase construction; the full strong-amalgamation
iteration and optional classification appendix are not finished.
