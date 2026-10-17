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
| G0 | finite affine reversal, `S`, cross-part colour type | CORE VERIFIED: affine reversal, raw datum, congruence G-action/S, exact cross-part language and R1–R3; main-theorem finiteness still to be imposed |
| G1 | recenter group at `g₀ ∈ S`, rank-one gauge, partial gauge transport | VERIFIED: origin equations, noncommutative rank-one, affine gauge equivalence (2.7), quotient-sorted gauge presentation (2.6) BOTH directions. OPEN: transported Group API and partial-map gauge transport |
| G2 | finite structures, exact induced embeddings, strong amalgamation | VERIFIED: R1–R3, heredity/embeddings, E-part strong one-point amalgam, old-old corner, same-old-part and fresh-part local cases, effective/raw completion bridge. OPEN: one global effective one-point amalgam plus arbitrary finite SAP/Fraïssé |
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

## 2026-10-17 — next SAP assembly step (design; NOT Lean-certified)

All relevant local matrix cases and both directions of the two-sorted gauge representation (2.6) are now Lean-certified. To complete G2, build **one global effective E-rectangle amalgam**, not another locally specified corner. The following is the intended construction to formalize:

1. For two one-point extensions of base D with E-equivalence, use the verified `combinedPartIndex` as a **surjective class-label map** on the strong carrier `V ⊕ Bool`, with labels `(Quotient E) ⊕ Bool`. Fresh labels distinguish the two genuinely new classes; an attached new point receives its old quotient label.
2. Introduce a *class-indexed* counterpart of `QuotientGauge`, indexed by these labels, or a quotient-index equivalence to the canonical imaginary sort of the amalgam. Then **every** legal skeleton/gauge assignment automatically yields the entire effective rectangle law via verified `QuotientGauge.toEffectiveGeometry`.
3. Choose representatives `rep(i) := Quotient.out i` of each OLD class. For distinct old i,j set `K_ij := D.F(rep(i),rep(j))` and let old λ-coordinates be `D.F(rep(j),a)`; for a new attached point use the corresponding left/right one-point effective F towards old anchors. Reconstruction/side-preservation follows from verified `EffectiveGeometry.anchored_factor` and the old-old forced-corner result.
4. For the newly created fresh label f, choose `K_(old,f)=1`, `K_(f,old)=s(1)`, and λ_(old a,f) = `s(F_side(old a,new f))`, λ_(fresh f,old)=1. This reproduces the required existing cross-colours in BOTH orientations, using the exact affine reversal. Unprescribed new–new edges may be chosen arbitrarily. For two fresh labels choose K in one direction and its s-reversal in the other.
5. PROVE the gauge assignment reproduces all old–old and old–new effective colours, using the exact quotient labels and the verified one-point geometry identities. The new–new colour is forced between two distinct old parts; same-old-part and fresh-singleton cases are already settled by independent Lean lemmas. Then use `EffectiveRawExtension.toStructure_isRectangleStructure` with the prescribed old-side raw edges and prove the two `AllThoseEPPA.Structure.Embedding` inclusions.
6. Only after a genuine one-point SAP theorem has been checked should one prove finite SAP by iterating one-point amalgams; Fraïssé limit and infinitude properties are later gates.

**Status warning:** none of steps 1–6 as a single assembled theorem is yet proved in Lean. `QuotientGauge` currently indexes by the canonical quotient, whereas the algorithm above describes quotient labels for an amalgam; bridging these types and proving side preservation is the principal remaining technical difficulty. This should not be confused with the HKN/valuation or coherent-EPPA stages, which remain OPEN.
