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


## 2026-10-17 — the abstract indexed-gauge automorphism criterion

- `Valuations/GaugeAutomorphisms.lean` states the exact σ,τ,m data of the effective witness automorphisms: a permutation of imaginary labels, a permutation of real vertices, the left gauge-coordinate multipliers, and the affine skeleton condition (3.9). It proves E is preserved and reflected and all cross-part effective colours are fixed.
- This gives the complete SUFFICIENCY direction of the effective automorphism criterion (2.8) and the algebra of (3.11–3.12), independent of the still-open construction of such permutations from partial automorphisms.
