import SemigenericEPPA.Bridge.FiniteOriginalRelationalSaturatedEPPA
import SemigenericEPPA.Bridge.RelationalTypedCoherentEPPA
import SemigenericEPPA.Bridge.CoherentFiniteRawClassNecessity
import SemigenericEPPA.Bridge.NontrivialSaturatedTypedCoherentEPPA

/-!
# Full coherent-EPPA classification with explicit canonical witness universes

The mathematics has one exact criterion:
  G is trivial OR the good effective set is nonempty and
  invariant under the full affine congruence action.

At the Lean universe level, the explicit trivial-group witness has
vertex type in Type (max 0 v), while the nontrivial finite effective
witness has vertex type in Type (max u v), since valuations contain G.
These universes need not coincide.

Rather than identifying unrelated universes or silently transporting
CoherentExtension through an unproved type equivalence, the class
predicate below explicitly selects the appropriate witness universe
according to whether the effective group is subsingleton. This
is a technical formulation choice only: the original structures,
raw predicates, finite witnesses, and typed coherent extension
predicate remain EXACTLY the same.

Both the raw functional class and the genuine original relational
R1--R3 class are treated. The positive G=1 and nontrivial saturated
results are separately proved, as are the necessary 2+1 / 3+1
obstructions. Nothing about DLF or finite SAP is claimed here.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]

/-- Whole finite raw R1--R3 class has coherent EPPA with a witness
in the natural low universe when G is subsingleton and in the
natural full valuation universe otherwise. Both branches require
finite witnesses and actual upstream typed coherent extensions. -/
def RawDatum.HasFiniteRawCoherentEPPAInCanonicalUniverses
    (d : RawDatum G C) : Prop :=
  ∀ (V : Type) [Fintype V] (P : RawRectanglePresentation d V),
    (Subsingleton G →
      ∃ (W : Type (max 0 v))
        (Q : RawRectanglePresentation d W),
        Finite W ∧
        ∃ psi : Structure.Embedding (rectangleTrivialAction C)
            P.toStructure Q.toStructure,
          Structure.IsCoherentEPPAWitness
            (rectangleTrivialAction C) psi) ∧
    (¬ Subsingleton G →
      ∃ (W : Type (max u v))
        (Q : RawRectanglePresentation d W),
        Finite W ∧
        ∃ psi : Structure.Embedding (rectangleTrivialAction C)
            P.toStructure Q.toStructure,
          Structure.IsCoherentEPPAWitness
            (rectangleTrivialAction C) psi)

/-- The COMPLETE coherent EPPA classification of the finite
functional raw R1--R3 class, with honest witness-universe choices. -/
theorem RawDatum.hasFiniteRawCoherentEPPAInCanonicalUniverses_iff
    (d : RawDatum G C) :
    d.HasFiniteRawCoherentEPPAInCanonicalUniverses ↔
      Subsingleton G ∨
        (d.selfReverseEffective.Nonempty ∧ d.IsCongruenceSaturated) := by
  constructor
  · intro h
    by_cases hTriv : Subsingleton G
    · exact Or.inl hTriv
    · have hAll : ∀ (V : Type) [Fintype V]
          (P : RawRectanglePresentation d V),
          ∃ (W : Type (max u v))
            (Q : RawRectanglePresentation d W)
            (psi : Structure.Embedding (rectangleTrivialAction C)
              P.toStructure Q.toStructure),
            Structure.IsCoherentEPPAWitness
              (rectangleTrivialAction C) psi := by
        intro V _ P
        obtain ⟨W, Q, _hFinite, psi, hCoherent⟩ :=
          (h V P).2 hTriv
        exact ⟨W, Q, psi, hCoherent⟩
      have hNec :=
        d.necessaryCoherentCondition_of_allFiniteRawPresentations hAll
      exact Or.inr (hNec.resolve_left hTriv)
  · intro hCriterion V _ P
    constructor
    · intro hTriv
      letI : Subsingleton G := hTriv
      obtain ⟨hFinite, Q, psi, hCoherent⟩ :=
        P.finite_typedCoherentEPPA_witness
      exact ⟨GOneJointRawCarrier P, Q, hFinite, psi, hCoherent⟩
    · intro hNontriv
      obtain ⟨hGood, hSat⟩ :=
        hCriterion.resolve_left hNontriv
      obtain ⟨_j, Q, _R, K, J, hFinite, psi, hCoherent⟩ :=
        P.finite_typedCoherentEPPA_witness_of_saturated hGood hSat
      exact ⟨RawCoverVertex
          (EffectiveWitnessVertex Q.toEffectiveGeometry)
          (UniversalResidualCarrier C),
        rawCoverPresentation K.toEffectiveGeometry
          J.code J.baseline J.baseline_reverse,
        hFinite, psi, hCoherent⟩

/-- Same coherent class property in the ORIGINAL relational language
E and all R_c, not merely the convenient functional raw presentation. -/
def RawDatum.HasFiniteRelationalCoherentEPPAInCanonicalUniverses
    (d : RawDatum G C) : Prop :=
  ∀ (V : Type) [Fintype V]
      (A : Structure (rectangleLanguage C) V),
    IsRectangleStructure d A →
      (Subsingleton G →
        ∃ (W : Type (max 0 v))
          (Q : RawRectanglePresentation d W),
          Finite W ∧
          ∃ psi : Structure.Embedding (rectangleTrivialAction C)
              A Q.toStructure,
            Structure.IsCoherentEPPAWitness
              (rectangleTrivialAction C) psi) ∧
      (¬ Subsingleton G →
        ∃ (W : Type (max u v))
          (Q : RawRectanglePresentation d W),
          Finite W ∧
          ∃ psi : Structure.Embedding (rectangleTrivialAction C)
              A Q.toStructure,
            Structure.IsCoherentEPPAWitness
              (rectangleTrivialAction C) psi)

/-- The COMPLETE finite original relational R1--R3 coherent
EPPA classification, with the same honest universe convention
and finite typed original-language witnesses in every case. -/
theorem RawDatum.hasFiniteRelationalCoherentEPPAInCanonicalUniverses_iff
    (d : RawDatum G C) :
    d.HasFiniteRelationalCoherentEPPAInCanonicalUniverses ↔
      Subsingleton G ∨
        (d.selfReverseEffective.Nonempty ∧ d.IsCongruenceSaturated) := by
  constructor
  · intro h
    by_cases hTriv : Subsingleton G
    · exact Or.inl hTriv
    · have hAll : ∀ (V : Type) [Fintype V]
          (P : RawRectanglePresentation d V),
          ∃ (W : Type (max u v))
            (Q : RawRectanglePresentation d W)
            (psi : Structure.Embedding (rectangleTrivialAction C)
              P.toStructure Q.toStructure),
            Structure.IsCoherentEPPAWitness
              (rectangleTrivialAction C) psi := by
        intro V _ P
        obtain ⟨W, Q, _hFinite, psi, hCoherent⟩ :=
          (h V P.toStructure P.toStructure_isRectangleStructure).2 hTriv
        exact ⟨W, Q, psi, hCoherent⟩
      have hNec :=
        d.necessaryCoherentCondition_of_allFiniteRawPresentations hAll
      exact Or.inr (hNec.resolve_left hTriv)
  · intro hCriterion V _ A hA
    constructor
    · intro hTriv
      letI : Subsingleton G := hTriv
      obtain ⟨hFinite, Q, psi, hCoherent⟩ :=
        hA.finite_relationalTypedCoherentEPPA_witness
      exact ⟨hA.finiteRelationalCoherentCarrier,
        Q, hFinite, psi, hCoherent⟩
    · intro hNontriv
      obtain ⟨hGood, hSat⟩ :=
        hCriterion.resolve_left hNontriv
      obtain ⟨W, Q, hFinite, psi, hCoherent⟩ :=
        hA.finite_originalCoherentEPPA_of_saturated hGood hSat
      exact ⟨W, Q, hFinite, psi, hCoherent⟩

end SemigenericEPPA
