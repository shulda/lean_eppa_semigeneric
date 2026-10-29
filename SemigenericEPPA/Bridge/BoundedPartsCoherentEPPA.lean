import SemigenericEPPA.Bridge.RelationalTypedCoherentEPPA
import SemigenericEPPA.Structure.PartQuotientCover

/-!
# Coherent EPPA for a fixed bound on the number of nonempty E-parts

The G=1 witness preserves the canonical quotient of E-classes.
Consequently a member with at most n nonempty parts gets a coherent
EPPA witness with at most n nonempty parts as well. This is a genuine
subclass theorem; the finite-n class is not a new unrestricted
group-valued RawDatum.

An injection of A/E into Fin n encodes n *possibly empty* labelled
parts. We impose NO new lower bound such as n ≥ 2 on the abstract
statement; the n ≥ 2 tournament corollary is a specialization.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {V : Type w}
variable {d : RawDatum G C}
variable {A : Structure (rectangleLanguage C) V}

namespace IsRectangleStructure

/-- There are at most n nonempty E-classes, witnessed by an injection
of the actual quotient A/E into Fin n (unused labels are permitted).
Unlike requiring exactly n nonempty parts, this is hereditary. -/
def HasAtMostNonemptyParts
    (h : IsRectangleStructure d A) (n : ℕ) : Prop :=
  ∃ label : PartQuotient h → Fin n, Function.Injective label

/-- An actual equivalence of E-part quotients transports an n-part
bound; no cardinality or choice assumptions are needed. -/
theorem hasAtMostNonemptyParts_of_partEquiv
    {W : Type w}
    {B : Structure (rectangleLanguage C) W}
    (hA : IsRectangleStructure d A)
    (hB : IsRectangleStructure d B)
    (n : ℕ) (e : PartQuotient hA ≃ PartQuotient hB)
    (hN : hA.HasAtMostNonemptyParts n) :
    hB.HasAtMostNonemptyParts n := by
  obtain ⟨label, hinj⟩ := hN
  exact ⟨fun q => label (e.symm q), hinj.comp e.symm.injective⟩

end IsRectangleStructure

namespace RawRectanglePresentation

variable {T : Type w} [Fintype T]

/-- The *same* original-language G=1 coherent witness stays inside
the full n-bounded sub-age for every n (in particular every n ≥ 2).
The bijection on actual part quotients is retained as an explicit
component of the final witness. -/
theorem finite_boundedPartsTypedCoherentEPPA_witness
    (P : RawRectanglePresentation d T) (n : ℕ)
    (hN : P.toStructure_isRectangleStructure.HasAtMostNonemptyParts n) :
    Finite (GOneJointRawCarrier P) ∧
    ∃ (Q : RawRectanglePresentation d (GOneJointRawCarrier P))
      (psiTyped : Structure.Embedding
        (rectangleTrivialAction C) P.toStructure Q.toStructure),
      Structure.IsCoherentEPPAWitness
        (rectangleTrivialAction C) psiTyped ∧
      Q.toStructure_isRectangleStructure.HasAtMostNonemptyParts n ∧
      ∃ partEquiv :
          PartQuotient P.toStructure_isRectangleStructure ≃
            PartQuotient Q.toStructure_isRectangleStructure,
        ∀ x : T,
          partEquiv (partClass P.toStructure_isRectangleStructure x) =
            partClass Q.toStructure_isRectangleStructure (psiTyped x) := by
  obtain ⟨hFin, Q, psiTyped, hCoherent, partEquiv, hPartMap⟩ :=
    P.finite_partPreservingTypedCoherentEPPA_witness
  refine ⟨hFin, Q, psiTyped, hCoherent, ?_, partEquiv, hPartMap⟩
  exact IsRectangleStructure.hasAtMostNonemptyParts_of_partEquiv
    P.toStructure_isRectangleStructure
    Q.toStructure_isRectangleStructure n partEquiv hN

end RawRectanglePresentation

/-- Original *relational* E/R_c class, not merely raw functional
presentations. A witness for each finite n-bounded original structure
also belongs to the n-bounded class, and coherent EPPA holds with
the actual induced map A/E -> B/E bijective. -/
theorem IsRectangleStructure.finite_boundedPartsRelationalCoherentEPPA_witness
    [Finite V] (h : IsRectangleStructure d A) (n : ℕ)
    (hN : h.HasAtMostNonemptyParts n) :
    Finite h.finiteRelationalCoherentCarrier ∧
    ∃ (Q : RawRectanglePresentation d h.finiteRelationalCoherentCarrier)
      (psiTyped : Structure.Embedding
        (rectangleTrivialAction C) A Q.toStructure),
      Structure.IsCoherentEPPAWitness
        (rectangleTrivialAction C) psiTyped ∧
      Q.toStructure_isRectangleStructure.HasAtMostNonemptyParts n ∧
      ∃ partEquiv :
          PartQuotient h ≃ PartQuotient Q.toStructure_isRectangleStructure,
        ∀ x : V, partEquiv (partClass h x) =
          partClass Q.toStructure_isRectangleStructure (psiTyped x) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hN' :
      h.toRawPresentation.toStructure_isRectangleStructure.HasAtMostNonemptyParts n := by
    simpa only [h.toRawPresentation_toStructure_eq] using hN
  have hRaw :=
    h.toRawPresentation.finite_boundedPartsTypedCoherentEPPA_witness n hN'
  rw [h.toRawPresentation_toStructure_eq] at hRaw
  simpa only [IsRectangleStructure.finiteRelationalCoherentCarrier] using hRaw

end SemigenericEPPA
