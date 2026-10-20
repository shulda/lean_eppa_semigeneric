import SemigenericEPPA.Structure.RelationalRoundtripEquality
import SemigenericEPPA.Bridge.GOneTypedCoherentEPPA

/-!
# Coherent EPPA for every finite original relational rectangle member when G=1

The previous finite_typedCoherentEPPA_witness theorem is formulated
using the convenient functional RawRectanglePresentation data. The
real mathematical class K(G,s,phi), however, consists of arbitrary
relational structures A in the ORIGINAL binary language R1--R3.

For every such A the already formalized relational-to-functional
roundtrip supplies P=h.toRawPresentation, and the exact equality
P.toStructure = A is separately certified. Thus the strong typed
coherent-EPPA witness statement transports along literal equality
of structures, requiring no new witness or groupoid assignment.

This is the human-facing positive coherent EPPA theorem for the
trivial effective group, in the original relational language.
Its hypotheses are only finite G and C, G subsingleton, finite
vertex set V, and the EXACT relational R1--R3 class predicate.
No assumptions about raw functional data are added.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {V : Type w}
variable {d : RawDatum G C}
variable {A : Structure (rectangleLanguage C) V}

/-- Fix one canonical finite enumeration of the old relational
carrier before forming the factorial-size witness. This choice
is made from `Finite V`, and does not depend on any later
partial map, group action or induced substructure. -/
noncomputable abbrev IsRectangleStructure.finiteRelationalCoherentCarrier
    [Finite V] (h : IsRectangleStructure d A) :=
  letI : Fintype V := Fintype.ofFinite V
  GOneJointRawCarrier h.toRawPresentation

/-- Every finite relational member of the exact generalized
semigeneric class with trivial effective group has one finite
coherent EPPA witness in the ORIGINAL R1--R3 binary language.
Only `Finite V` is required: the factorial-size enumeration is
selected once by `finiteRelationalCoherentCarrier`. -/
theorem IsRectangleStructure.finite_relationalTypedCoherentEPPA_witness
    [Finite V] (h : IsRectangleStructure d A) :
    Finite (h.finiteRelationalCoherentCarrier) ∧
    ∃ (Q : RawRectanglePresentation d
          (h.finiteRelationalCoherentCarrier))
      (ψ : Structure.Embedding
        (rectangleTrivialAction C) A Q.toStructure),
      Structure.IsCoherentEPPAWitness
        (rectangleTrivialAction C) ψ := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hTyped :=
    h.toRawPresentation.finite_typedCoherentEPPA_witness
  simpa only [IsRectangleStructure.finiteRelationalCoherentCarrier,
    h.toRawPresentation_toStructure_eq] using hTyped

end SemigenericEPPA
