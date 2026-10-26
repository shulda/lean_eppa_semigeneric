import SemigenericEPPA.Bridge.RawTypedEPPA
import SemigenericEPPA.Structure.RelationalRoundtripEquality

/-!
# Typed EPPA for an arbitrary original relational rectangle

The raw presentation bridge is exact equality of the original E/R_c
structure.  We therefore export an immediately usable typed EPPA
statement with the ORIGINAL relational A as the source, rather than
requiring clients to rewrite A by hand first.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}
variable {A : Structure (rectangleLanguage C) V}

/-- Every finite original E/R_c rectangle has an actual finite typed
EPPA witness extending every typed partial automorphism, with its
specified induced embedding into one common witness. -/
theorem IsRectangleStructure.finite_relationalTypedEPPA_witness
    [Finite G] [Finite C] [Finite V]
    (h : IsRectangleStructure d A) :
    Finite (RawEPPAWitnessCarrier h.toRawPresentation) ∧
    ∃ (R : RawRectanglePresentation d
        (RawEPPAWitnessCarrier h.toRawPresentation))
      (ψ : Structure.Embedding
        (rectangleTrivialAction C) A R.toStructure),
      Structure.IsEPPAWitness (rectangleTrivialAction C) ψ := by
  obtain ⟨hFinite, R, ψ, hEPPA⟩ :=
    h.toRawPresentation.finite_typedEPPA_witness
  refine ⟨hFinite, R, ?_⟩
  rw [← h.toRawPresentation_toStructure_eq]
  exact ⟨ψ, hEPPA⟩

end SemigenericEPPA
