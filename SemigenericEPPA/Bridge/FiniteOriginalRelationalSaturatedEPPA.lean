import SemigenericEPPA.Bridge.RelationalSaturatedTypedCoherentEPPA

/-!
# Human-facing finite relational coherent EPPA without an enumeration parameter

The fully explicit factorial construction is stated using a chosen
Fintype instance on the old vertex sort. A genuine finite old
R1--R3 relational structure is more naturally given only with
Finite V, not a specified enumeration.

Choose one enumeration once, before any partial maps or groups,
run the certified saturated relational typed coherent witness,
and hide the auxiliary factorial gauge/index data in an existential
finite original-language raw witness type W.

The witness relation and embedding are not replaced by a language
expansion; W carries exactly the original E and R_c binary
relations and satisfies the same rectangle class predicate.

This is the natural user-facing positive coherent EPPA statement
for arbitrary finite original relational structures. It still
assumes the exact nonempty-and-saturated good effective set
criterion; it does not claim the DLF or SAP classifications.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {V : Type w} [Finite V]
variable {d : RawDatum G C}
variable {A : Structure (rectangleLanguage C) V}

/-- Original finite relational R1--R3 class admits coherent EPPA
under a genuine nonempty and globally congruence-saturated good
effective colour set, with no Fintype enumeration in the API.

The target W is finite and itself a literal R1--R3 relational
rectangle structure with the same binary language. -/
theorem IsRectangleStructure.finite_originalCoherentEPPA_of_saturated
    (h : IsRectangleStructure d A)
    (hGood : d.selfReverseEffective.Nonempty)
    (hSat : d.IsCongruenceSaturated) :
    ∃ (W : Type (max u (max v w)))
      (Q : RawRectanglePresentation d W),
      Finite W ∧
      ∃ psi : Structure.Embedding
          (rectangleTrivialAction C) A Q.toStructure,
        Structure.IsCoherentEPPAWitness
          (rectangleTrivialAction C) psi := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨j, Q, R, K, J, hFinite, psi, hCoherent⟩ :=
    h.finite_relationalTypedCoherentEPPA_of_saturated
      hGood hSat
  exact ⟨RawCoverVertex
      (EffectiveWitnessVertex Q.toEffectiveGeometry)
      (UniversalResidualCarrier C),
    rawCoverPresentation K.toEffectiveGeometry
      J.code J.baseline J.baseline_reverse,
    hFinite, psi, hCoherent⟩

end SemigenericEPPA
