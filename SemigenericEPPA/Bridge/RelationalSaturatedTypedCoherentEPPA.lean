import SemigenericEPPA.Bridge.NontrivialSaturatedTypedCoherentEPPA
import SemigenericEPPA.Structure.RelationalRoundtripEquality

/-!
# Coherent EPPA for arbitrary finite ORIGINAL relational R1--R3 members

The saturated positive coherent theorem is first stated for the
convenient functional raw rectangle presentation. The manuscript's
actual structures use the original finite binary relational
language with one distinguished E predicate and raw R_c predicates.

The certified relational-to-functional roundtrip recovers P from
any genuine IsRectangleStructure d A and proves P.toStructure=A
literally. Transporting the full fixed finite coherent witness along
this equality does not change the witness, old embedding, coherent
functor, or any underlying raw colour.

This is the original-language positive coherent classification
branch for arbitrary finite nonabelian effective G and general
affine reversal s, under the exact mathematical good-set
nonemptiness and congruence-saturation criterion. Neither DLF
nor the final iff statement is claimed in this file.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {V : Type w} [Fintype V]
variable {d : RawDatum G C}
variable {A : Structure (rectangleLanguage C) V}

/-- Every finite original relational R1--R3 member with a
nonempty globally congruence-saturated good effective colour set
has a FINITE coherent EPPA witness in exactly its original language,
using one fixed factorial/valuation/raw cover. -/
theorem IsRectangleStructure.finite_relationalTypedCoherentEPPA_of_saturated
    (h : IsRectangleStructure d A)
    (hGood : d.selfReverseEffective.Nonempty)
    (hsat : d.IsCongruenceSaturated) :
    let Praw : RawRectanglePresentation d V := h.toRawPresentation
    ∃ (j : V → Fin (coherentPaddingSize V))
      (Q : IndexedGauge d.s
        (Quotient Praw.effectiveReduct.part × Fin (coherentPaddingSize V))
        (Quotient Praw.effectiveReduct.part))
      (R : IndexedGauge d.s
        (Quotient Praw.effectiveReduct.part × Fin (coherentPaddingSize V))
        (Quotient Q.toEffectiveGeometry.part))
      (K : EffectiveWitnessSkeleton Q.toEffectiveGeometry),
      let D : EffectiveGeometry d.s V := Praw.effectiveReduct
      let B := Q.toEffectiveGeometry
      let old : V → Quotient D.part × Fin (coherentPaddingSize V) :=
        D.factorialAuxiliaryOldMap j
      let psi : V → EffectiveWitnessVertex B :=
        fun a => B.gaugeOldWitnessVertex R.vertexGauge (old a)
      ∃ J : FixedJointRawCover.{u, v, w, max u w, w}
          Praw K.toEffectiveGeometry psi,
        Finite (RawCoverVertex
          (EffectiveWitnessVertex B) (UniversalResidualCarrier C)) ∧
        ∃ e : Structure.Embedding
          (rectangleTrivialAction C) A
          (rawCoverPresentation K.toEffectiveGeometry
            J.code J.baseline J.baseline_reverse).toStructure,
          Structure.IsCoherentEPPAWitness (rectangleTrivialAction C) e := by
  classical
  have hTyped :=
    h.toRawPresentation.finite_typedCoherentEPPA_witness_of_saturated
      hGood hsat
  rw [h.toRawPresentation_toStructure_eq] at hTyped
  exact hTyped

end SemigenericEPPA
