import SemigenericEPPA.Valuations.TwistedOldVertexExtension
import SemigenericEPPA.Valuations.PaddedPartialParameters
import SemigenericEPPA.Valuations.WitnessFiniteness
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Basic

/-!
# Finite effective EPPA via the explicit two-layer valuation witness

This is the unconditional effective EPPA construction of the
group-valued semigeneric manuscript (Theorem "Effective EPPA").

For each finite effective geometry D and finite group G, FIRST fix:
* the uniform padding B₀ on (V/E) × V;
* its finite two-layer valuation carrier;
* one affine-compatible ordered witness skeleton K, independently
  of the partial automorphism to be extended.

The embedding sends x to the complete old valuation vertex of
([x],x). It is injective, preserves/reflection E and preserves every
old effective cross-part group colour literally.

THEN for every actual injective partial E/F-isomorphism p on the
original V, use the already checked unconditional parameters
(ι,π,m) of (3.13)--(3.15), and the completed witness-coordinate
extension of (3.16)--(3.19), to obtain ONE total automorphism of
this same finite witness which extends p on the FULL valuation
vertices, preserves/reflection E, and preserves every effective
cross-part group colour.

The chosen witness is independent of p. Neither raw-fibre colours
nor coherent extension assignments are involved: these are
separate later gates and are NOT consequences of effective EPPA.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- The explicit effective EPPA witness is finite, contains the old
geometry as an induced E/F-substructure, and every partial old
isomorphism extends to a genuine automorphism of that ONE witness.

The geometry is encoded with an E setoid and group-valued F on
cross-part pairs. Inside E-classes, F is a dummy and neither the
embedding nor the automorphism requires preservation of those
irrelevant dummy values.

This is the complete semantic effective EPPA statement, with
the actual witness carrier and old inclusion exhibited. -/
theorem finite_effectiveEPPA_witness
    [Finite V] [Finite G] (D : EffectiveGeometry s V) :
    Finite (EffectiveWitnessVertex D.uniformPaddedGeometry) ∧
    ∃ K : EffectiveWitnessSkeleton D.uniformPaddedGeometry,
      K.ExtendsOldSkeleton D.uniformPaddedGeometry ∧
      Function.Injective
        (fun x : V =>
          D.uniformPaddedGeometry.oldWitnessVertex
            (D.paddedOldMap x)) ∧
      (∀ x y : V,
        K.toEffectiveGeometry.part
          (D.uniformPaddedGeometry.oldWitnessVertex (D.paddedOldMap x))
          (D.uniformPaddedGeometry.oldWitnessVertex (D.paddedOldMap y)) ↔
            D.part x y) ∧
      (∀ x y : V, ¬D.part x y →
        K.toEffectiveGeometry.F
          (D.uniformPaddedGeometry.oldWitnessVertex (D.paddedOldMap x))
          (D.uniformPaddedGeometry.oldWitnessVertex (D.paddedOldMap y)) =
            D.F x y) ∧
      (∀ (S : Set V) (p : S → V),
        Function.Injective p →
        (∀ x y : S, D.part x.val y.val ↔ D.part (p x) (p y)) →
        (∀ x y : S, ¬D.part x.val y.val →
          D.F (p x) (p y) = D.F x.val y.val) →
        ∃ T : EffectiveWitnessVertex D.uniformPaddedGeometry ≃
            EffectiveWitnessVertex D.uniformPaddedGeometry,
          (∀ x : S,
            T (D.uniformPaddedGeometry.oldWitnessVertex
                (D.paddedOldMap x.val)) =
              D.uniformPaddedGeometry.oldWitnessVertex
                (D.paddedOldMap (p x))) ∧
          (∀ X Y : EffectiveWitnessVertex D.uniformPaddedGeometry,
            K.toEffectiveGeometry.part (T X) (T Y) ↔
              K.toEffectiveGeometry.part X Y) ∧
          (∀ X Y : EffectiveWitnessVertex D.uniformPaddedGeometry,
            ¬K.toEffectiveGeometry.part X Y →
              K.toEffectiveGeometry.F (T X) (T Y) =
                K.toEffectiveGeometry.F X Y)) := by
  classical
  let B := D.uniformPaddedGeometry
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype G := Fintype.ofFinite _
  letI : Finite (Quotient D.part × V) := D.finite_uniformPaddedCarrier
  letI : Fintype (Quotient D.part × V) := Fintype.ofFinite _
  have hf : Finite (EffectiveWitnessVertex B) :=
    B.finite_effectiveWitnessVertices
  letI : Fintype (EffectiveWitnessPart B) := B.fintypeEffectiveWitnessParts
  letI : LinearOrder (EffectiveWitnessPart B) :=
    LinearOrder.lift' (Fintype.equivFin (EffectiveWitnessPart B))
      (Fintype.equivFin (EffectiveWitnessPart B)).injective
  let K : EffectiveWitnessSkeleton B := B.orderedSkeleton
  have hK : K.ExtendsOldSkeleton B := B.orderedSkeleton_extendsOld
  refine ⟨hf, K, hK, ?_, ?_, ?_, ?_⟩
  · exact B.oldWitnessVertex_injective.comp D.paddedOldMap_injective
  · intro x y
    exact
      (B.oldWitnessVertex_part_iff K (D.paddedOldMap x)
        (D.paddedOldMap y)).trans
        (D.paddedOldMap_part x y)
  · intro x y hxy
    have hxyB :
        ¬B.part (D.paddedOldMap x) (D.paddedOldMap y) := by
      intro h
      exact hxy ((D.paddedOldMap_part x y).mp h)
    exact (B.oldWitnessVertex_colour K hK
      (D.paddedOldMap x) (D.paddedOldMap y) hxyB).trans
        (D.paddedOldMap_crossColour x y hxy)
  · intro S p hp hE hF
    obtain ⟨ι, π, m, hπ, hπold, hinc, hcompat, _⟩ :=
      D.exists_paddedPartialParameters S p hp hE hF
    have hpB (x : D.paddedPartialDomain S) :
        π x.val = D.paddedPartialMap S p x := by
      calc
        π x.val = π (D.paddedOldMap x.val.2) :=
          congrArg π (D.paddedPartialDomain_eq_old S x)
        _ = D.paddedOldMap (p ⟨x.val.2, x.property.2⟩) :=
          hπold ⟨x.val.2, x.property.2⟩
        _ = D.paddedPartialMap S p x := rfl
    obtain ⟨T, htext, htpart, htcolour⟩ :=
      exists_twistedWitnessAutomorphism_extending_old
        B K hK (D.paddedPartialDomain S)
        (D.paddedPartialMap S p) ι π hπ hpB m hinc hcompat
    refine ⟨T, ?_, htpart, htcolour⟩
    intro x
    simpa [paddedPartialOld, paddedPartialMap, paddedOldMap] using
      (htext (D.paddedPartialOld S x))

end EffectiveGeometry

end SemigenericEPPA
