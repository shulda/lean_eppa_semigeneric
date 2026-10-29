import SemigenericEPPA.Valuations.GOneActualRawAutSubgroupLifts
import SemigenericEPPA.Structure.PartQuotient

/-!
# The G=1 coherent witness has no new E-parts

The existing G=1 coherent construction is a raw residual cover over
  (A/E) × Fin (coherentPaddingSize A).
The induced E-equivalence on the raw cover is exactly equality of
the first base coordinate. Hence every witness vertex lies in the
E-class of an old zero-section vertex.

This statement is independent of any choice of a partial
automorphism or of a later coherence assignment.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Every vertex of the fixed raw cover belongs to an E-class
containing an old vertex. This includes the empty A case: the
cover is then empty, since its effective base has no E-classes. -/
theorem gOneJointRawPart_coveredByOld
    (P : RawRectanglePresentation d A)
    (j : A → Fin (coherentPaddingSize A))
    (K : FixedJointRawCover.{u, v, w, w, t}
      P P.gOneFactorialGeometry (P.gOneFactorialOldMap j)) :
    ∀ z : GOneJointRawCarrier P, ∃ x : A,
      (P.gOneJointRawPresentation j K).part
        (P.gOneJointRawOldMap j x) z := by
  intro z
  obtain ⟨x, hx⟩ := Quotient.exists_rep z.1.1
  refine ⟨x, ?_⟩
  change P.gOneFactorialGeometry.part
    (P.gOneFactorialOldMap j x) z.1
  change Quotient.mk P.effectiveReduct.part x = z.1.1
  exact hx

end RawRectanglePresentation
end SemigenericEPPA
