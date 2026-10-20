import SemigenericEPPA.Structure.QuotientGaugeConverse

/-!
# Canonical diagonal gauge normalization in genuine rectangle members

Cross-E rectangle laws leave same-part dummy F-values unrestricted.
Nevertheless the ACTUAL binary relational class is converted to
effective geometries with F(x,y)=1 on each E-part. The canonical
quotient gauge then has its *diagonal vertex-to-part coordinate* equal
to 1 for every original vertex x.

Consequently, whenever a group action sends old classes compatibly
with its old vertices, diagonal quotient-gauge coordinates are
automatically equivariant, independently of the action's behaviour
on the non-diagonal gauges. This is the precise missing diagonal
condition in the indexed old-vertex transport argument.

The result is not true for an arbitrary EffectiveGeometry whose
same-part dummy F-values were chosen without normalization.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {H : Type t} [Group H]
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- If same-part dummy values are normalized to 1, then the old
canonical quotient-gauge coordinate at its OWN index equals 1.
This explicitly uses the same-part normalization, not R3. -/
theorem quotientGauge_diagonal_one
    (D : EffectiveGeometry s V)
    (hSame : ∀ x y : V, D.part x y → D.F x y = 1)
    (x : V) :
    D.toQuotientGauge.vertexGauge x (Quotient.mk D.part x) = 1 := by
  change D.F (D.representative (Quotient.mk D.part x)) x = 1
  exact hSame _ _ (D.part.iseqv.symm (D.related_representative x))

/-- A compatible old-label / quotient-index group action therefore
preserves the diagonal quotient-gauge coordinate literally. No
restriction on its off-diagonal action is needed for this equation. -/
theorem quotientGauge_diagonal_H_invariant
    (D : EffectiveGeometry s V)
    (hSame : ∀ x y : V, D.part x y → D.F x y = 1)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (h : H) (x : V) :
    D.toQuotientGauge.vertexGauge (rho h x)
        (iota h (Quotient.mk D.part x)) =
      D.toQuotientGauge.vertexGauge x (Quotient.mk D.part x) := by
  rw [← hcls h x,
    D.quotientGauge_diagonal_one hSame (rho h x),
    D.quotientGauge_diagonal_one hSame x]

end EffectiveGeometry

/-- Every genuine original R1--R3 member has the normalized
same-part quotient gauges needed by the H-action extension proof.
No extra normalization assumption is imposed on the raw class. -/
theorem IsRectangleStructure.effective_diagonal_gauge_one
    {d : RawDatum G C}
    {A : AllThoseEPPA.Structure (rectangleLanguage C) V}
    (h : IsRectangleStructure d A) (x : V) :
    h.toEffectiveGeometry.toQuotientGauge.vertexGauge x
        (Quotient.mk h.toEffectiveGeometry.part x) = 1 := by
  apply EffectiveGeometry.quotientGauge_diagonal_one
  intro a b hab
  exact h.effectiveTotal_same a b hab

end SemigenericEPPA
